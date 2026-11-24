import UnforcedLeray.Loc.L05EssentialRadius.Kernel
import UnforcedLeray.Analysis.LerayProjection.TranslationGenerator
import UnforcedLeray.Analysis.LerayProjection.TranslationH1
import UnforcedLeray.Analysis.Heat.ConvolutionOrbit
import UnforcedLeray.Analysis.Heat.Derivatives

/-!
# L5: multiplication by a `C₀` field is compact `H¹(ℝ³) → L²(ℝ³)`

`paper/main.tex` line 332 (blueprint B0714 (a)): "Multiplication by `U_* ∈ C_0` is compact
`X → L²`, by Rellich compactness on balls and a small uniform tail." This file proves
`C0MulCompact` (`Kernel.lean`). The local compactness on balls is obtained by heat smoothing
instead of a Rellich–Kondrachov theorem:

* `norm_translation_sub_le`: `‖f(·+a) - f‖₂ ≤ 3|a| ‖f‖_{H¹}`, from the translation generator
  (`Leray.translation_eq_add_integral_weakDerivative`) in each coordinate direction;
* `norm_sub_heat_le`: `‖f - e^{tΔ}f‖₂ ≤ 3·√(8t)·2^{3/2} ‖f‖_{H¹}` (Minkowski in the Gaussian
  translation-orbit integral and the first Gaussian moment `Gaussian.norm_kernel_le_sqrt`);
* `inner_average_eq`, `norm_average_le`: the heat average at a point is the `L²` pairing with
  the probe `z ↦ k_t(x-z)w`; hence it is bounded by `‖k_t‖₂ ‖f‖₂` and tends to `0` pointwise
  along a weakly null sequence;
* `c0MulCompact`: for `fₙ ⇀ 0` in `H¹` and `U ∈ C₀`,
  `|U|²|fₙ|² ≤ 2‖U‖²_∞|fₙ - e^{tΔ}fₙ|² + 2‖U‖²_∞ 1_{B_R}|e^{tΔ}fₙ|² + 2η²|e^{tΔ}fₙ|²`
  with `|U| ≤ η` off `B_R` (small uniform tail), and dominated convergence on `B_R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace UnforcedLeray.Loc.L05

open UnforcedLeray.Blueprint UnforcedLeray.Infra.WeaklyNullCompact SobolevGraph

/-! ## Coordinates of `ℝ³` -/

theorem space_eq_sum (a : Space) :
    ∑ k, ⟪coordinateVector k, a⟫_ℝ • coordinateVector k = a := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' a
  simp only [EuclideanSpace.basisFun_apply] at this
  exact this

theorem abs_inner_coordinate_le (k : Fin 3) (a : Space) : |⟪coordinateVector k, a⟫_ℝ| ≤ ‖a‖ := by
  have := abs_real_inner_le_norm (coordinateVector k) a
  rwa [norm_coordinateVector, one_mul] at this

theorem norm_le_sum_abs_inner (a : Space) : ‖a‖ ≤ ∑ k, |⟪coordinateVector k, a⟫_ℝ| := by
  conv_lhs => rw [← space_eq_sum a]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_smul, norm_coordinateVector, mul_one, Real.norm_eq_abs]

theorem norm_value_le (F : H1) : ‖F.value‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : H1Ambient) 0

/-! ## Translation and heat approximation in `H¹` -/

/-- `‖f(· + t eᵢ) - f‖₂ ≤ |t| ‖f‖_{H¹}`. -/
theorem norm_translation_coord_sub_le (F : H1) (i : Fin 3) (t : ℝ) :
    ‖Leray.translation (t • coordinateVector i) F.value - F.value‖ ≤ |t| * ‖F‖ := by
  rw [Leray.translation_eq_add_integral_weakDerivative F.value (F.derivative i) i
    (F.hasWeakDerivative i) t, add_sub_cancel_left]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖F‖) fun s _ => ?_).trans ?_
  · rw [Leray.norm_translation]
    exact SobolevEmbedding.h1_derivative_norm_le F i
  · rw [sub_zero, mul_comm]

/-- `‖f(· + a) - f‖₂ ≤ 3|a| ‖f‖_{H¹}`. -/
theorem norm_translation_sub_le (F : H1) (a : Space) :
    ‖Leray.translation a F.value - F.value‖ ≤ 3 * ‖a‖ * ‖F‖ := by
  set c : Fin 3 → ℝ := fun k => ⟪coordinateVector k, a⟫_ℝ with hc
  have ha : c 0 • coordinateVector 0 + c 1 • coordinateVector 1 + c 2 • coordinateVector 2 =
      a := by
    conv_rhs => rw [← space_eq_sum a]
    rw [Fin.sum_univ_three]
  obtain ⟨W2, hW2⟩ : ∃ W : H1, W = Leray.h1Translate (c 2 • coordinateVector 2) F := ⟨_, rfl⟩
  obtain ⟨W1, hW1⟩ : ∃ W : H1, W = Leray.h1Translate (c 1 • coordinateVector 1) W2 := ⟨_, rfl⟩
  have hv2 : W2.value = Leray.translation (c 2 • coordinateVector 2) F.value := by
    rw [hW2, Leray.value_h1Translate]
  have hv1 : W1.value = Leray.translation (c 1 • coordinateVector 1) W2.value := by
    rw [hW1, Leray.value_h1Translate]
  have hn2 : ‖W2‖ = ‖F‖ := by rw [hW2, Leray.norm_h1Translate]
  have hn1 : ‖W1‖ = ‖F‖ := by rw [hW1, Leray.norm_h1Translate, hn2]
  have hval : Leray.translation a F.value =
      Leray.translation (c 0 • coordinateVector 0) W1.value := by
    rw [hv1, hv2, Leray.translation_add, Leray.translation_add, ha]
  have key : Leray.translation a F.value - F.value =
      (Leray.translation (c 0 • coordinateVector 0) W1.value - W1.value) +
      (Leray.translation (c 1 • coordinateVector 1) W2.value - W2.value) +
      (Leray.translation (c 2 • coordinateVector 2) F.value - F.value) := by
    rw [hval, ← hv1, ← hv2]
    abel
  rw [key]
  have h0 := norm_translation_coord_sub_le W1 0 (c 0)
  have h1 := norm_translation_coord_sub_le W2 1 (c 1)
  have h2 := norm_translation_coord_sub_le F 2 (c 2)
  rw [hn1] at h0
  rw [hn2] at h1
  have hc0 : |c 0| ≤ ‖a‖ := abs_inner_coordinate_le 0 a
  have hc1 : |c 1| ≤ ‖a‖ := abs_inner_coordinate_le 1 a
  have hc2 : |c 2| ≤ ‖a‖ := abs_inner_coordinate_le 2 a
  have hF := norm_nonneg F
  calc ‖(Leray.translation (c 0 • coordinateVector 0) W1.value - W1.value) +
        (Leray.translation (c 1 • coordinateVector 1) W2.value - W2.value) +
        (Leray.translation (c 2 • coordinateVector 2) F.value - F.value)‖
      ≤ |c 0| * ‖F‖ + |c 1| * ‖F‖ + |c 2| * ‖F‖ :=
        (norm_add₃_le).trans (add_le_add (add_le_add h0 h1) h2)
    _ ≤ ‖a‖ * ‖F‖ + ‖a‖ * ‖F‖ + ‖a‖ * ‖F‖ := by gcongr
    _ = 3 * ‖a‖ * ‖F‖ := by ring

theorem heat_translation_eq (y : Space) (v : L2Space) :
    Heat.translation y v = Leray.translation (-y) v := by
  apply Lp.ext
  filter_upwards [Heat.translation_ae y v, Leray.coeFn_translation (-y) v] with x h1 h2
  rw [h1, h2, sub_eq_add_neg]

/-- **Heat approximation in `H¹`**: `‖f - e^{tΔ}f‖₂ ≤ 3√(8t)·2^{3/2} ‖f‖_{H¹}`. -/
theorem norm_sub_heat_le (F : H1) {t : ℝ} (ht : 0 < t) :
    ‖F.value - Heat.heatOperator t F.value‖ ≤
      3 * Real.sqrt (8 * t) * (2 : ℝ) ^ ((3 : ℝ) / 2) * ‖F‖ := by
  have hk := Heat.kernel_integrable ht
  have horb := Heat.convolutionOrbit_integrable (Heat.kernel t) hk F.value
  have h1 : Heat.heatOperator t F.value =
      ∫ y, Heat.kernel t y • Heat.translation y F.value := by
    rw [Heat.heatOperator_pos ht, Heat.convolutionOperator_eq_integral_translationOrbit]
  have h2 : ∫ y, Heat.kernel t y • F.value = F.value := by
    rw [integral_smul_const, Heat.integral_kernel ht, one_smul]
  have h3 : F.value - Heat.heatOperator t F.value =
      ∫ y, Heat.kernel t y • (F.value - Heat.translation y F.value) := by
    simp_rw [smul_sub]
    rw [integral_sub (hk.smul_const F.value) horb, h2, h1]
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have hbound : ∀ y, ‖Heat.kernel t y • (F.value - Heat.translation y F.value)‖ ≤
      (3 * ‖F‖ * Real.sqrt (8 * t)) * Heat.Gaussian.wideKernel (4 * t) y := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (Heat.kernel_nonneg ht y), heat_translation_eq,
      norm_sub_rev]
    have htr := norm_translation_sub_le F (-y)
    rw [norm_neg] at htr
    have hks := Heat.Gaussian.norm_kernel_le_sqrt h4t y
    rw [show (2 : ℝ) * (4 * t) = 8 * t by ring] at hks
    have hkt : Heat.kernel t y = Heat.Gaussian.kernel (4 * t) y := rfl
    calc Heat.kernel t y * ‖Leray.translation (-y) F.value - F.value‖
        ≤ Heat.kernel t y * (3 * ‖y‖ * ‖F‖) :=
          mul_le_mul_of_nonneg_left htr (Heat.kernel_nonneg ht y)
      _ = 3 * ‖F‖ * (‖y‖ * Heat.Gaussian.kernel (4 * t) y) := by rw [hkt]; ring
      _ ≤ 3 * ‖F‖ * (Real.sqrt (8 * t) * Heat.Gaussian.wideKernel (4 * t) y) :=
          mul_le_mul_of_nonneg_left hks (by positivity)
      _ = _ := by ring
  rw [h3]
  refine (norm_integral_le_of_norm_le
    ((Heat.Gaussian.wideKernel_integrable h4t).const_mul _)
    (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_const_mul, Heat.Gaussian.integral_wideKernel h4t]
  ring

/-! ## The heat average at a point -/

/-- The probe `z ↦ k_t(x - z) w`. -/
def kernelProbe (t : ℝ) (x w : Space) : SpatialField := fun z => Heat.kernel t (x - z) • w

theorem kernelProbe_memLp {t : ℝ} (ht : 0 < t) (x w : Space) :
    MemLp (kernelProbe t x w) 2 volume := by
  have hk : MemLp (fun z => Heat.kernel t (x - z)) 2 volume :=
    (Heat.kernel_memLp_two ht).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume x)
  have hc : Continuous (kernelProbe t x w) := by
    unfold kernelProbe
    exact ((Heat.Gaussian.kernel_smooth (4 * t)).continuous.comp
      (continuous_const.sub continuous_id)).smul continuous_const
  refine (hk.norm.const_mul ‖w‖).of_le hc.aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  simp only [kernelProbe, norm_smul, Real.norm_eq_abs, abs_mul, abs_norm, abs_abs]
  rw [mul_comm]

theorem norm_kernelProbe_le {t : ℝ} (ht : 0 < t) (x w : Space) :
    ‖toL2 (kernelProbe t x w)‖ ≤ ‖w‖ * Real.sqrt (∫ z, Heat.kernel t z ^ 2) := by
  have hsq := norm_toL2_sq (kernelProbe_memLp ht x w)
  have hint : ∫ z, ‖kernelProbe t x w z‖ ^ 2 = ‖w‖ ^ 2 * ∫ z, Heat.kernel t z ^ 2 := by
    simp only [kernelProbe, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_mul_const, mul_comm]
    congr 1
    exact integral_sub_left_eq_self (fun z => Heat.kernel t z ^ 2) volume x
  rw [hint] at hsq
  have h0 : 0 ≤ ∫ z, Heat.kernel t z ^ 2 := integral_nonneg fun z => sq_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg (toL2 (kernelProbe t x w))), hsq,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The heat average at `x`, tested against `w`, is the `L²` pairing with the probe. -/
theorem inner_average_eq {t : ℝ} (ht : 0 < t) (v : L2Space) (x w : Space) :
    ⟪w, Heat.average t (v : SpatialField) x⟫_ℝ = ⟪toL2 (kernelProbe t x w), v⟫_ℝ := by
  rw [L2.inner_def]
  have hrep := coeFn_toL2 (kernelProbe_memLp ht x w)
  have h1 : (∫ z, ⟪(toL2 (kernelProbe t x w) : SpatialField) z, (v : SpatialField) z⟫_ℝ) =
      ∫ z, Heat.kernel t (x - z) * ⟪w, (v : SpatialField) z⟫_ℝ := by
    refine integral_congr_ae (hrep.mono fun z hz => ?_)
    simp only [hz, kernelProbe, real_inner_smul_left]
  have h2 : ⟪w, Heat.average t (v : SpatialField) x⟫_ℝ =
      ∫ y, Heat.kernel t y * ⟪w, (v : SpatialField) (x - y)⟫_ℝ := by
    rw [Heat.average, ← integral_inner (Heat.average_integrable ht (Lp.memLp v) x)]
    simp only [real_inner_smul_right]
  have h3 : (∫ z, Heat.kernel t (x - z) * ⟪w, (v : SpatialField) z⟫_ℝ) =
      ∫ y, Heat.kernel t y * ⟪w, (v : SpatialField) (x - y)⟫_ℝ := by
    have := integral_sub_left_eq_self
      (fun y => Heat.kernel t y * ⟪w, (v : SpatialField) (x - y)⟫_ℝ) volume x
    simp only [sub_sub_cancel] at this
    exact this
  rw [h1, h2, h3]

/-- `‖e^{tΔ}v(x)‖ ≤ ‖k_t‖₂ ‖v‖₂` at every point. -/
theorem norm_average_le {t : ℝ} (ht : 0 < t) (v : L2Space) (x : Space) :
    ‖Heat.average t (v : SpatialField) x‖ ≤ Real.sqrt (∫ z, Heat.kernel t z ^ 2) * ‖v‖ := by
  set a := Heat.average t (v : SpatialField) x
  have h := inner_average_eq ht v x a
  rw [real_inner_self_eq_norm_sq] at h
  have hle : ‖a‖ ^ 2 ≤ ‖a‖ * (Real.sqrt (∫ z, Heat.kernel t z ^ 2) * ‖v‖) := by
    rw [h]
    refine (real_inner_le_norm _ _).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_kernelProbe_le ht x a) (norm_nonneg _)
  have ha := norm_nonneg a
  have hb : 0 ≤ Real.sqrt (∫ z, Heat.kernel t z ^ 2) * ‖v‖ := by positivity
  by_contra hlt
  have hlt' := not_le.mp hlt
  nlinarith

/-- Along a weakly null sequence the heat averages tend to `0` at every point. -/
theorem tendsto_average_of_weaklyNull {t : ℝ} (ht : 0 < t) {v : ℕ → L2Space}
    (hv : ∀ ψ : L2Space, Tendsto (fun n => ⟪ψ, v n⟫_ℝ) atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => Heat.average t (v n : SpatialField) x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hk : ∀ k : Fin 3, Tendsto (fun n => |⟪coordinateVector k,
      Heat.average t (v n : SpatialField) x⟫_ℝ|) atTop (𝓝 0) := by
    intro k
    simp only [inner_average_eq ht]
    simpa using (hv (toL2 (kernelProbe t x (coordinateVector k)))).abs
  have hs : Tendsto (fun n => ∑ k, |⟪coordinateVector k,
      Heat.average t (v n : SpatialField) x⟫_ℝ|) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun k _ => hk k
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_le_sum_abs_inner _) hs

/-! ## Compactness of multiplication by a `C₀` field -/

/-- A small uniform tail: `|U| ≤ η` outside a ball. -/
theorem exists_tail (U : ZeroAtInftyContinuousMap Space Space) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ y : Space, y ∉ Metric.closedBall (0 : Space) R → ‖U y‖ ≤ η := by
  obtain ⟨K, hK, hKU⟩ := (hasBasis_cocompact.tendsto_iff Metric.nhds_basis_closedBall).mp
    U.zero_at_infty' η hη
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun y hy => ?_⟩
  have hyK : y ∉ K := fun h => hy (hR h)
  have := hKU y hyK
  rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- The pointwise splitting inequality. -/
theorem pointwise_split {u w h : ℝ} {B η ι : ℝ} (hu : 0 ≤ u) (hB : u ≤ B) (hη : u ≤ η ∨ ι = 1)
    (hι : 0 ≤ ι) (hw : 0 ≤ w) (hh : 0 ≤ h) (hη0 : 0 ≤ η) {d : ℝ} (hd : 0 ≤ d) (hwd : w ≤ d + h) :
    u ^ 2 * w ^ 2 ≤ 2 * B ^ 2 * d ^ 2 + 2 * B ^ 2 * (ι * h ^ 2) + 2 * η ^ 2 * h ^ 2 := by
  have hw2 : w ^ 2 ≤ 2 * d ^ 2 + 2 * h ^ 2 := by
    have : w ^ 2 ≤ (d + h) ^ 2 := pow_le_pow_left₀ hw hwd 2
    nlinarith [sq_nonneg (d - h)]
  have hu2 : u ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hu hB 2
  have hu2' : u ^ 2 ≤ B ^ 2 * ι + η ^ 2 := by
    rcases hη with h1 | h1
    · have : u ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hu h1 2
      nlinarith [sq_nonneg B]
    · rw [h1]; nlinarith [sq_nonneg η]
  calc u ^ 2 * w ^ 2 ≤ u ^ 2 * (2 * d ^ 2 + 2 * h ^ 2) :=
        mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
    _ = 2 * u ^ 2 * d ^ 2 + 2 * u ^ 2 * h ^ 2 := by ring
    _ ≤ 2 * B ^ 2 * d ^ 2 + 2 * (B ^ 2 * ι + η ^ 2) * h ^ 2 := by
        gcongr
    _ = _ := by ring

/-- Three elementary inequalities used to choose `t`, `R` and `n` in `c0MulCompact`. -/
theorem arith_heat_term {B A M t δ X : ℝ} (hX : X ≤ A ^ 2 * t * M ^ 2) (ht : 0 < t)
    (htK : t * (8 * (B ^ 2 * A ^ 2 * M ^ 2 + 1)) = δ) : 2 * B ^ 2 * X ≤ δ / 4 := by
  have h1 : 2 * B ^ 2 * X ≤ 2 * B ^ 2 * (A ^ 2 * t * M ^ 2) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  linarith

theorem arith_ball_term {B I s δ : ℝ} (hI : I < s) (hs : 0 < s)
    (hs8 : s * (8 * (B ^ 2 + 1)) = δ) : 2 * B ^ 2 * I < δ / 4 := by
  have h1 : B ^ 2 * I ≤ B ^ 2 * s := mul_le_mul_of_nonneg_left hI.le (sq_nonneg _)
  linarith

theorem arith_tail_term {s X M δ : ℝ} (hX : X ≤ M ^ 2) (hs : 0 < s)
    (hs8 : s * (8 * (M ^ 2 + 1)) = δ) : 2 * s * X ≤ δ / 4 := by
  have h1 : s * X ≤ s * M ^ 2 := mul_le_mul_of_nonneg_left hX hs.le
  linarith

/-- The splitting estimate for one field: with `|U| ≤ η` off `B_R`, for all `v, G ∈ L²`,
`∫|U|²|v|² ≤ 2‖U‖²_∞‖v - G‖² + 2‖U‖²_∞ ∫_{B_R}|G|² + 2η²‖G‖²`. -/
theorem integral_mul_le_split (U : ZeroAtInftyContinuousMap Space Space) (v G : L2Space)
    {η R : ℝ} (hη : 0 ≤ η)
    (hR : ∀ y : Space, y ∉ Metric.closedBall (0 : Space) R → ‖U y‖ ≤ η) :
    ∫ y, ‖U y‖ ^ 2 * ‖(v : SpatialField) y‖ ^ 2 ≤
      2 * ‖U‖ ^ 2 * ‖v - G‖ ^ 2 +
      2 * ‖U‖ ^ 2 * (∫ y, (Metric.closedBall (0 : Space) R).indicator
        (fun y => ‖(G : SpatialField) y‖ ^ 2) y) +
      2 * η ^ 2 * ‖G‖ ^ 2 := by
  set ball := Metric.closedBall (0 : Space) R with hball
  have hball_meas : MeasurableSet ball := measurableSet_closedBall
  have hD2 : Integrable (fun y => ‖((v - G : L2Space) : SpatialField) y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hG2 : Integrable (fun y => ‖(G : SpatialField) y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hGI : Integrable (fun y => ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y)
      volume := hG2.indicator hball_meas
  have hpt : (fun y => ‖U y‖ ^ 2 * ‖(v : SpatialField) y‖ ^ 2) ≤ᵐ[volume]
      fun y => 2 * ‖U‖ ^ 2 * ‖((v - G : L2Space) : SpatialField) y‖ ^ 2 +
        2 * ‖U‖ ^ 2 * ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y +
        2 * η ^ 2 * ‖(G : SpatialField) y‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub v G] with y hy
    have hsplit : ‖(v : SpatialField) y‖ ≤
        ‖((v - G : L2Space) : SpatialField) y‖ + ‖(G : SpatialField) y‖ := by
      have : (v : SpatialField) y =
          ((v - G : L2Space) : SpatialField) y + (G : SpatialField) y := by
        rw [hy, Pi.sub_apply, sub_add_cancel]
      rw [this]
      exact norm_add_le _ _
    have hind : ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y =
        ball.indicator (fun _ => (1 : ℝ)) y * ‖(G : SpatialField) y‖ ^ 2 := by
      by_cases hyb : y ∈ ball
      · rw [indicator_of_mem hyb, indicator_of_mem hyb, one_mul]
      · rw [indicator_of_notMem hyb, indicator_of_notMem hyb, zero_mul]
    rw [hind]
    have hcase : ‖U y‖ ≤ η ∨ ball.indicator (fun _ => (1 : ℝ)) y = 1 := by
      by_cases hyb : y ∈ ball
      · right; rw [indicator_of_mem hyb]
      · left; exact hR y hyb
    have hι : 0 ≤ ball.indicator (fun _ => (1 : ℝ)) y :=
      indicator_nonneg (fun _ _ => zero_le_one) y
    have := pointwise_split (norm_nonneg (U y)) (norm_C0_apply_le U y) hcase hι
      (norm_nonneg _) (norm_nonneg _) hη (norm_nonneg _) hsplit
    linarith
  have i1 : Integrable (fun y => 2 * ‖U‖ ^ 2 * ‖((v - G : L2Space) : SpatialField) y‖ ^ 2)
      volume := hD2.const_mul _
  have i2 : Integrable
      (fun y => 2 * ‖U‖ ^ 2 * ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y) volume :=
    hGI.const_mul _
  have i3 : Integrable (fun y => 2 * η ^ 2 * ‖(G : SpatialField) y‖ ^ 2) volume :=
    hG2.const_mul _
  have i12 : Integrable (fun y => 2 * ‖U‖ ^ 2 * ‖((v - G : L2Space) : SpatialField) y‖ ^ 2 +
      2 * ‖U‖ ^ 2 * ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y) volume :=
    i1.add i2
  have i123 : Integrable (fun y => 2 * ‖U‖ ^ 2 * ‖((v - G : L2Space) : SpatialField) y‖ ^ 2 +
      2 * ‖U‖ ^ 2 * ball.indicator (fun y => ‖(G : SpatialField) y‖ ^ 2) y +
      2 * η ^ 2 * ‖(G : SpatialField) y‖ ^ 2) volume :=
    i12.add i3
  have eD : ∫ y, ‖((v - G : L2Space) : SpatialField) y‖ ^ 2 = ‖v - G‖ ^ 2 :=
    (norm_sq_eq_integral (v - G)).symm
  have eG : ∫ y, ‖(G : SpatialField) y‖ ^ 2 = ‖G‖ ^ 2 := (norm_sq_eq_integral G).symm
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) i123 hpt).trans
    (le_of_eq ?_)
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, eD, eG]

/-- The local term: along a weakly null bounded sequence, `∫_{B_R}|e^{tΔ}fₙ|² → 0` (dominated
convergence with the pointwise bound `‖k_t‖₂ M`). -/
theorem tendsto_ball_heat {t : ℝ} (ht : 0 < t) {f : ℕ → H1} {M : ℝ} (hM : ∀ n, ‖f n‖ ≤ M)
    (hv : ∀ ψ : L2Space, Tendsto (fun n => ⟪ψ, (f n).value⟫_ℝ) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun n => ∫ y, (Metric.closedBall (0 : Space) R).indicator
      (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) y) atTop (𝓝 0) := by
  set ball := Metric.closedBall (0 : Space) R with hball
  have hball_meas : MeasurableSet ball := measurableSet_closedBall
  have hrep : ∀ᵐ y ∂volume, ∀ n, (Heat.heatOperator t (f n).value : SpatialField) y =
      Heat.average t ((f n).value : SpatialField) y :=
    ae_all_iff.mpr fun n => Heat.heatOperator_rep ht (f n).value
  have hmeas : ∀ n, AEStronglyMeasurable (fun y => ball.indicator
      (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) y) volume := by
    intro n
    have h0 : AEStronglyMeasurable
        (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) volume :=
      (Lp.aestronglyMeasurable _).norm.pow 2
    exact h0.indicator hball_meas
  have hbound : ∀ n, ∀ᵐ y ∂volume, ‖ball.indicator
      (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) y‖ ≤
      ball.indicator (fun _ => (Real.sqrt (∫ z, Heat.kernel t z ^ 2) * M) ^ 2) y := by
    intro n
    filter_upwards [hrep] with y hy
    by_cases hyb : y ∈ ball
    · simp only [indicator_of_mem hyb]
      rw [Real.norm_of_nonneg (sq_nonneg _), hy n]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_average_le ht _ y).trans ?_
      exact mul_le_mul_of_nonneg_left ((norm_value_le _).trans (hM n)) (Real.sqrt_nonneg _)
    · simp only [indicator_of_notMem hyb, norm_zero, le_refl]
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n => ball.indicator
      (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) y) atTop (𝓝 0) := by
    filter_upwards [hrep] with y hy
    by_cases hyb : y ∈ ball
    · simp only [indicator_of_mem hyb, hy]
      simpa using (tendsto_average_of_weaklyNull ht hv y).norm.pow 2
    · simp only [indicator_of_notMem hyb]
      exact tendsto_const_nhds
  have hdom : Integrable
      (fun y => ball.indicator (fun _ => (Real.sqrt (∫ z, Heat.kernel t z ^ 2) * M) ^ 2) y)
      volume :=
    (integrableOn_const (μ := volume)
      (measure_closedBall_lt_top (x := (0 : Space)) (r := R)).ne).integrable_indicator hball_meas
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) _ hmeas hdom
    hbound hlim
  simpa using h

/-- **B0714 (a)** (line 332): multiplication by `U ∈ C₀(ℝ³;ℝ³)` is compact `H¹ → L²`. -/
theorem c0MulCompact : C0MulCompact := by
  intro U f hf
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := ℝ) hf
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hv : ∀ ψ : L2Space, Tendsto (fun n => ⟪ψ, (f n).value⟫_ℝ) atTop (𝓝 0) := by
    have hw := ((weakTendsto_zero_iff (𝕜 := ℝ)).mpr hf).map H1.valueCLM
    rw [map_zero] at hw
    exact (weakTendsto_zero_iff (𝕜 := ℝ)).mp hw
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * Real.sqrt 8 * (2 : ℝ) ^ ((3 : ℝ) / 2) := ⟨_, rfl⟩
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- the tail
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.sqrt (δ / (8 * (M ^ 2 + 1))) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact Real.sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = δ / (8 * (M ^ 2 + 1)) := by rw [hηdef]; exact Real.sq_sqrt (by positivity)
  obtain ⟨R, hR⟩ := exists_tail U hη
  -- the heat time
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ / (8 * (‖U‖ ^ 2 * A ^ 2 * M ^ 2 + 1)) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; positivity
  have htK : t * (8 * (‖U‖ ^ 2 * A ^ 2 * M ^ 2 + 1)) = δ := by
    rw [htdef]; exact div_mul_cancel₀ δ (by positivity)
  -- the local term
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_ball_heat ht hM hv R)
    (δ / (8 * (‖U‖ ^ 2 + 1))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [Real.dist_eq, sub_zero] at hNn ⊢
  have hI0 : 0 ≤ ∫ y, (Metric.closedBall (0 : Space) R).indicator
      (fun y => ‖(Heat.heatOperator t (f n).value : SpatialField) y‖ ^ 2) y :=
    integral_nonneg fun y => indicator_nonneg (fun y _ => sq_nonneg _) y
  rw [abs_of_nonneg hI0] at hNn
  have hsplit := integral_mul_le_split U (f n).value (Heat.heatOperator t (f n).value) hη.le hR
  have hDnb : ‖(f n).value - Heat.heatOperator t (f n).value‖ ≤ A * Real.sqrt t * M := by
    refine (norm_sub_heat_le (f n) ht).trans ?_
    rw [hA, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have : 0 ≤ 3 * (Real.sqrt 8 * Real.sqrt t) * (2 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    calc 3 * (Real.sqrt 8 * Real.sqrt t) * (2 : ℝ) ^ ((3 : ℝ) / 2) * ‖f n‖
        ≤ 3 * (Real.sqrt 8 * Real.sqrt t) * (2 : ℝ) ^ ((3 : ℝ) / 2) * M :=
          mul_le_mul_of_nonneg_left (hM n) this
      _ = _ := by ring
  have hHn : ‖Heat.heatOperator t (f n).value‖ ≤ M :=
    (Heat.heatOperator_apply_norm_le t (f n).value).trans ((norm_value_le _).trans (hM n))
  have hval0 : 0 ≤ ∫ y, ‖U y‖ ^ 2 * ‖((f n).value : SpatialField) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  rw [abs_of_nonneg hval0]
  -- the three terms
  have hsqD : ‖(f n).value - Heat.heatOperator t (f n).value‖ ^ 2 ≤ A ^ 2 * t * M ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hDnb 2
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.le] at this
    exact this
  have hT1 := arith_heat_term hsqD ht htK
  have hT2 := arith_ball_term hNn (by positivity) (div_mul_cancel₀ δ (by positivity))
  have hT3 : 2 * η ^ 2 * ‖Heat.heatOperator t (f n).value‖ ^ 2 ≤ δ / 4 := by
    rw [hη2]
    exact arith_tail_term (pow_le_pow_left₀ (norm_nonneg _) hHn 2) (by positivity)
      (div_mul_cancel₀ δ (by positivity))
  linarith

end UnforcedLeray.Loc.L05
