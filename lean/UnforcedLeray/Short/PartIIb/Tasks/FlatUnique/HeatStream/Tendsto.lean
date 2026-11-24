import UnforcedLeray.Short.PartIIb.Sub.T11_3
import UnforcedLeray.Units.B0284.Contraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Tendsto.Scaling

/-!
# Part II-b, leaf `PartII-b:T11/3/6` (`HeatConvTendsto`): approximate identity in `L^p(cell)`

Source of record: `the November 2 reference manuscript`, SP 1923-1927 (heat flow
tends to its datum). Statement: `HeatConvTendsto` of `Sub/T11_3.lean`.

Proof outline (general `p > 0`, no sup-norm and no higher Gaussian moments):
* `f` is bounded (periodicity in `q`, compactness in `η`) and `|f(x)| ≤ M e^{L - |x₂|}`.
* Parabolic scaling `∫ G_{θ}(w) g(w) dw = ∫ G_1(u) g(√θ u) du` and `e^{|u₂|} G_1(u)` integrable give,
  for `0 < θ ≤ 1`, the uniform envelope `|G_θ * f (z) - f z| ≤ A e^{-|z₂|}`.
* `e^{-p|t|} ≤ 1/(m(1+t²))` makes the envelope integrable against the cell for every `p > 0`.
* Pointwise convergence `G_θ * f(z) → f(z)` by dominated convergence in the unit variable `u`.
* Conclude by `tendsto_lintegral_filter_of_dominated_convergence` along `𝓝[>] 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

namespace TendstoMain

theorem continuous_heatKernel2_aux (θ : ℝ) :
    Continuous (UnforcedLeray.B0284.heatKernel2 θ) := by
  unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  fun_prop

/-- A continuous `q`-periodic function vanishing for `|η| ≥ L` is bounded. -/
theorem exists_bound_of_periodic {c L : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hper : ∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) (hsupp : ∀ z : ℝ × ℝ, L ≤ |z.2| → f z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ × ℝ, ‖f z‖ ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := c)).prod
    (isCompact_Icc (a := -|L|) (b := |L|))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : L ≤ |z.2|
  · rw [hsupp z hz, norm_zero]
    exact le_max_right _ _
  · have hz' : |z.2| < L := not_le.mp hz
    obtain ⟨y, hy, hfy⟩ := Function.Periodic.exists_mem_Ico₀
      (f := fun x : ℝ => f (x, z.2)) (c := c) (fun x => hper (x, z.2)) hc z.1
    have hfz : f z = f (y, z.2) := hfy
    have hmem : (y, z.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-|L|) |L| := by
      refine ⟨⟨hy.1, hy.2.le⟩, abs_le.mp ?_⟩
      exact (hz'.le).trans (le_abs_self L)
    rw [hfz]
    exact (hC (y, z.2) hmem).trans (le_max_left _ _)

/-- The envelope `|f x| ≤ M e^{L - |x₂|}`. -/
theorem norm_le_envelope {L M : ℝ} (hM : 0 ≤ M) {f : ℝ × ℝ → ℝ} (hM' : ∀ z, ‖f z‖ ≤ M)
    (hsupp : ∀ z : ℝ × ℝ, L ≤ |z.2| → f z = 0) (z : ℝ × ℝ) :
    ‖f z‖ ≤ M * Real.exp (L - |z.2|) := by
  by_cases hz : L ≤ |z.2|
  · rw [hsupp z hz, norm_zero]
    positivity
  · have h1 : 1 ≤ Real.exp (L - |z.2|) := Real.one_le_exp (by linarith [not_le.mp hz])
    calc ‖f z‖ ≤ M := hM' z
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * Real.exp (L - |z.2|) := mul_le_mul_of_nonneg_left h1 hM

theorem exp_L_sub_abs_le {L a s b : ℝ} (hs : |s| ≤ |b|) :
    Real.exp (L - |a - s|) ≤ Real.exp (L - |a|) * Real.exp |b| := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := abs_sub_abs_le_abs_sub a s
  linarith

/-- Parabolic rescaling of the heat convolution. -/
theorem heatConv_eq_scaled {θ : ℝ} (hθ : 0 < θ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w) =
      ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * f (z - Real.sqrt θ • u) := by
  have h := UnforcedLeray.Short.IIb.TendstoAux.integral_heatKernel2_scale
    (r := Real.sqrt θ) (Real.sqrt_pos.mpr hθ) (fun w => f (z - w))
  rw [Real.sq_sqrt hθ.le] at h
  exact h

/-- Uniform-in-`θ` envelope of the heat convolution: `|G_θ * f(z)| ≤ M e^{L - |z₂|} C₁`. -/
theorem norm_heatConv_le {θ L M : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hM : 0 ≤ M)
    {f : ℝ × ℝ → ℝ} (henv : ∀ x : ℝ × ℝ, ‖f x‖ ≤ M * Real.exp (L - |x.2|)) (z : ℝ × ℝ) :
    ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)‖ ≤
      (M * Real.exp (L - |z.2|)) *
        ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2| := by
  rw [heatConv_eq_scaled hθ f z]
  have hs1 : Real.sqrt θ ≤ 1 := (Real.sqrt_le_sqrt hθ1).trans_eq Real.sqrt_one
  calc ‖∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * f (z - Real.sqrt θ • u)‖
      ≤ ∫ u : ℝ × ℝ, ‖UnforcedLeray.B0284.heatKernel2 1 u * f (z - Real.sqrt θ • u)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ × ℝ, (M * Real.exp (L - |z.2|)) *
          (UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2|) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
        · exact (UnforcedLeray.Short.IIb.TendstoAux.integrable_heatKernel2_mul_exp_abs).const_mul _
        · refine Eventually.of_forall (fun u => ?_)
          dsimp only
          have hG : 0 ≤ UnforcedLeray.B0284.heatKernel2 1 u :=
            UnforcedLeray.B0284.heatKernel2_nonneg one_pos u
          have hsabs : |Real.sqrt θ * u.2| ≤ |u.2| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg θ)]
            exact mul_le_of_le_one_left (abs_nonneg _) hs1
          have hexp := exp_L_sub_abs_le (L := L) (a := z.2) (s := Real.sqrt θ * u.2) (b := u.2)
            hsabs
          have hfx : ‖f (z - Real.sqrt θ • u)‖ ≤
              M * Real.exp (L - |z.2 - Real.sqrt θ * u.2|) := henv _
          rw [norm_mul, Real.norm_of_nonneg hG]
          calc UnforcedLeray.B0284.heatKernel2 1 u * ‖f (z - Real.sqrt θ • u)‖
              ≤ UnforcedLeray.B0284.heatKernel2 1 u *
                  (M * (Real.exp (L - |z.2|) * Real.exp |u.2|)) := by
                apply mul_le_mul_of_nonneg_left _ hG
                exact hfx.trans (mul_le_mul_of_nonneg_left hexp hM)
            _ = (M * Real.exp (L - |z.2|)) *
                  (UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2|) := by ring
    _ = (M * Real.exp (L - |z.2|)) *
          ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2| :=
        integral_const_mul _ _

/-- The heat convolution of a bounded continuous function is continuous. -/
theorem continuous_heatConv {θ M : ℝ} (hθ : 0 < θ) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hM' : ∀ z, ‖f z‖ ≤ M) :
    Continuous (fun z : ℝ × ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) := by
  refine continuous_of_dominated (bound := fun w => M * UnforcedLeray.B0284.heatKernel2 θ w)
    ?_ ?_ ?_ ?_
  · intro z
    exact ((continuous_heatKernel2_aux θ).mul
      (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · intro z
    refine Eventually.of_forall (fun w => ?_)
    rw [norm_mul, Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    exact (mul_le_mul_of_nonneg_left (hM' _)
      (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)).trans_eq (mul_comm _ _)
  · exact (UnforcedLeray.B0284.integrable_heatKernel2 hθ).const_mul M
  · refine Eventually.of_forall (fun w => ?_)
    exact continuous_const.mul (hf.comp (continuous_id.sub continuous_const))

/-- Pointwise approximate identity: `G_θ * f (z) → f (z)` as `θ → 0⁺`. -/
theorem tendsto_heatConv_nhds {M : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hM' : ∀ z, ‖f z‖ ≤ M) (z : ℝ × ℝ) :
    Tendsto (fun θ : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w))
      (𝓝[>] (0 : ℝ)) (𝓝 (f z)) := by
  have hsq : Tendsto (fun θ : ℝ => Real.sqrt θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ => Real.sqrt θ) (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hint : ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * f z = f z := by
    rw [integral_mul_const, UnforcedLeray.B0284.integral_heatKernel2 one_pos, one_mul]
  have hF : Tendsto
      (fun θ : ℝ => ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * f (z - Real.sqrt θ • u))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * f z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ × ℝ => M * UnforcedLeray.B0284.heatKernel2 1 u) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun θ => ?_)
      have hc : Continuous (fun u : ℝ × ℝ => f (z - Real.sqrt θ • u)) := by fun_prop
      exact ((continuous_heatKernel2_aux 1).mul hc).aestronglyMeasurable
    · refine Eventually.of_forall (fun θ => Eventually.of_forall (fun u => ?_))
      rw [norm_mul, Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg one_pos u)]
      exact (mul_le_mul_of_nonneg_left (hM' _)
        (UnforcedLeray.B0284.heatKernel2_nonneg one_pos u)).trans_eq (mul_comm _ _)
    · exact (UnforcedLeray.B0284.integrable_heatKernel2 one_pos).const_mul M
    · refine Eventually.of_forall (fun u => ?_)
      have h2 : Tendsto (fun θ : ℝ => Real.sqrt θ • u) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) • u)) :=
        hsq.smul_const u
      have h1 : Tendsto (fun θ : ℝ => z - Real.sqrt θ • u) (𝓝[>] (0 : ℝ))
          (𝓝 (z - (0 : ℝ) • u)) := tendsto_const_nhds.sub h2
      rw [zero_smul, sub_zero] at h1
      exact ((hf.tendsto z).comp h1).const_mul _
  have hF' := hF
  rw [hint] at hF'
  refine Tendsto.congr' ?_ hF'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact (heatConv_eq_scaled (Set.mem_Ioi.mp hθ) f z).symm

/-- The exponential-type envelope `(A e^{-|t|})^p` is integrable for every `p > 0`. -/
theorem integrable_rpow_exp_neg_abs {A p : ℝ} (hA : 0 ≤ A) (hp : 0 < p) :
    Integrable (fun t : ℝ => (A * Real.exp (-|t|)) ^ p) := by
  have hm0 : 0 < min 1 (p ^ 2 / 2) := lt_min one_pos (by positivity)
  have hm1 : min 1 (p ^ 2 / 2) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (p ^ 2 / 2) ≤ p ^ 2 / 2 := min_le_right _ _
  have hbound : ∀ t : ℝ, (A * Real.exp (-|t|)) ^ p ≤
      (A ^ p / min 1 (p ^ 2 / 2)) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hq := Real.quadratic_le_exp_of_nonneg (x := |t| * p) (by positivity)
    have hsq : (|t| * p) ^ 2 = t ^ 2 * p ^ 2 := by rw [mul_pow, sq_abs]
    have h3 : min 1 (p ^ 2 / 2) * t ^ 2 ≤ p ^ 2 / 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right hm2 (sq_nonneg t)
    have h4 : min 1 (p ^ 2 / 2) * (1 + t ^ 2) ≤ Real.exp (|t| * p) := by
      nlinarith [abs_nonneg t, mul_nonneg (abs_nonneg t) hp.le]
    have h5 : Real.exp (-|t| * p) ≤ (min 1 (p ^ 2 / 2) * (1 + t ^ 2))⁻¹ := by
      rw [show -|t| * p = -(|t| * p) by ring, Real.exp_neg]
      exact inv_anti₀ (by positivity) h4
    rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]
    have h6 : (min 1 (p ^ 2 / 2) * (1 + t ^ 2))⁻¹ =
        (min 1 (p ^ 2 / 2))⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [mul_inv]
    have hAp : 0 ≤ A ^ p := Real.rpow_nonneg hA p
    calc A ^ p * Real.exp (-|t| * p)
        ≤ A ^ p * (min 1 (p ^ 2 / 2) * (1 + t ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_left h5 hAp
      _ = (A ^ p / min 1 (p ^ 2 / 2)) * (1 + t ^ 2)⁻¹ := by
          rw [h6]
          ring
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (A ^ p / min 1 (p ^ 2 / 2))) ?_ ?_
  · exact (Continuous.rpow_const (by fun_prop) (fun _ => Or.inr hp.le)).aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg hA (Real.exp_pos _).le) p)]
    exact hbound t

/-- Pointwise indicator inequality on the centred cell. -/
theorem cell_indicator_le {A p c : ℝ} (z : ℝ × ℝ) :
    (UnforcedLeray.Cyl.cell c).indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p) z ≤
      (Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞) z.1 *
        ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p := by
  by_cases hz : z ∈ UnforcedLeray.Cyl.cell c
  · have h1 : z.1 ∈ Set.Ico (-c / 2) (c / 2) := hz.1
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem h1, Pi.one_apply, one_mul, le_refl]
  · simp [Set.indicator_of_notMem hz]

/-- The tail envelope has finite lower integral against the normalized cell measure. -/
theorem lintegral_tail_ne_top {A p c : ℝ} (hA : 0 ≤ A) (hp : 0 < p) :
    ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p ∂(UnforcedLeray.Cyl.avgμ c) ≠ ⊤ := by
  have hS : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hgInt : ∫⁻ y : ℝ, ENNReal.ofReal (A * Real.exp (-|y|)) ^ p ≠ ⊤ := by
    have h : ∫⁻ y : ℝ, ENNReal.ofReal (A * Real.exp (-|y|)) ^ p =
        ∫⁻ y : ℝ, ENNReal.ofReal ((A * Real.exp (-|y|)) ^ p) :=
      lintegral_congr (fun y => ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg hA (Real.exp_pos _).le) hp.le)
    rw [h]
    exact (integrable_rpow_exp_neg_abs hA hp).lintegral_lt_top.ne
  have hI : Measurable ((Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Ico
  have hG : Measurable (fun y : ℝ => ENNReal.ofReal (A * Real.exp (-|y|)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun y : ℝ =>
      A * Real.exp (-|y|))).pow_const p
  have hprod : ∫⁻ z : ℝ × ℝ, (Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞) z.1 *
      ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p ∂(volume : Measure (ℝ × ℝ)) =
      (∫⁻ x : ℝ, (Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞) x) *
        ∫⁻ y : ℝ, ENNReal.ofReal (A * Real.exp (-|y|)) ^ p := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact lintegral_prod_mul hI.aemeasurable hG.aemeasurable
  have hIfin : ∫⁻ x : ℝ, (Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞) x ≠ ⊤ := by
    rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hfinal : ∫⁻ z : ℝ × ℝ, (Set.Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ≥0∞) z.1 *
      ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
    rw [hprod]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hIfin) (lt_top_iff_ne_top.mpr hgInt)
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [lintegral_smul_measure]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [← lintegral_indicator hS]
  exact ne_top_of_lt ((lintegral_mono (fun z => cell_indicator_le (A := A) (p := p) (c := c) z)).trans_lt hfinal)

end TendstoMain

/-- **Leaf `PartII-b:T11/3/6`** (approximate identity in `L^p(cell)`). For `f` continuous,
`c`-periodic, vanishing for `|η|` large, and `p > 0`, `G_θ * f → f` in `L^p(Cyl.avgμ c)` as
`θ → 0+`. -/
theorem heatConvTendsto : HeatConvTendsto := by
  unfold HeatConvTendsto
  intro c p f hc hp hf hper hsupp
  obtain ⟨L, hL⟩ := hsupp
  obtain ⟨M, hM0, hM⟩ := TendstoMain.exists_bound_of_periodic hc hf hper hL
  have henv : ∀ x : ℝ × ℝ, ‖f x‖ ≤ M * Real.exp (L - |x.2|) :=
    TendstoMain.norm_le_envelope hM0 hM hL
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ,
      C1 = ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2| := ⟨_, rfl⟩
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    exact integral_nonneg (fun u => mul_nonneg
      (UnforcedLeray.B0284.heatKernel2_nonneg one_pos u) (Real.exp_pos _).le)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = M * (C1 + 1) * Real.exp L := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg hM0 (by linarith)) (Real.exp_pos _).le
  have hbd : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ z : ℝ × ℝ,
      ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ ≤
        A * Real.exp (-|z.2|) := by
    intro θ hθ hθ1 z
    have h1 := TendstoMain.norm_heatConv_le hθ hθ1 hM0 henv z
    rw [← hC1] at h1
    have h2 := henv z
    have hexpsplit : Real.exp (L - |z.2|) = Real.exp L * Real.exp (-|z.2|) := by
      rw [sub_eq_add_neg, Real.exp_add]
    calc ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖
        ≤ ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)‖ + ‖f z‖ :=
          norm_sub_le _ _
      _ ≤ (M * Real.exp (L - |z.2|)) * C1 + M * Real.exp (L - |z.2|) := add_le_add h1 h2
      _ = A * Real.exp (-|z.2|) := by
          rw [hA, hexpsplit]
          ring
  have hmeas : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Measurable (fun z : ℝ × ℝ =>
      ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ^ p) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : 0 < θ := Set.mem_Ioi.mp hθ
    have hcont : Continuous (fun z : ℝ × ℝ =>
        (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z) :=
      (TendstoMain.continuous_heatConv hθ0 hf hM).sub hf
    exact (ENNReal.continuous_rpow_const (y := p) |>.comp
      (continuous_enorm.comp hcont)).measurable
  have hbdd : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c),
      ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ^ p ≤
        ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    refine ae_of_all _ (fun z => ?_)
    have h' : ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ≤
        ENNReal.ofReal (A * Real.exp (-|z.2|)) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbd θ hθ.1 hθ.2.le z)
    exact ENNReal.rpow_le_rpow h' hp.le
  have hfin : ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p
      ∂(UnforcedLeray.Cyl.avgμ c) ≠ ⊤ :=
    TendstoMain.lintegral_tail_ne_top hA0 hp
  have hlim : ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), Tendsto (fun θ : ℝ =>
      ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ^ p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine ae_of_all _ (fun z => ?_)
    have h1 : Tendsto (fun θ : ℝ =>
        (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 := (TendstoMain.tendsto_heatConv_nhds hf hM z).sub_const (f z)
      rwa [sub_self] at h0
    have h2 : Tendsto (fun θ : ℝ =>
        ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun θ : ℝ =>
          ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ)
          (𝓝[>] (0 : ℝ)) (𝓝 ‖(0 : ℝ)‖ₑ) :=
        (continuous_enorm.tendsto (0 : ℝ)).comp h1
      rwa [enorm_zero] at h0
    have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
    rw [ENNReal.zero_rpow_of_pos hp] at h3
    exact h3
  have key := tendsto_lintegral_filter_of_dominated_convergence
    (μ := UnforcedLeray.Cyl.avgμ c) (l := 𝓝[>] (0 : ℝ))
    (F := fun (θ : ℝ) (z : ℝ × ℝ) =>
      ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ^ p)
    (f := fun _ => (0 : ℝ≥0∞))
    (fun z : ℝ × ℝ => ENNReal.ofReal (A * Real.exp (-|z.2|)) ^ p) hmeas hbdd hfin hlim
  simpa using key

end UnforcedLeray.Short.IIb
