import UnforcedLeray.Lib.HeatR3.HeatDecay
import UnforcedLeray.Lib.HeatR3.FTC

/-!
# The heat increment of the inlet: `|D^j(e^{νΔ}b - b)(y)| ≤ K|y|^{-3-j}` (INF04 T9, (2.48))


`heat_sub_self_decay`, by bypass BP4 (cutoff and heat FTC instead of Taylor expansion with a
vanishing first moment). Equation (2.48) of the manuscript (tex 5934–5953, B0698; B0306).

For `b ∈ 𝒦₄(C)` (`|D^i b(x)| ≤ C|x|^{-1-i}`, `i ≤ 4`), `ν > 0`, `j ≤ 2` and `|y| ≥ 1`:

`|D^j(e^{νΔ}b - b)(y)| ≤ K |y|^{-3-j}`,   `K = K(C, ν, j)` uniform over the class.

Proof (BP4): `b = χb + (b - χb)` with the fixed bump `χ` of `HeatDecay.lean`.
* `D^j e^{νΔ}(χb)(y) = O(⟨y⟩^{-3-j})` (kernel side, weight transfer);
* `D^j(χb)(y)` vanishes for `|y| > 2` and is bounded for `1 ≤ |y| ≤ 2`;
* `w = b - χb ∈ C⁴(ℝ³)` with `|D^i w(z)| ≤ K⟨z⟩^{-1-i}`; by the heat FTC applied to `D^j w`,
  `D^j(e^{νΔ}w - w) = ∫_0^ν e^{tΔ}Δ(D^j w) dt`, and `|Δ D^j w| ≤ 3K⟨z⟩^{-3-j}` with the weighted
  heat bound gives `O(ν ⟨y⟩^{-3-j})`.
The general-order lemmas `*_gen` restate those of `HeatDecay.lean` for the class `𝒦_k`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem InvDistClass.bound'' {k : ℕ} {C : ℝ} {v : Space → E} (hv : InvDistClass k C v) {i : ℕ}
    (hi : i ≤ k) {x : Space} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ i v x‖ ≤ C * ‖x‖ ^ (-((1 + i : ℕ) : ℝ)) := by
  have h := hv.bound i hi x hx
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem InvDistClass.const_nonneg' {k : ℕ} {C : ℝ} {v : Space → E} (hv : InvDistClass k C v) :
    0 ≤ C := by
  set x : Space := EuclideanSpace.single 0 1
  have hx : x ≠ 0 := by simp [x]
  have h := hv.bound 0 (Nat.zero_le k) x hx
  have hpos : 0 < ‖x‖ ^ (-(1 + ((0 : ℕ) : ℝ))) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hpos

theorem InvDistClass.norm_le' {k : ℕ} {C : ℝ} {v : Space → E} (hv : InvDistClass k C v)
    {x : Space} (hx : x ≠ 0) : ‖v x‖ ≤ C * ‖x‖⁻¹ := by
  have h := hv.bound 0 (Nat.zero_le k) x hx
  rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero, Real.rpow_neg_one] at h

/-- `‖D^k(D^n f)(x)‖ = ‖D^{k+n} f(x)‖` (no regularity needed). -/
theorem norm_iteratedFDeriv_iteratedFDeriv' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (n : ℕ) : ∀ (k : ℕ) (x : Space),
      ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ n f) x‖ = ‖iteratedFDeriv ℝ (k + n) f x‖ := by
  induction n with
  | zero =>
    intro k x
    rw [add_zero, iteratedFDeriv_zero_eq_comp,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  | succ n ih =>
    intro k x
    have h := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) F)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) F).symm
      (fderiv ℝ (iteratedFDeriv ℝ n f)) x k
    rw [iteratedFDeriv_succ_eq_comp_left]
    refine h.trans ?_
    rw [norm_iteratedFDeriv_fderiv, ih (k + 1) x, show k + 1 + n = k + (n + 1) by omega]

/-- Pointwise `|Δu(z)| ≤ 3 |D²u(z)|`. -/
theorem norm_vlap_le_pt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (u : Space → F) (z : Space) : ‖vlap u z‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 u z‖ := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖iteratedFDeriv ℝ 2 u z ![coordinateVector i, coordinateVector i]‖ ≤
      ‖iteratedFDeriv ℝ 2 u z‖ := by
    intro i
    refine ((iteratedFDeriv ℝ 2 u z).le_opNorm _).trans ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, norm_coordinateVector, mul_one, le_refl]
  calc ∑ i : Fin 3, ‖iteratedFDeriv ℝ 2 u z ![coordinateVector i, coordinateVector i]‖
      ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 2 u z‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖iteratedFDeriv ℝ 2 u z‖ := by simp

theorem heatNear_bound_gen {k : ℕ} {C : ℝ} (j m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ K : ℝ, ∀ v : Space → E, InvDistClass k C v → ∀ y : Space,
      ‖iteratedFDeriv ℝ j (average θ (fun z => cut z • v z)) y‖ ≤
        K * (1 + ‖y‖) ^ (-(m : ℝ)) := by
  obtain ⟨C', hC'0, hC'⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 j hθ
    (m := (m : ℝ)) (by positivity)
  refine ⟨C' * (3 ^ m * C * ∫ y in Metric.closedBall (0 : Space) 2, ‖y‖ ^ (-(1 : ℝ))),
    fun v hv y => ?_⟩
  have hC := hv.const_nonneg'
  have hadm : HeatAdmissible (fun z => cut z • v z) := by
    refine HeatAdmissible.of_inv_bound ?_ (C := C) fun x hx => ?_
    · have hm := hv.heatAdmissible.1
      exact (contDiff_cut.continuous.aestronglyMeasurable).smul hm
    · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg x)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one x)).trans (hv.norm_le' hx)
  refine (norm_iteratedFDeriv_average_le_kernel hadm hθ j y).trans ?_
  set g : Space → ℝ := fun z => 3 ^ m * C *
    (Metric.closedBall (0 : Space) 2).indicator (fun z => ‖z‖ ^ (-(1 : ℝ))) z with hg
  have hgi : Integrable g :=
    (integrableOn_inv_norm_closedBall_two.integrable_indicator
      Metric.isClosed_closedBall.measurableSet).const_mul _
  have hbound : ∀ᵐ z ∂(volume : Measure Space),
      ‖iteratedFDeriv ℝ j (kernel θ) (y - z)‖ * ‖cut z • v z‖ ≤
        C' * (1 + ‖y‖) ^ (-(m : ℝ)) * g z := by
    filter_upwards [Measure.ae_ne volume (0 : Space)] with z hz
    have hK : ‖iteratedFDeriv ℝ j (kernel θ) (y - z)‖ ≤
        C' * ((1 + ‖z‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) := by
      rw [← Gaussian.gaussKernel_three_eq]
      refine (hC' (y - z)).trans (mul_le_mul_of_nonneg_left ?_ hC'0.le)
      have h := one_add_norm_sub_rpow_neg_le (m := (m : ℝ)) (by positivity) z y
      rwa [norm_sub_rev] at h
    by_cases hz2 : 2 ≤ ‖z‖
    · rw [cut_eq_zero hz2, zero_smul, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hC'0.le (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg (mul_nonneg (by positivity) hC)
          (Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _))
    · push_neg at hz2
      have hmem : z ∈ Metric.closedBall (0 : Space) 2 := by
        simpa using hz2.le
      have hvz : ‖cut z • v z‖ ≤ C * ‖z‖ ^ (-(1 : ℝ)) := by
        rw [norm_smul, Real.norm_of_nonneg (cut_nonneg z), Real.rpow_neg_one]
        exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one z)).trans (hv.norm_le' hz)
      have h27 : (1 + ‖z‖) ^ (m : ℝ) ≤ 3 ^ m := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      rw [hg]
      simp only [Set.indicator_of_mem hmem]
      have hw : 0 ≤ (1 + ‖y‖) ^ (-(m : ℝ)) := Real.rpow_nonneg (by positivity) _
      calc ‖iteratedFDeriv ℝ j (kernel θ) (y - z)‖ * ‖cut z • v z‖
          ≤ C' * ((1 + ‖z‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) *
              (C * ‖z‖ ^ (-(1 : ℝ))) := by gcongr
        _ ≤ C' * (3 ^ m * (1 + ‖y‖) ^ (-(m : ℝ))) * (C * ‖z‖ ^ (-(1 : ℝ))) := by
            gcongr
        _ = C' * (1 + ‖y‖) ^ (-(m : ℝ)) * (3 ^ m * C * ‖z‖ ^ (-(1 : ℝ))) := by ring
  calc ∫ z : Space, ‖iteratedFDeriv ℝ j (kernel θ) (y - z)‖ * ‖cut z • v z‖
      ≤ ∫ z : Space, C' * (1 + ‖y‖) ^ (-(m : ℝ)) * g z :=
        integral_mono_of_nonneg (Eventually.of_forall fun z =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hgi.const_mul _) hbound
    _ = C' * (3 ^ m * C * ∫ y in Metric.closedBall (0 : Space) 2, ‖y‖ ^ (-(1 : ℝ))) *
          (1 + ‖y‖) ^ (-(m : ℝ)) := by
        rw [integral_const_mul, hg, integral_const_mul, integral_indicator
          Metric.isClosed_closedBall.measurableSet]
        ring

/-- The Leibniz constant of `χv` on `|z| ≥ 1`. -/
theorem cut_smul_deriv_bound_gen (k : ℕ) (C : ℝ) {i : ℕ} (hi : i ≤ k) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : Space → E, InvDistClass k C v → ∀ z : Space, 1 ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤ L := by
  choose B hB0 hB using cut_deriv_bound
  refine ⟨∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B l * |C|,
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hB0 l)) (abs_nonneg C),
    fun v hv z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hmem : z ∈ ({0}ᶜ : Set Space) := hz0
  have hcut : ContDiffOn ℝ k cut {0}ᶜ := (contDiff_infty.mp contDiff_cut k).contDiffOn
  have hL := norm_iteratedFDerivWithin_smul_le hcut hv.smooth hopen.uniqueDiffOn hmem
    (n := i) (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen i hopen hmem] at hL
  refine hL.trans (Finset.sum_le_sum fun l hl => ?_)
  rw [iteratedFDerivWithin_of_isOpen l hopen hmem,
    iteratedFDerivWithin_of_isOpen (i - l) hopen hmem]
  have hil : i - l ≤ k := by omega
  have hv' := hv.bound'' hil hz0
  have hzpow : ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hz (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hvl : ‖iteratedFDeriv ℝ (i - l) v z‖ ≤ |C| := by
    refine hv'.trans ?_
    calc C * ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) ≤ |C| * ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ |C| * 1 := by gcongr
      _ = |C| := mul_one _
  calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l cut z‖ * ‖iteratedFDeriv ℝ (i - l) v z‖
      ≤ (i.choose l : ℝ) * B l * |C| :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hB l z) (by positivity)) hvl (norm_nonneg _)
          (mul_nonneg (by positivity) (hB0 l))

theorem contDiffAt_far_gen {k : ℕ} {C : ℝ} {v : Space → E} (hv : InvDistClass k C v) (z : Space) :
    ContDiffAt ℝ k (fun z => v z - cut z • v z) z := by
  by_cases hz : z = 0
  · subst hz
    have h : (fun z => v z - cut z • v z) =ᶠ[𝓝 (0 : Space)] fun _ => (0 : E) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) one_pos] with w hw
      exact far_eq_zero (by simpa using (Metric.mem_ball.mp hw).le)
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
    have hvz : ContDiffAt ℝ k v z := hv.smooth.contDiffAt (hopen.mem_nhds hz)
    exact hvz.sub ((contDiff_infty.mp contDiff_cut k).contDiffAt.smul hvz)

theorem contDiff_far_gen {k : ℕ} {C : ℝ} {v : Space → E} (hv : InvDistClass k C v) :
    ContDiff ℝ k (fun z => v z - cut z • v z) :=
  contDiff_iff_contDiffAt.mpr (contDiffAt_far_gen hv)

theorem far_deriv_bound_gen (k : ℕ) (C : ℝ) {i : ℕ} (hi : i ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Space → E, InvDistClass k C v → ∀ z : Space,
      ‖iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z‖ ≤
        K * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
  obtain ⟨L, hL0, hL⟩ := cut_smul_deriv_bound_gen (E := E) k C hi
  refine ⟨2 ^ (1 + i) * |C| + 3 ^ (1 + i) * L, by positivity, fun v hv z => ?_⟩
  have hw : 0 ≤ (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  by_cases hz1 : ‖z‖ < 1
  · have h : (fun z => v z - cut z • v z) =ᶠ[𝓝 z] fun _ => (0 : E) := by
      have : {w : Space | ‖w‖ < 1} ∈ 𝓝 z :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hz1
      filter_upwards [this] with w hw
      exact far_eq_zero hw.le
    rw [(h.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
  push_neg at hz1
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hvz : ContDiffAt ℝ i v z :=
    (hv.smooth.contDiffAt (hopen.mem_nhds hz0)).of_le (by exact_mod_cast hi)
  have hwz : ContDiffAt ℝ i (fun z => cut z • v z) z :=
    (contDiff_cut.of_le (by exact_mod_cast le_top)).contDiffAt.smul hvz
  have hsub : iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z =
      iteratedFDeriv ℝ i v z - iteratedFDeriv ℝ i (fun z => cut z • v z) z :=
    iteratedFDeriv_sub_apply (f := v) (g := fun z => cut z • v z) hvz hwz
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ i v z‖ ≤ 2 ^ (1 + i) * |C| * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
    refine (hv.bound'' hi hz0).trans ?_
    have h2 := rpow_neg_le_two_pow_mul hz1 (1 + i)
    calc C * ‖z‖ ^ (-((1 + i : ℕ) : ℝ)) ≤ |C| * ‖z‖ ^ (-((1 + i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ |C| * (2 ^ (1 + i) * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := by gcongr
      _ = 2 ^ (1 + i) * |C| * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by ring
  have h2 : ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤
      3 ^ (1 + i) * L * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
    by_cases hz2 : 2 < ‖z‖
    · rw [iteratedFDeriv_cut_smul_eq_zero i hz2, norm_zero]; positivity
    · push_neg at hz2
      have h3 := one_le_three_pow_mul (norm_nonneg z) hz2 (1 + i)
      calc ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤ L := hL v hv z hz1
        _ ≤ L * (3 ^ (1 + i) * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := le_mul_of_one_le_right hL0 h3
        _ = 3 ^ (1 + i) * L * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by ring
  linarith

/-! ### The estimate (2.48) -/

/-- **INF04 T9 `heat_sub_self_decay`** ((2.48), BP4; B0698, B0306). For `b ∈ 𝒦₄(C)`, `ν > 0`,
`j ≤ 2`: there is `K = K(C, ν, j)` with
`‖D^j(e^{νΔ}b - b)(y)‖ ≤ K |y|^{-3-j}` for every `|y| ≥ 1`, uniformly over the class. -/
theorem heat_sub_self_decay (C : ℝ) {ν : ℝ} (hν : 0 < ν) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ b : Space → E, InvDistClass 4 C b → ∀ y : Space, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (fun y => average ν b y - b y) y‖ ≤
        K * ‖y‖ ^ (-((3 + j : ℕ) : ℝ)) := by
  obtain ⟨K₁, hK₁⟩ := heatNear_bound_gen (E := E) (k := 4) (C := C) j (3 + j) hν
  obtain ⟨L, hL0, hL⟩ := cut_smul_deriv_bound_gen (E := E) 4 C (i := j) (by omega)
  have hall : ∀ i ≤ 4, ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Space → E, InvDistClass 4 C v → ∀ z : Space,
      ‖iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z‖ ≤
        K * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := fun i hi => far_deriv_bound_gen 4 C hi
  choose! Kf hKf0 hKf using hall
  set M := Kf 0 + Kf 1 + Kf 2 + Kf 3 + Kf 4 with hM
  set β : ℝ := -((3 + j : ℕ) : ℝ) with hβ
  set Kt := ν * (momentConst |β| ν * (3 * Kf (j + 2))) with hKt
  have hKt0 : 0 ≤ Kt := mul_nonneg hν.le (mul_nonneg (momentConst_nonneg _)
    (mul_nonneg (by norm_num) (hKf0 (j + 2) (by omega))))
  refine ⟨|K₁| + 3 ^ (3 + j) * L + Kt, fun b hb y hy => ?_⟩
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy; linarith
  have hyβ : (1 + ‖y‖) ^ β ≤ ‖y‖ ^ β := by
    rw [hβ, Real.rpow_neg (by positivity), Real.rpow_neg (norm_nonneg _), Real.rpow_natCast,
      Real.rpow_natCast]
    exact inv_anti₀ (pow_pos (norm_pos_iff.mpr hy0) _)
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith) _)
  have hw0 : 0 ≤ (1 + ‖y‖) ^ β := Real.rpow_nonneg (by positivity) _
  set w₁ : Space → E := fun z => cut z • b z with hw₁
  set w₂ : Space → E := fun z => b z - cut z • b z with hw₂
  have hadm := hb.heatAdmissible
  have hadm₁ : HeatAdmissible w₁ := by
    refine HeatAdmissible.of_inv_bound ?_ (C := C) fun x hx => ?_
    · exact (contDiff_cut.continuous.aestronglyMeasurable).smul hadm.1
    · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg x)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one x)).trans (hb.norm_le' hx)
  have hadm₂ : HeatAdmissible w₂ := hadm.sub hadm₁
  -- the decomposition
  have hsplit : (fun y => average ν b y - b y) =
      (fun y => average ν w₁ y) - w₁ + (fun y => average ν w₂ y - w₂ y) := by
    have hb12 : b = w₁ + w₂ := by
      funext z; simp only [hw₁, hw₂, Pi.add_apply, add_sub_cancel]
    have havg : average ν b = average ν w₁ + average ν w₂ := by
      rw [← average_add' hadm₁ hadm₂ hν, ← hb12]
    funext z
    rw [havg]
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hb12]
    simp only [Pi.add_apply]
    abel
  -- regularity at `y`
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hbz : ContDiffAt ℝ 4 b y := hb.smooth.contDiffAt (hopen.mem_nhds hy0)
  have hG1 : ContDiffAt ℝ j (fun y => average ν w₁ y) y :=
    (contDiff_average hadm₁ hν).contDiffAt.of_le (by exact_mod_cast le_top)
  have hH1 : ContDiffAt ℝ j w₁ y :=
    ((contDiff_infty.mp contDiff_cut 4).contDiffAt.smul hbz).of_le
      (by exact_mod_cast (by omega : j ≤ 4))
  have hw₂c : ContDiff ℝ 4 w₂ := contDiff_far_gen hb
  have hG2 : ContDiffAt ℝ j (fun y => average ν w₂ y - w₂ y) y :=
    ((contDiff_average hadm₂ hν).contDiffAt.of_le (by exact_mod_cast le_top)).sub
      (hw₂c.contDiffAt.of_le (by exact_mod_cast (by omega : j ≤ 4)))
  rw [hsplit, iteratedFDeriv_add_apply (f := (fun y => average ν w₁ y) - w₁)
    (g := fun y => average ν w₂ y - w₂ y) (hG1.sub hH1) hG2,
    iteratedFDeriv_sub_apply hG1 hH1]
  -- (1) the heat flow of the near part
  have h1 : ‖iteratedFDeriv ℝ j (fun y => average ν w₁ y) y‖ ≤ |K₁| * (1 + ‖y‖) ^ β := by
    refine (hK₁ b hb y).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self K₁) hw0
  -- (2) the near part itself
  have h2 : ‖iteratedFDeriv ℝ j w₁ y‖ ≤ 3 ^ (3 + j) * L * (1 + ‖y‖) ^ β := by
    by_cases hy2 : 2 < ‖y‖
    · rw [hw₁, iteratedFDeriv_cut_smul_eq_zero j hy2, norm_zero]; positivity
    · push_neg at hy2
      have h3 := one_le_three_pow_mul (norm_nonneg y) hy2 (3 + j)
      calc ‖iteratedFDeriv ℝ j w₁ y‖ ≤ L := hL b hb y hy
        _ ≤ L * (3 ^ (3 + j) * (1 + ‖y‖) ^ β) := le_mul_of_one_le_right hL0 h3
        _ = 3 ^ (3 + j) * L * (1 + ‖y‖) ^ β := by ring
  -- (3) the far part, by the heat FTC applied to `D^j w₂`
  have hbd4 : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k w₂ z‖ ≤ M := by
    intro k hk z
    have h := hKf k hk b hb z
    have hw : (1 + ‖z‖) ^ (-((1 + k : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hKk : Kf k ≤ M := by
      have := hKf0 0 (by norm_num); have := hKf0 1 (by norm_num); have := hKf0 2 (by norm_num)
      have := hKf0 3 (by norm_num); have := hKf0 4 (by norm_num)
      interval_cases k <;> simp only [hM] <;> linarith
    calc _ ≤ Kf k * (1 + ‖z‖) ^ (-((1 + k : ℕ) : ℝ)) := h
      _ ≤ Kf k * 1 := by gcongr; exact hKf0 k hk
      _ ≤ M := by rw [mul_one]; exact hKk
  have hDj : ContDiff ℝ 2 (iteratedFDeriv ℝ j w₂) :=
    hw₂c.iteratedFDeriv_right (by exact_mod_cast (by omega : 2 + j ≤ 4))
  have hbdj : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j w₂) z‖ ≤ M := by
    intro k hk z
    rw [norm_iteratedFDeriv_iteratedFDeriv']
    exact hbd4 (k + j) (by omega) z
  have h3 : ‖iteratedFDeriv ℝ j (fun y => average ν w₂ y - w₂ y) y‖ ≤ Kt * (1 + ‖y‖) ^ β := by
    have hsub : iteratedFDeriv ℝ j (fun y => average ν w₂ y - w₂ y) y =
        average ν (iteratedFDeriv ℝ j w₂) y - iteratedFDeriv ℝ j w₂ y := by
      show iteratedFDeriv ℝ j ((fun y => average ν w₂ y) - w₂) y = _
      rw [iteratedFDeriv_sub_apply (f := fun y => average ν w₂ y) (g := w₂)
        ((contDiff_average hadm₂ hν).contDiffAt.of_le (by exact_mod_cast le_top))
        (hw₂c.contDiffAt.of_le (by exact_mod_cast (by omega : j ≤ 4)))]
      rw [iteratedFDeriv_average (n := 4) hν hw₂c hbd4 j (by omega)]
    rw [hsub, average_sub_eq_integral hDj hbdj hν y]
    have hvb : ∀ z, ‖vlap (iteratedFDeriv ℝ j w₂) z‖ ≤ 3 * Kf (j + 2) * (1 + ‖z‖) ^ β := by
      intro z
      refine (norm_vlap_le_pt _ z).trans ?_
      rw [norm_iteratedFDeriv_iteratedFDeriv']
      have h := hKf (j + 2) (by omega) b hb z
      have he : ((1 + (j + 2) : ℕ) : ℝ) = ((3 + j : ℕ) : ℝ) := by push_cast; ring
      rw [he, ← hβ] at h
      have h' : ‖iteratedFDeriv ℝ (2 + j) w₂ z‖ ≤ Kf (j + 2) * (1 + ‖z‖) ^ β := by
        rw [show 2 + j = j + 2 by omega]; exact h
      linarith
    have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) ν, ‖average t (vlap (iteratedFDeriv ℝ j w₂)) y‖ ≤
        momentConst |β| ν * (3 * Kf (j + 2)) * (1 + ‖y‖) ^ β := by
      intro t ht
      rw [uIoc_of_le hν.le] at ht
      have h := norm_average_le_weight (Θ := ν) (β := β) (M := 3 * Kf (j + 2)) ht.1 ht.2
        (fun z => by simpa only [mul_assoc] using hvb z) y
      simpa only [mul_assoc] using h
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    refine h.trans (le_of_eq ?_)
    rw [sub_zero, abs_of_pos hν, hKt]; ring
  -- (4) sum up
  have htot : ‖iteratedFDeriv ℝ j (fun y => average ν w₁ y) y - iteratedFDeriv ℝ j w₁ y +
      iteratedFDeriv ℝ j (fun y => average ν w₂ y - w₂ y) y‖ ≤
      (|K₁| + 3 ^ (3 + j) * L + Kt) * (1 + ‖y‖) ^ β := by
    rw [add_mul, add_mul]
    linarith [norm_add_le (iteratedFDeriv ℝ j (fun y => average ν w₁ y) y -
      iteratedFDeriv ℝ j w₁ y) (iteratedFDeriv ℝ j (fun y => average ν w₂ y - w₂ y) y),
      norm_sub_le (iteratedFDeriv ℝ j (fun y => average ν w₁ y) y) (iteratedFDeriv ℝ j w₁ y)]
  refine htot.trans ?_
  have hK0 : 0 ≤ |K₁| + 3 ^ (3 + j) * L + Kt := by positivity
  exact mul_le_mul_of_nonneg_left hyβ hK0

end UnforcedLeray.Heat
