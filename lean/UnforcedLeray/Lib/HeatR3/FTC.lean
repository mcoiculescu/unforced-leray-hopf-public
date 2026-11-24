import UnforcedLeray.Lib.HeatR3.Smooth
import UnforcedLeray.Lib.HeatR3.Decay
import UnforcedLeray.Analysis.Heat.DerivativeLp

/-!
# The heat equation and the heat FTC for `C²_b` data on `ℝ³` (INF04 T7, `average_sub_eq_integral`)


for `u ∈ C²(ℝ³; E)` with `u, Du, D²u` bounded,

`e^{θΔ}u(x) - u(x) = ∫_0^θ e^{tΔ}(Δu)(x) dt`   (the heat FTC of bypass BP4, B0720, B0722).

Proof without integration by parts: the time derivative of the kernel is its Laplacian
(compiled `timeDerivativeKernel_eq_laplacian`), the Laplacian of `e^{tΔ}u` computed on the
kernel side (`kconv`) is `∫ ΔG_t(x - y) u(y) dy`, and computed on the data side
(`iteratedFDeriv_average`) it is `e^{tΔ}(Δu)(x)`. The value at `t = 0⁺` is the approximate
identity `|e^{εΔ}u(x) - u(x)| ≤ ‖Du‖_∞ ∫ G_ε(y)|y| dy = O(√ε)`.

Main results:
* `vlap` (the coordinate vector Laplacian), `norm_vlap_le`;
* `hasDerivAt_average_time_of_bound`: `t ↦ e^{tΔ}g(x)` is differentiable for bounded measurable
  `g` (`t > 0`), with derivative `∫ ∂_tG_t(y) g(x - y) dy`;
* `hasDerivAt_average_time`: `∂_t e^{tΔ}u(x) = e^{tΔ}(Δu)(x)` for `u ∈ C²_b`;
* `norm_average_sub_le_sqrt`: `|e^{εΔ}u(x) - u(x)| ≤ c ‖Du‖_∞ √ε`;
* `average_sub_eq_integral`: the heat FTC.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The coordinate vector Laplacian `Δu(x) = Σ_i D²u(x)(e_i, e_i)` of `u : ℝ³ → E`. -/
def vlap (u : Space → E) (x : Space) : E :=
  ∑ i : Fin 3, iteratedFDeriv ℝ 2 u x ![coordinateVector i, coordinateVector i]

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem norm_vlap_le {u : Space → E} {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ M)
    (x : Space) : ‖vlap u x‖ ≤ 3 * M := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ 2 u x ![coordinateVector i, coordinateVector i]‖ ≤ M := by
    intro i
    refine ((iteratedFDeriv ℝ 2 u x).le_opNorm _).trans ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, norm_coordinateVector, mul_one]
    exact hM x
  calc ∑ i : Fin 3, ‖iteratedFDeriv ℝ 2 u x ![coordinateVector i, coordinateVector i]‖
      ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => h i
    _ = 3 * M := by simp

/-! ### Differentiability in time for bounded data -/

/-- **Time derivative of the heat flow of bounded data** (adapted from the compiled
`average_hasDerivAt_timeDerivativeKernel`, `Analysis/Heat/AveragingEvolution.lean`, for `L²`
data): for `g` measurable with `|g| ≤ M` and `t > 0`. -/
theorem hasDerivAt_average_time_of_bound {g : Space → E} (hg : AEStronglyMeasurable g volume)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s : ℝ => average s g x)
      (∫ y : Space, timeDerivativeKernel t y • g (x - y)) t := by
  let F : ℝ → Space → E := fun s y => kernel s y • g (x - y)
  let F' : ℝ → Space → E := fun s y => timeDerivativeKernel s y • g (x - y)
  let B : Space → ℝ := fun y => (4 * Gaussian.timeEnvelope (4 * t) y) * M
  have hs : AEStronglyMeasurable (fun y : Space => g (x - y)) volume :=
    hg.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure Space) x)
  have hF (s : ℝ) : AEStronglyMeasurable (F s) volume :=
    (continuous_kernel s).aestronglyMeasurable.smul hs
  have hFd : AEStronglyMeasurable (F' t) volume :=
    ((Gaussian.timeKernel_continuous (4 * t)).const_mul 4).aestronglyMeasurable.smul hs
  have hB : Integrable B :=
    ((Gaussian.timeEnvelope_integrable (by positivity : 0 < 4 * t)).const_mul 4).mul_const M
  have hFi : Integrable (F t) := by
    refine ((kernel_integrable ht).mul_const M).mono' (hF t) (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg ht y)]
    exact mul_le_mul_of_nonneg_left (hM _) (kernel_nonneg ht y)
  have hbound (y : Space) (s : ℝ) (hs' : s ∈ Ioo (t / 2) (2 * t)) : ‖F' s y‖ ≤ B y := by
    have he : ‖timeDerivativeKernel s y‖ ≤ 4 * Gaussian.timeEnvelope (4 * t) y := by
      have hr := Gaussian.timeKernel_local_bound (t := 4 * t) (by positivity) (4 * s)
        (show 4 * s ∈ Ioo ((4 * t) / 2) (2 * (4 * t)) by
          constructor <;> linarith [hs'.1, hs'.2]) y
      simpa only [timeDerivativeKernel, norm_mul, Real.norm_ofNat] using
        mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 4 by norm_num)
    exact (norm_smul _ _).le.trans (mul_le_mul he (hM _) (norm_nonneg _)
      ((norm_nonneg _).trans he))
  have hdiff (y : Space) (s : ℝ) (hs' : s ∈ Ioo (t / 2) (2 * t)) :
      HasDerivAt (fun r => F r y) (F' s y) s :=
    (kernel_hasDerivAt_timeDerivativeKernel (by linarith [hs'.1] : 0 < s) y).smul_const
      (g (x - y))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B)
    (Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < 2 * t))
    (Eventually.of_forall hF) hFi hFd
    (Eventually.of_forall hbound) hB (Eventually.of_forall hdiff)
  exact hd.2

theorem continuousOn_average_time_of_bound {g : Space → E} (hg : AEStronglyMeasurable g volume)
    {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (x : Space) :
    ContinuousOn (fun s : ℝ => average s g x) (Ioi 0) := fun _ ht =>
  (hasDerivAt_average_time_of_bound hg hM ht x).continuousAt.continuousWithinAt

/-! ### The Laplacian, kernel side and data side -/

/-- `D²(kconv)` applied to `(v, w)` is the integral of `D²K(x-y)(v, w) • g(y)`. -/
theorem iteratedFDeriv_two_average_apply {f : Space → E} (hf : HeatAdmissible f) {t : ℝ}
    (ht : 0 < t) (x v w : Space) :
    iteratedFDeriv ℝ 2 (average t f) x ![v, w] =
      ∫ y : Space, (fderiv ℝ (fderiv ℝ (kernel t)) (x - y) v w) • f y := by
  obtain ⟨m, hm⟩ := hf.integrable_norm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hK := decayKernel_gaussKernel (m := (m : ℝ)) ht hm0
  rw [iteratedFDeriv_two_apply, average_eq_kconv]
  exact fderiv_fderiv_kconv_apply _ hm0 hK hf.1 hm x v w

/-- `fderiv (y ↦ DK(y) e) z e = D²K(z)(e, e)` for `C²` kernels. -/
theorem laplacian_eq_sum_fderiv_fderiv {K : Space → ℝ} (hK : ContDiff ℝ 2 K) (z : Space) :
    laplacian K z = ∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ K) z (coordinateVector i) (coordinateVector i) := by
  simp only [laplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ K) z :=
    (hK.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply]

/-- **Kernel side.** `∫ ΔG_t(y) • f(x - y) dy = Σ_i D²(e^{tΔ}f)(x)(e_i, e_i)` for admissible `f`. -/
theorem integral_laplacian_kernel_eq {f : Space → E} (hf : HeatAdmissible f) {t : ℝ}
    (ht : 0 < t) (x : Space) :
    ∫ y : Space, laplacian (kernel t) y • f (x - y) = vlap (average t f) x := by
  have hK2 : ContDiff ℝ 2 (kernel t) := by
    simpa using contDiff_infty.mp (decayKernel_gaussKernel (m := 0) ht le_rfl).smooth 2
  simp only [vlap]
  simp_rw [iteratedFDeriv_two_average_apply hf ht x]
  rw [← integral_finset_sum]
  · rw [← integral_sub_left_eq_self (fun y => laplacian (kernel t) y • f (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel, laplacian_eq_sum_fderiv_fderiv hK2, Finset.sum_smul]
  · intro i _
    obtain ⟨m, hm⟩ := hf.integrable_norm
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hK := (decayKernel_gaussKernel (m := (m : ℝ)) ht hm0).fderiv.fderiv
    obtain ⟨C, hC⟩ := hK.norm_le
    set Ki : Space → ℝ := fun z =>
      fderiv ℝ (fderiv ℝ (kernel t)) z (coordinateVector i) (coordinateVector i) with hKi
    have hKic : Continuous Ki :=
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).continuous.comp
        ((ContinuousLinearMap.apply ℝ _ (coordinateVector i)).continuous.comp
          hK.smooth.continuous))
    have hKib : ∀ z, ‖Ki z‖ ≤ C * (1 + ‖z‖) ^ (-(m : ℝ)) := by
      intro z
      refine le_trans ?_ (hC z)
      calc ‖Ki z‖ ≤ ‖fderiv ℝ (fderiv ℝ (kernel t)) z (coordinateVector i)‖ *
            ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ (kernel t)) z‖ * ‖coordinateVector i‖ *
            ‖coordinateVector i‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (fderiv ℝ (kernel t)) z‖ := by rw [norm_coordinateVector]; ring
    have hi := integrable_kconv_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hm0 hKic hKib hf.1 hm x
    simpa only [ContinuousLinearMap.lsmul_apply, hKi] using hi

/-! ### The heat equation for `C²_b` data -/

/-- `D²u ↦ Δu` passes through the heat integral (data side). -/
theorem vlap_average {θ : ℝ} (hθ : 0 < θ) {u : Space → E} (hu : ContDiff ℝ 2 u) {M : ℝ}
    (hb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ M) (x : Space) :
    vlap (average θ u) x = average θ (vlap u) x := by
  have hD2 := iteratedFDeriv_average hθ hu hb 2 le_rfl
  have hc2 : Continuous (iteratedFDeriv ℝ 2 u) := hu.continuous_iteratedFDeriv le_rfl
  have hint := integrable_average_of_bound hθ hc2 (hb 2 le_rfl) x
  simp only [vlap, hD2]
  have hcomp : ∀ i : Fin 3, average θ (iteratedFDeriv ℝ 2 u) x
      ![coordinateVector i, coordinateVector i] =
      average θ (fun y => iteratedFDeriv ℝ 2 u y ![coordinateVector i, coordinateVector i]) x := by
    intro i
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) E
        ![coordinateVector i, coordinateVector i]
    have h := L.integral_comp_comm hint
    simp only [average]
    simpa [L] using h.symm
  simp_rw [hcomp]
  simp only [average]
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [vlap, Finset.smul_sum]
  · intro i _
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) E →L[ℝ] E :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) E
        ![coordinateVector i, coordinateVector i]
    simpa [L] using L.integrable_comp hint

/-- **The heat equation** for `C²_b` data: `∂_t e^{tΔ}u(x) = e^{tΔ}(Δu)(x)`, `t > 0`. -/
theorem hasDerivAt_average_time {u : Space → E} (hu : ContDiff ℝ 2 u) {M : ℝ}
    (hb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ M) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s : ℝ => average s u x) (average t (vlap u) x) t := by
  have hb0 : ∀ y, ‖u y‖ ≤ M := fun y => by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by norm_num) y
  have hcont : Continuous u := hu.continuous
  have hadm : HeatAdmissible u := HeatAdmissible.of_memLp (p := ∞) le_top
    (memLp_top_of_bound hcont.aestronglyMeasurable M (Eventually.of_forall hb0))
  have h := hasDerivAt_average_time_of_bound hcont.aestronglyMeasurable hb0 ht x
  have heq : ∫ y : Space, timeDerivativeKernel t y • u (x - y) = average t (vlap u) x := by
    simp_rw [timeDerivativeKernel_eq_laplacian ht]
    rw [integral_laplacian_kernel_eq hadm ht x, vlap_average ht hu hb x]
  rwa [heq] at h

/-! ### The approximate identity -/

theorem integrable_kernel_mul_norm {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : Space => kernel θ y * ‖y‖) := by
  refine (integrable_kernel_mul_weight hθ zero_le_one).mono'
    ((continuous_kernel θ).mul continuous_norm).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (kernel_nonneg hθ y) (norm_nonneg y)), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left (by linarith) (kernel_nonneg hθ y)

/-- `∫ G_ε(y)|y| dy = √ε ∫ G_1(z)|z| dz` (scaling `y = √ε z`). -/
theorem integral_kernel_mul_norm {ε : ℝ} (hε : 0 < ε) :
    ∫ y : Space, kernel ε y * ‖y‖ = Real.sqrt ε * ∫ z : Space, kernel 1 z * ‖z‖ := by
  set R := Real.sqrt ε with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hε
  have hRε : R ^ 2 * 1 = ε := by rw [mul_one]; exact Real.sq_sqrt hε.le
  set f : Space → ℝ := fun y => kernel ε y * ‖y‖ with hf
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) f R (hR := hR0.le)
  rw [show Module.finrank ℝ Space = 3 by simp [Space]] at hJac
  have hscale : ∀ z : Space, f (R • z) = (R ^ 3)⁻¹ * R * (kernel 1 z * ‖z‖) := by
    intro z
    simp only [hf]
    rw [← Gaussian.gaussKernel_three_eq, ← hRε, Gaussian.gaussKernel_scale hR0 one_pos,
      Real.rpow_neg hR0.le, show ((3 : ℕ) : ℝ) = (3 : ℕ) by rfl, Real.rpow_natCast,
      norm_smul, Real.norm_of_nonneg hR0.le]
    ring
  have h1 : ∫ z : Space, f (R • z) = (R ^ 3)⁻¹ * R * ∫ z : Space, kernel 1 z * ‖z‖ := by
    simp_rw [hscale]; rw [integral_const_mul]
  rw [h1, smul_eq_mul] at hJac
  have hR3 : (R ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hR0.ne')
  have := hJac.symm
  rw [mul_assoc] at this
  exact (mul_left_cancel₀ hR3 this)

/-- **Approximate identity**: `|e^{εΔ}u(x) - u(x)| ≤ M √ε ∫ G_1|z|` when `|Du| ≤ M`. -/
theorem norm_average_sub_le_sqrt {u : Space → E} (hu : ContDiff ℝ 1 u) {M : ℝ}
    (hb0 : ∀ x, ‖u x‖ ≤ M) (hb1 : ∀ x, ‖fderiv ℝ u x‖ ≤ M) {ε : ℝ} (hε : 0 < ε) (x : Space) :
    ‖average ε u x - u x‖ ≤ M * (Real.sqrt ε * ∫ z : Space, kernel 1 z * ‖z‖) := by
  have hint := integrable_average_of_bound hε hu.continuous hb0 x
  have hrep : average ε u x - u x = ∫ y : Space, kernel ε y • (u (x - y) - u x) := by
    simp only [smul_sub]
    rw [integral_sub hint ((kernel_integrable hε).smul_const (u x)), integral_smul_const,
      integral_kernel hε, one_smul]
    rfl
  rw [hrep, ← integral_kernel_mul_norm hε, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_kernel_mul_norm hε).const_mul M)
    (Eventually.of_forall fun y => ?_)
  have hmv : ‖u (x - y) - u x‖ ≤ M * ‖y‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (f := u)
      (fun z _ => (hu.differentiable one_ne_zero) z) (fun z _ => hb1 z) convex_univ
      (mem_univ x) (mem_univ (x - y))
    simpa [sub_sub_cancel_left, norm_neg] using h
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg hε y)]
  calc kernel ε y * ‖u (x - y) - u x‖ ≤ kernel ε y * (M * ‖y‖) :=
        mul_le_mul_of_nonneg_left hmv (kernel_nonneg hε y)
    _ = M * (kernel ε y * ‖y‖) := by ring

/-! ### The heat FTC -/

/-- **INF04 T7 `average_sub_eq_integral`** (BP4; B0720, B0722). For `u ∈ C²(ℝ³; E)` with
`‖D^k u‖ ≤ M` (`k ≤ 2`) and `θ > 0`: `e^{θΔ}u(x) - u(x) = ∫_0^θ e^{tΔ}(Δu)(x) dt`. -/
theorem average_sub_eq_integral {u : Space → E} (hu : ContDiff ℝ 2 u) {M : ℝ}
    (hb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ M) {θ : ℝ} (hθ : 0 < θ) (x : Space) :
    average θ u x - u x = ∫ t in (0)..θ, average t (vlap u) x := by
  have hb0 : ∀ y, ‖u y‖ ≤ M := fun y => by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by norm_num) y
  have hb1 : ∀ y, ‖fderiv ℝ u y‖ ≤ M := fun y => by
    simpa only [norm_iteratedFDeriv_one] using hb 1 (by norm_num) y
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hb0 0)
  have hvc : Continuous (vlap u) := by
    unfold vlap
    exact continuous_finset_sum _ fun i _ =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) E
        ![coordinateVector i, coordinateVector i]).continuous.comp
        (hu.continuous_iteratedFDeriv le_rfl)
  have hvb : ∀ y, ‖vlap u y‖ ≤ 3 * M := norm_vlap_le (hb 2 le_rfl)
  set f : ℝ → E := fun t => average t (vlap u) x with hf
  have hfc : ContinuousOn f (Ioi 0) :=
    continuousOn_average_time_of_bound hvc.aestronglyMeasurable hvb x
  have hfb : ∀ t, 0 < t → ‖f t‖ ≤ 3 * M := fun t ht => norm_average_le_of_bound ht hvb x
  have hfi : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine ⟨(hfc.mono fun t ht => lt_of_le_of_lt ha ht.1).aestronglyMeasurable measurableSet_Ioc,
      ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := 3 * M) measure_Ioc_lt_top ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hfb t (lt_of_le_of_lt ha ht.1)
  -- FTC on `[ε, θ]`
  have hftc : ∀ ε, 0 < ε → ε ≤ θ →
      average θ u x - average ε u x = ∫ t in ε..θ, f t := by
    intro ε hε hεθ
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => average s u x)
      (fun t ht => ?_)
      (hfi ε θ hε.le hεθ)).symm
    have ht' : 0 < t := lt_of_lt_of_le hε (by rw [uIcc_of_le hεθ] at ht; exact ht.1)
    exact hasDerivAt_average_time hu hb ht' x
  -- the error at `ε` is `O(√ε) + O(ε)`
  set c := ∫ z : Space, kernel 1 z * ‖z‖ with hc
  have hc0 : 0 ≤ c := integral_nonneg fun z => mul_nonneg (kernel_nonneg one_pos z) (norm_nonneg z)
  set D := ‖(average θ u x - u x) - ∫ t in (0)..θ, f t‖ with hD
  have hbound : ∀ ε, 0 < ε → ε ≤ θ → D ≤ M * (Real.sqrt ε * c) + 3 * M * ε := by
    intro ε hε hεθ
    have hsplit : ∫ t in (0)..θ, f t = (∫ t in (0)..ε, f t) + ∫ t in ε..θ, f t :=
      (intervalIntegral.integral_add_adjacent_intervals (hfi 0 ε le_rfl hε.le)
        (hfi ε θ hε.le hεθ)).symm
    have hsmall : ‖∫ t in (0)..ε, f t‖ ≤ 3 * M * ε := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε)
        (C := 3 * M) (f := f) (fun t ht => by
          rw [uIoc_of_le hε.le] at ht; exact hfb t ht.1)
      simpa [abs_of_pos hε] using h
    have heq : (average θ u x - u x) - ∫ t in (0)..θ, f t =
        (average ε u x - u x) - ∫ t in (0)..ε, f t := by
      rw [hsplit, ← hftc ε hε hεθ]; abel
    rw [hD, heq]
    refine (norm_sub_le _ _).trans ?_
    exact add_le_add (norm_average_sub_le_sqrt (hu.of_le (by norm_num)) hb0 hb1 hε x) hsmall
  have hlim : Tendsto (fun ε => M * (Real.sqrt ε * c) + 3 * M * ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => M * (Real.sqrt ε * c) + 3 * M * ε) (𝓝 0)
        (𝓝 (M * (Real.sqrt 0 * c) + 3 * M * 0)) :=
      ((continuous_const.mul ((Real.continuous_sqrt).mul continuous_const)).add
        (continuous_const.mul continuous_id)).tendsto 0
    simp only [Real.sqrt_zero, zero_mul, mul_zero, add_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D ≤ M * (Real.sqrt ε * c) + 3 * M * ε := by
    filter_upwards [Ioo_mem_nhdsGT hθ] with ε hε
    exact hbound ε hε.1 hε.2.le
  have hD0 : D ≤ 0 := ge_of_tendsto hlim hev
  have hD' : D = 0 := le_antisymm hD0 (norm_nonneg _)
  rw [hD, norm_eq_zero, sub_eq_zero] at hD'
  exact hD'

end UnforcedLeray.Heat
