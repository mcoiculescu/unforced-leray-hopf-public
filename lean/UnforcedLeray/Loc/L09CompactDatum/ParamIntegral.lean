import UnforcedLeray.Lib.Kernels.GaussDeriv
import UnforcedLeray.Analysis.Heat.Averaging

/-!
# L9 helper: iterated differentiation under the integral sign, vector-valued

Helper of `Loc/L09CompactDatum.lean` (step L9 `CompactDatumStep`, `paper/main.tex`
lines 430–461, blueprint units B0717–B0720).


(real-valued integrands) copied with the codomain `ℝ` replaced by a complete normed space
`G`; the proofs are unchanged up to that replacement.

The second part applies it to the heat average `Heat.average t f x = ∫ G_t(y) f(x-y) dy`
of a smooth field whose derivatives of every order are bounded: the average is smooth and
each of its derivatives obeys the bound of the corresponding derivative of `f`
(the kernel is nonnegative with integral `1`). This is the Gaussian bound used for
`loc:eq:heat-correction` (line 457).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Local domination of all iterated derivatives of a family `F a` on the set `U`. -/
def LocDominated (μ : Measure α) (F : α → E → G) (U : Set E) : Prop :=
  ∀ n : ℕ, ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ b : α → ℝ, Integrable b μ ∧
    ∀ᵐ a ∂μ, ∀ y ∈ s, ‖iteratedFDeriv ℝ n (F a) y‖ ≤ b a

theorem LocDominated.integrable {F : α → E → G} {U : Set E} (hdom : LocDominated μ F U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    Integrable (fun a => iteratedFDeriv ℝ n (F a) x) μ := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom n x hx
  refine Integrable.mono' hb (hmeas n x hx) ?_
  filter_upwards [hbound] with a ha using ha x (mem_of_mem_nhds hs)

private theorem fderiv_iteratedFDeriv_meas {F : α → E → G} {U : Set E}
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    AEStronglyMeasurable (fun a => fderiv ℝ (iteratedFDeriv ℝ n (F a)) x) μ := by
  have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).continuous
    |>.comp_aestronglyMeasurable (hmeas (n + 1) x hx)
  refine h.congr (Eventually.of_forall fun a => ?_)
  simp only [Function.comp_apply, fderiv_iteratedFDeriv]

private theorem hasFDerivAt_iteratedFDeriv_of_contDiffOn {f : E → G} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) {y : E} (hy : y ∈ U) :
    HasFDerivAt (iteratedFDeriv ℝ n f) (fderiv ℝ (iteratedFDeriv ℝ n f) y) y := by
  have h1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) y :=
    (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := 1) (i := n)
      (by exact_mod_cast le_top)
  exact (h1.differentiableAt one_ne_zero).hasFDerivAt

/-- One differentiation under the integral sign, at the level of the `n`-th derivative. -/
theorem hasFDerivAt_integral_iteratedFDeriv {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ)
      (∫ a, fderiv ℝ (iteratedFDeriv ℝ n (F a)) x ∂μ) x := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom (n + 1) x hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b)
    (inter_mem hs (hU.mem_nhds hx))
  · filter_upwards [hU.mem_nhds hx] with y hy using hmeas n y hy
  · exact hdom.integrable hmeas n hx
  · exact fderiv_iteratedFDeriv_meas hmeas n hx
  · filter_upwards [hbound] with a ha y hy
    rw [norm_fderiv_iteratedFDeriv]
    exact ha y hy.1
  · exact hb
  · filter_upwards [hsmooth] with a ha y hy
    exact hasFDerivAt_iteratedFDeriv_of_contDiffOn hU ha n hy.2

/-- Iterated differentiation under the integral sign. -/
theorem iteratedFDeriv_integral_eq {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x = ∫ a, iteratedFDeriv ℝ n (F a) x ∂μ := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have : ∀ a, iteratedFDeriv ℝ 0 (F a) x =
        (continuousMultilinearCurryFin0 ℝ E G).symm (F a x) := fun a => by
      rw [iteratedFDeriv_zero_eq_comp]; rfl
    simp_rw [this]
    exact ((continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ n ih =>
    have hEq : iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) =ᶠ[𝓝 x]
        fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih hy
    have hderiv := hasFDerivAt_integral_iteratedFDeriv hU hsmooth hmeas hdom n hx
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hEq.fderiv_eq, hderiv.fderiv]
    exact (LinearIsometry.integral_comp_comm (X := α) (μ := μ) (𝕜 := ℝ)
      (E := E →L[ℝ] E [×n]→L[ℝ] G)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) G)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).symm.toLinearIsometry
      _).symm

/-- Differentiability of the iterated derivatives of the parametric integral on `U`. -/
theorem differentiableAt_iteratedFDeriv_integral {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ)) x := by
  have hEq : iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) =ᶠ[𝓝 x]
      fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ := by
    filter_upwards [hU.mem_nhds hx] with y hy using
      iteratedFDeriv_integral_eq hU hsmooth hmeas hdom n hy
  exact (hasFDerivAt_integral_iteratedFDeriv hU hsmooth hmeas hdom n hx).differentiableAt
    |>.congr_of_eventuallyEq hEq

/-- Smoothness of the parametric integral on `U`. -/
theorem contDiffOn_integral {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) :
    ContDiffOn ℝ ∞ (fun y => ∫ a, F a y ∂μ) U := by
  rw [contDiffOn_infty]
  intro N
  apply contDiffOn_of_differentiableOn
  intro m _
  have hd : DifferentiableOn ℝ (iteratedFDeriv ℝ m (fun y => ∫ a, F a y ∂μ)) U := fun y hy =>
    (differentiableAt_iteratedFDeriv_integral hU hsmooth hmeas hdom m hy).differentiableWithinAt
  exact hd.congr (iteratedFDerivWithin_of_isOpen m hU)

/-- The norm of an iterated derivative of the integral is at most the integral of the norms. -/
theorem norm_iteratedFDeriv_integral_le {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
      ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  rw [iteratedFDeriv_integral_eq hU hsmooth hmeas hdom n hx]
  exact norm_integral_le_integral_norm _

/-- First-order differentiation under the integral sign on `U`, with the plain derivative. -/
theorem hasFDerivAt_integral_of_locDominated {F : α → E → G} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have h0 : ∀ a y, F a y = (continuousMultilinearCurryFin0 ℝ E G) (iteratedFDeriv ℝ 0 (F a) y) := by
    intro a y; simp
  have h1 : ∀ a y, fderiv ℝ (F a) y =
      (continuousMultilinearCurryFin1 ℝ E G) (iteratedFDeriv ℝ 1 (F a) y) := by
    intro a y; ext v; simp
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom 1 x hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b)
    (inter_mem hs (hU.mem_nhds hx))
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp_rw [h0]
    exact (continuousMultilinearCurryFin0 ℝ E G).continuous.comp_aestronglyMeasurable
      (hmeas 0 y hy)
  · have hi := hdom.integrable hmeas 0 hx
    have := (continuousMultilinearCurryFin0 ℝ E G).toContinuousLinearEquiv.toContinuousLinearMap
      |>.integrable_comp hi
    refine this.congr (Eventually.of_forall fun a => ?_)
    simp
  · simp_rw [h1]
    exact (continuousMultilinearCurryFin1 ℝ E G).continuous.comp_aestronglyMeasurable
      (hmeas 1 x hx)
  · filter_upwards [hbound] with a ha y hy
    rw [← norm_iteratedFDeriv_one]
    exact ha y hy.1
  · exact hb
  · filter_upwards [hsmooth] with a ha y hy
    exact ((ha.contDiffAt (hU.mem_nhds hy.2)).differentiableAt (by simp)).hasFDerivAt

/-! ## Heat averages of fields with bounded derivatives -/

section HeatAverage

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The derivatives of one integrand of the heat average. -/
theorem iteratedFDeriv_heatIntegrand (t : ℝ) (f : Space → V) (n : ℕ) (y x : Space) :
    iteratedFDeriv ℝ n (fun x => Heat.kernel t y • f (x - y)) x =
      Heat.kernel t y • iteratedFDeriv ℝ n f (x - y) := by
  rw [Kernels.iteratedFDeriv_const_smul_left n (fun x => f (x - y)) (Heat.kernel t y) x,
    iteratedFDeriv_comp_sub]

/-- **Heat smoothing of a field with bounded derivatives.** If `f` is smooth and each
derivative is bounded, the heat average at a positive time is smooth, and every derivative
of the average obeys the bound of the corresponding derivative of `f`. -/
theorem heatAverage_smooth_bounds {f : Space → V} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ n : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (Heat.average t f) ∧
      ∀ (n : ℕ) (M : ℝ), (∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ M) →
        ∀ x, ‖iteratedFDeriv ℝ n (Heat.average t f) x‖ ≤ M := by
  set F : Space → Space → V := fun y x => Heat.kernel t y • f (x - y) with hF
  have hav : Heat.average t f = fun x => ∫ y, F y x := rfl
  have hk : Continuous (Heat.kernel t) := (Kernels.heatKernel_smooth t).continuous
  have hsmooth : ∀ᵐ y ∂(volume : Measure Space), ContDiff ℝ ∞ (F y) :=
    Eventually.of_forall fun y => contDiff_const.smul (hf.comp (contDiff_id.sub contDiff_const))
  have hDn : ∀ n : ℕ, Continuous (iteratedFDeriv ℝ n f) := fun n =>
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hmeas : ∀ (n : ℕ), ∀ x ∈ (univ : Set Space),
      AEStronglyMeasurable (fun y => iteratedFDeriv ℝ n (F y) x) volume := by
    intro n x _
    simp_rw [hF, iteratedFDeriv_heatIntegrand]
    exact (hk.smul ((hDn n).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hsmooth : ∀ᵐ y ∂(volume : Measure Space), ContDiffOn ℝ ∞ (F y) univ :=
    hsmooth.mono fun y hy => hy.contDiffOn
  have hdom : LocDominated volume F univ := by
    intro n x _
    obtain ⟨M, hM⟩ := hb n
    refine ⟨univ, univ_mem, fun y => Heat.kernel t y * M,
      (Heat.kernel_integrable ht).mul_const M, Eventually.of_forall fun y z _ => ?_⟩
    simp only [hF]
    rw [iteratedFDeriv_heatIntegrand, norm_smul, Real.norm_of_nonneg (Heat.kernel_nonneg ht y)]
    exact mul_le_mul_of_nonneg_left (hM _) (Heat.kernel_nonneg ht y)
  refine ⟨?_, ?_⟩
  · rw [hav, ← contDiffOn_univ]
    exact contDiffOn_integral isOpen_univ hsmooth hmeas hdom
  · intro n M hM x
    rw [hav]
    refine (norm_iteratedFDeriv_integral_le isOpen_univ hsmooth hmeas hdom n (mem_univ x)).trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
    have hle : ∀ y, ‖iteratedFDeriv ℝ n (F y) x‖ ≤ Heat.kernel t y * M := by
      intro y
      simp only [hF]
      rw [iteratedFDeriv_heatIntegrand, norm_smul, Real.norm_of_nonneg (Heat.kernel_nonneg ht y)]
      exact mul_le_mul_of_nonneg_left (hM _) (Heat.kernel_nonneg ht y)
    calc ∫ y, ‖iteratedFDeriv ℝ n (F y) x‖ ≤ ∫ y, Heat.kernel t y * M :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
            ((Heat.kernel_integrable ht).mul_const M) (Eventually.of_forall hle)
      _ = M := by rw [integral_mul_const, Heat.integral_kernel ht, one_mul]

end HeatAverage

end UnforcedLeray.L09
