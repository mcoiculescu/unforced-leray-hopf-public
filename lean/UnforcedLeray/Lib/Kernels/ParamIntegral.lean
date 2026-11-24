import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Iterated derivatives of parametric integrals (helper for INF22 K1)

Helper module of `Lib/Kernels.lean`. Mathlib has only the first-order rule
`hasFDerivAt_integral_of_dominated_of_fderiv_le`; this module iterates it (scoping note
`INF22-INF27-Kernels.md`, §6 risk 1): if every `F a` is smooth, all iterated derivatives are
measurable in the parameter and locally dominated by integrable functions on an open set `U`,
then on `U` the integral `x ↦ ∫ F a x ∂μ` is smooth and its iterated derivatives are the
integrals of the iterated derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Kernels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Local domination of all iterated derivatives of a family `F a` on the set `U`. -/
def LocDominated (μ : Measure α) (F : α → E → ℝ) (U : Set E) : Prop :=
  ∀ n : ℕ, ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ b : α → ℝ, Integrable b μ ∧
    ∀ᵐ a ∂μ, ∀ y ∈ s, ‖iteratedFDeriv ℝ n (F a) y‖ ≤ b a

theorem LocDominated.integrable {F : α → E → ℝ} {U : Set E} (hdom : LocDominated μ F U)
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    Integrable (fun a => iteratedFDeriv ℝ n (F a) x) μ := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom n x hx
  refine Integrable.mono' hb (hmeas n x) ?_
  filter_upwards [hbound] with a ha using ha x (mem_of_mem_nhds hs)

theorem LocDominated.integrable_apply {F : α → E → ℝ} {U : Set E} (hdom : LocDominated μ F U)
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    {x : E} (hx : x ∈ U) :
    Integrable (fun a => F a x) μ := by
  have h := hdom.integrable hmeas 0 hx
  have h' := (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    |>.integrable_comp h
  refine h'.congr (Eventually.of_forall fun a => ?_)
  simp [iteratedFDeriv_zero_eq_comp]

private theorem fderiv_iteratedFDeriv_meas {F : α → E → ℝ}
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) (x : E) :
    AEStronglyMeasurable (fun a => fderiv ℝ (iteratedFDeriv ℝ n (F a)) x) μ := by
  have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).continuous
    |>.comp_aestronglyMeasurable (hmeas (n + 1) x)
  refine h.congr (Eventually.of_forall fun a => ?_)
  simp only [Function.comp_apply, fderiv_iteratedFDeriv]

/-- One differentiation under the integral sign, at the level of the `n`-th derivative. -/
theorem hasFDerivAt_integral_iteratedFDeriv {F : α → E → ℝ} {U : Set E}
    (hsmooth : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (F a))
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ)
      (∫ a, fderiv ℝ (iteratedFDeriv ℝ n (F a)) x ∂μ) x := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom (n + 1) x hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b) hs
  · exact Eventually.of_forall (fun y => hmeas n y)
  · exact hdom.integrable hmeas n hx
  · exact fderiv_iteratedFDeriv_meas hmeas n x
  · filter_upwards [hbound] with a ha y hy
    rw [norm_fderiv_iteratedFDeriv]
    exact ha y hy
  · exact hb
  · filter_upwards [hsmooth] with a ha y _
    exact ((ha.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) y).hasFDerivAt

/-- Iterated differentiation under the integral sign. -/
theorem iteratedFDeriv_integral_eq {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (F a))
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x = ∫ a, iteratedFDeriv ℝ n (F a) x ∂μ := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have : ∀ a, iteratedFDeriv ℝ 0 (F a) x =
        (continuousMultilinearCurryFin0 ℝ E ℝ).symm (F a x) := fun a => by
      rw [iteratedFDeriv_zero_eq_comp]; rfl
    simp_rw [this]
    exact ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ n ih =>
    have hEq : iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) =ᶠ[𝓝 x]
        fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih hy
    have hderiv := hasFDerivAt_integral_iteratedFDeriv hsmooth hmeas hdom n hx
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hEq.fderiv_eq, hderiv.fderiv]
    exact (LinearIsometry.integral_comp_comm (X := α) (μ := μ) (𝕜 := ℝ)
      (E := E →L[ℝ] E [×n]→L[ℝ] ℝ)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm.toLinearIsometry
      _).symm

/-- Differentiability of the iterated derivatives of the parametric integral on `U`. -/
theorem differentiableAt_iteratedFDeriv_integral {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (F a))
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ)) x := by
  have hEq : iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) =ᶠ[𝓝 x]
      fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ := by
    filter_upwards [hU.mem_nhds hx] with y hy using
      iteratedFDeriv_integral_eq hU hsmooth hmeas hdom n hy
  exact (hasFDerivAt_integral_iteratedFDeriv hsmooth hmeas hdom n hx).differentiableAt
    |>.congr_of_eventuallyEq hEq

/-- Smoothness of the parametric integral on `U`. -/
theorem contDiffOn_integral {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (F a))
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
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
theorem norm_iteratedFDeriv_integral_le {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiff ℝ ∞ (F a))
    (hmeas : ∀ (n : ℕ) (x : E), AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDominated μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
      ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  rw [iteratedFDeriv_integral_eq hU hsmooth hmeas hdom n hx]
  exact norm_integral_le_integral_norm _

end UnforcedLeray.Kernels
