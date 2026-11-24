import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Iterated derivatives of parametric integrals when each slice is smooth only on an open set `U`

Variant of `UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le`
(`Lib/Kernels/ParamIntegral.lean`) in which each `F a` is only `C^∞` on the open set `U`, and
measurability is only needed at points of `U`.  Used for the horizontal average of fields that are
smooth only for `s > 0` (source `shorter-proof-2026-11-02.tex` 397-404).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.PO

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Local domination of all iterated derivatives of a family `F a` on the set `U`. -/
def LocDom (μ : Measure α) (F : α → E → ℝ) (U : Set E) : Prop :=
  ∀ n : ℕ, ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ b : α → ℝ, Integrable b μ ∧
    ∀ᵐ a ∂μ, ∀ y ∈ s, ‖iteratedFDeriv ℝ n (F a) y‖ ≤ b a

theorem LocDom.integrable {F : α → E → ℝ} {U : Set E} (hdom : LocDom μ F U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    Integrable (fun a => iteratedFDeriv ℝ n (F a) x) μ := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom n x hx
  refine Integrable.mono' hb (hmeas n x hx) ?_
  filter_upwards [hbound] with a ha using ha x (mem_of_mem_nhds hs)

private theorem fderiv_meas {F : α → E → ℝ} {U : Set E}
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    AEStronglyMeasurable (fun a => fderiv ℝ (iteratedFDeriv ℝ n (F a)) x) μ := by
  have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).continuous
    |>.comp_aestronglyMeasurable (hmeas (n + 1) x hx)
  refine h.congr (Eventually.of_forall fun a => ?_)
  simp only [Function.comp_apply, fderiv_iteratedFDeriv]

theorem hasFDerivAt_int {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDom μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ)
      (∫ a, fderiv ℝ (iteratedFDeriv ℝ n (F a)) x ∂μ) x := by
  obtain ⟨s, hs, b, hb, hbound⟩ := hdom (n + 1) x hx
  have hs' : s ∩ U ∈ 𝓝 x := Filter.inter_mem hs (hU.mem_nhds hx)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b) hs'
  · filter_upwards [hs'] with y hy using hmeas n y hy.2
  · exact hdom.integrable hmeas n hx
  · exact fderiv_meas hmeas n hx
  · filter_upwards [hbound] with a ha y hy
    rw [norm_fderiv_iteratedFDeriv]
    exact ha y hy.1
  · exact hb
  · filter_upwards [hsmooth] with a ha y hy
    have hd := ha.differentiableOn_iteratedFDerivWithin (m := n)
      (by exact_mod_cast WithTop.coe_lt_top _) hU.uniqueDiffOn
    have hd' : DifferentiableAt ℝ (iteratedFDerivWithin ℝ n (F a) U) y :=
      (hd y hy.2).differentiableAt (hU.mem_nhds hy.2)
    have hEq : iteratedFDerivWithin ℝ n (F a) U =ᶠ[𝓝 y] iteratedFDeriv ℝ n (F a) := by
      filter_upwards [hU.mem_nhds hy.2] with z hz using iteratedFDerivWithin_of_isOpen n hU hz
    exact (hd'.congr_of_eventuallyEq hEq.symm).hasFDerivAt

theorem iteratedFDeriv_int_eq {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDom μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
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
    have hderiv := hasFDerivAt_int hU hsmooth hmeas hdom n hx
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hEq.fderiv_eq, hderiv.fderiv]
    exact (LinearIsometry.integral_comp_comm (X := α) (μ := μ) (𝕜 := ℝ)
      (E := E →L[ℝ] E [×n]→L[ℝ] ℝ)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm.toLinearIsometry
      _).symm

theorem differentiableAt_iteratedFDeriv_int {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDom μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ)) x := by
  have hEq : iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) =ᶠ[𝓝 x]
      fun y => ∫ a, iteratedFDeriv ℝ n (F a) y ∂μ := by
    filter_upwards [hU.mem_nhds hx] with y hy using
      iteratedFDeriv_int_eq hU hsmooth hmeas hdom n hy
  exact (hasFDerivAt_int hU hsmooth hmeas hdom n hx).differentiableAt
    |>.congr_of_eventuallyEq hEq

/-- Smoothness of the parametric integral on `U`. -/
theorem contDiffOn_int {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDom μ F U) :
    ContDiffOn ℝ ∞ (fun y => ∫ a, F a y ∂μ) U := by
  rw [contDiffOn_infty]
  intro N
  apply contDiffOn_of_differentiableOn
  intro m _
  have hd : DifferentiableOn ℝ (iteratedFDeriv ℝ m (fun y => ∫ a, F a y ∂μ)) U := fun y hy =>
    (differentiableAt_iteratedFDeriv_int hU hsmooth hmeas hdom m hy).differentiableWithinAt
  exact hd.congr (iteratedFDerivWithin_of_isOpen m hU)

/-- The norm of an iterated derivative of the integral is at most the integral of the norms. -/
theorem norm_iteratedFDeriv_int_le {F : α → E → ℝ} {U : Set E} (hU : IsOpen U)
    (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : LocDom μ F U) (n : ℕ) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
      ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  rw [iteratedFDeriv_int_eq hU hsmooth hmeas hdom n hx]
  exact norm_integral_le_integral_norm _

end UnforcedLeray.Short.PartIIIb.Concrete.PO
