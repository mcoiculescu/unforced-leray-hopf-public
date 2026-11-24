import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProduct

/-! Compact bounds and explicit slice-chain derivative identities for the test product. -/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private theorem contDiff_realC_bounds : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_piLp_apply (p := 2) (i := i))

/-- A continuous function is norm-bounded on every compact set. -/
theorem exists_norm_bound_on_compact {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] (f : E → F) (hf : Continuous f) {K : Set E}
    (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖f x‖ ≤ C := by
  have hn : Continuous (fun x => ‖f x‖) := continuous_norm.comp hf
  have himage : IsCompact ((fun x => ‖f x‖) '' K) := hK.image hn
  obtain ⟨B, hB⟩ := himage.bddAbove
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- Restricting a smooth spacetime field to a fixed phase differentiates only in the spatial
component of the spacetime direction. -/
theorem fderiv_slice_eq_spatial {Φ : ℝ × Space → CVec3}
    (hΦ : Differentiable ℝ Φ) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => Φ (τ, x)) y v =
      fderiv ℝ Φ (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : Space => (τ, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hΦ (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : Space →L[ℝ] CVec3 => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

/-- Chain rule for the linear real embedding of a spatial background into the complex field. -/
theorem fderiv_realC_background {U : ℝ → SpatialField}
    (hU : IsBoundedBackground U) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => realC (U τ x)) y v =
      fderiv ℝ realC (U τ y) (fderiv ℝ (U τ) y v) := by
  have hC : DifferentiableAt ℝ realC (U τ y) :=
    (contDiff_realC_bounds.differentiable (by simp)) (U τ y)
  have hV := hU.differentiable τ y
  have hcomp := hC.hasFDerivAt.comp y hV.hasFDerivAt
  have h := congrArg (fun A : Space →L[ℝ] CVec3 => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using h

#print axioms exists_norm_bound_on_compact
#print axioms fderiv_slice_eq_spatial
#print axioms fderiv_realC_background

end UnforcedLeray.Cons.C03.Concrete
