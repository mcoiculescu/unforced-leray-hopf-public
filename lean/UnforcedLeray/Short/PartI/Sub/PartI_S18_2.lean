import UnforcedLeray.Short.PartI.Sub.PartI_S18

/-!
# `PartI:S18/2` decomposed: `dilX0_dualCont`

Source `the November 2 reference manuscript`
lines 946-953 ("their dilates are norm continuous by dominated convergence").
Reduction by Riesz: `ℓ ∘ J_{1/a} = ⟨J_{1/a}^* v, ·⟩`, so the dual-norm continuity follows from the
strong continuity of the adjoint family on the Hilbert space `X0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **Leaf (strong continuity of the adjoint dilations)** (source 946-953): for `v ∈ X0`,
`a ↦ (J_{1/a})^* v` is continuous `(0,∞) → X0` (Hilbert adjoint on the closed subspace `X0`). -/
def DilX0AdjStrongCont : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) (v : Planar.X0 hM),
    Continuous (fun a : Set.Ioi (0 : ℝ) =>
      ContinuousLinearMap.adjoint (Planar.dilX0 hM (inv_pos.2 a.2) : Planar.X0 hM →L[ℂ] Planar.X0 hM) v)

theorem dilX0_dualCont_of (h : DilX0AdjStrongCont) : DilX0DualCont := by
  intro M hM ℓ
  set v : Planar.X0 hM := (InnerProductSpace.toDual ℂ (Planar.X0 hM)).symm ℓ with hv
  have hℓ : ∀ w, ℓ w = inner ℂ v w := fun w => by
    have := InnerProductSpace.toDual_apply_apply (𝕜 := ℂ) (x := v) (y := w)
    rw [hv, LinearIsometryEquiv.apply_symm_apply] at *
    simpa using (by simp [hv] : ℓ w = (InnerProductSpace.toDual ℂ (Planar.X0 hM) v) w)
  have key : ∀ a : Set.Ioi (0 : ℝ),
      ℓ.comp (Planar.dilX0 hM (inv_pos.2 a.2) : Planar.X0 hM →L[ℂ] Planar.X0 hM) =
        innerSL ℂ (ContinuousLinearMap.adjoint
          (Planar.dilX0 hM (inv_pos.2 a.2) : Planar.X0 hM →L[ℂ] Planar.X0 hM) v) := by
    intro a
    ext1 w
    simp [hℓ, ContinuousLinearMap.adjoint_inner_left]
  simp_rw [key]
  exact (innerSL ℂ).continuous.comp (h M hM v)

end UnforcedLeray.Short.PartI
