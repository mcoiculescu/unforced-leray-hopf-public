import UnforcedLeray.Cons.L2.CanonicalBranch.DysonLimit

/-!
# Adjoint estimates and mild identity for the actual first transport-diffusion family

This downstream leaf records the adjoint-side bounds needed by the compact-Duhamel comparison.
It consumes the sharp estimate already transferred to the actual `Fβ` and the existing concrete
adjoint-Dyson theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.Evolution

/-- The adjoint of the actual first transport-diffusion family has the same sharp energy bound. -/
theorem canonicalTransportDysonFamily_adjoint_sharp_norm_le
    {a b s t δ : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (hβ : ContinuousOn β (Set.Icc a b))
    (hβi : ∀ r u, IntervalIntegrable β volume r u)
    (hβ0 : ∀ r, 0 ≤ β r) (M : ℝ) (hβM : ∀ r, |β r| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (hβδ : ∀ r ∈ Set.Icc a b, β r ≤ δ) (hδ : 0 ≤ δ)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖ContinuousLinearMap.adjoint
        ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s) x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  have h := canonicalTransportDysonFamily_sharp_norm_le lam κ β hβ hβi hβ0 M hβM
    hβsm hβblock hβδ hδ has hst ht x
  have hop : ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    simpa [mul_assoc] using
      (canonicalTransportDysonFamily_sharp_norm_le lam κ β hβ hβi hβ0 M hβM
        hβsm hβblock hβδ hδ has hst ht z)
  calc
    ‖ContinuousLinearMap.adjoint
        ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s) x‖ ≤
        ‖ContinuousLinearMap.adjoint
          ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s)‖ * ‖x‖ :=
      (ContinuousLinearMap.adjoint
        ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s)).le_opNorm x
    _ = ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s‖ * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg x)

/-- Concrete adjoint Duhamel formula for the actual first transport-diffusion evolution. -/
theorem canonicalTransportDysonFamily_adjoint_mild
    {a b s t : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (hβi : ∀ r u, IntervalIntegrable β volume r u)
    (hβ0 : ∀ r, 0 ≤ β r) (M : ℝ) (hβM : ∀ r, |β r| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (y : XG) :
    ContinuousLinearMap.adjoint
        ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s) y =
      ContinuousLinearMap.adjoint ((freeDiffusionFamily (a := a) (b := b) β hβi hβ0 M hβM).U t s) y +
        ∫ r in s..t,
          ContinuousLinearMap.adjoint ((freeDiffusionFamily (a := a) (b := b) β hβi hβ0 M hβM).U r s)
            (ContinuousLinearMap.adjoint
              ((transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock).A r)
              (ContinuousLinearMap.adjoint
                ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t r) y)) := by
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let A : BoundedPert XG a b :=
    transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock
  have hE : E.AdjointContinuous := by
    exact freeDiffusionFamily_adjointContinuous β hβi hβ0 M hβM
  have hA : A.AdjointMeasurable :=
    transportDysonPert_adjointMeasurable UnforcedLeray.B0087.imMulOp lam κ β a b
      hβsm hβblock
  have h := Evolution.adjoint_dyson (F := E) (A := A) hE hA ⟨has, hst, ht⟩ y
  change ContinuousLinearMap.adjoint ((Evolution.dyson E A).U t s) y =
    ContinuousLinearMap.adjoint (E.U t s) y +
      ∫ r in s..t, ContinuousLinearMap.adjoint (E.U r s)
        (ContinuousLinearMap.adjoint (A.A r)
          (ContinuousLinearMap.adjoint ((Evolution.dyson E A).U t r) y))
  exact h

end UnforcedLeray.Cons.G3b
