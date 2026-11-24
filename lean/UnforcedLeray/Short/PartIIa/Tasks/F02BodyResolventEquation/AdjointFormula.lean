import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.HeatSymmetric
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.DilationDual

/-!
# Part II-a, task `PartII-a:F02/3`: the adjoint formula for the free similarity semigroup

Source of record: `the November 2 reference manuscript`, lines 1363-1370.
This file proves the Prop `AdjointFormula` defined in `Sub/F02.lean`:
`⟪u, S_ν(r)h⟫ = ⟪S'_ν(r)u, h⟫`.

Proof. With `a = e^{r/2}` and `σ = ν(e^r - 1)`, the dilation identity `DilationDual` (F02/2)
gives `a·(a³)⁻¹ ∫ ⟪u(a⁻¹ z), Heat.flow h σ z⟫`. Symmetry of the heat flow (F02/1) moves the
flow onto the dilated field `u(a⁻¹ ·)`, and the intertwining `B0418.flow_comp_smul` turns it into
`Heat.flow u (a⁻² σ) (a⁻¹ ·)`. Finally `a·(a³)⁻¹ = e^{-r}`, `a⁻² σ = ν(1 - e^{-r})`, and
`a⁻¹ = e^{-r/2}` match `adjFree`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

/-- **The adjoint formula** (task `PartII-a:F02/3`), proved: the Prop `AdjointFormula`. -/
theorem adjointFormula : AdjointFormula := by
  intro ν r hν hr p q _ hp hq u h hu hh
  have hapos : 0 < Real.exp (r / 2) := Real.exp_pos _
  have hane : Real.exp (r / 2) ≠ 0 := hapos.ne'
  have hExp : Real.exp r = Real.exp (r / 2) * Real.exp (r / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hσ : 0 ≤ ν * (Real.exp r - 1) :=
    mul_nonneg hν (by linarith [Real.one_le_exp hr])
  have hinvpos : 0 < (Real.exp (r / 2))⁻¹ := inv_pos.mpr hapos
  have hconst : Real.exp (r / 2) * (Real.exp (r / 2) ^ 3)⁻¹ = Real.exp (-r) := by
    rw [Real.exp_neg, hExp]; field_simp
  have hsq : (Real.exp (r / 2))⁻¹ ^ 2 * (ν * (Real.exp r - 1)) = ν * (1 - Real.exp (-r)) := by
    rw [Real.exp_neg, hExp]; field_simp
  have hδ : (Real.exp (r / 2))⁻¹ = Real.exp (-r / 2) := by
    rw [← Real.exp_neg, neg_div]
  have hv : MemLp (fun w : Space => u ((Real.exp (r / 2))⁻¹ • w)) p volume :=
    SpatialScaling.memLp_comp_dilation hu hinvpos.ne'
  have hflow : Heat.flow (fun w : Space => u ((Real.exp (r / 2))⁻¹ • w)) (ν * (Real.exp r - 1)) =
      fun x => Heat.flow u ((Real.exp (r / 2))⁻¹ ^ 2 * (ν * (Real.exp r - 1)))
        ((Real.exp (r / 2))⁻¹ • x) :=
    UnforcedLeray.B0418.flow_comp_smul hinvpos u _
  calc ∫ y, inner ℝ (u y) (AncientLocalization.freeEvolution ν r h y)
      = Real.exp (r / 2) * (Real.exp (r / 2) ^ 3)⁻¹ *
          ∫ z, inner ℝ (u ((Real.exp (r / 2))⁻¹ • z)) (Heat.flow h (ν * (Real.exp r - 1)) z) :=
        dilationDual (Real.exp (r / 2)) (Real.exp (r / 2)) hapos u
          (Heat.flow h (ν * (Real.exp r - 1)))
    _ = Real.exp (-r) * ∫ z, inner ℝ
          (Heat.flow (fun w : Space => u ((Real.exp (r / 2))⁻¹ • w)) (ν * (Real.exp r - 1)) z)
          (h z) := by
        rw [hconst]
        congr 1
        exact heatSymmetricLp p q hp hq _ hσ _ h hv hh
    _ = Real.exp (-r) * ∫ z, inner ℝ
          (Heat.flow u (ν * (1 - Real.exp (-r))) (Real.exp (-r / 2) • z)) (h z) := by
        rw [hflow, hsq, hδ]
    _ = ∫ y, inner ℝ (adjFree ν r u y) (h y) := by
        unfold adjFree SpatialScaling.spatialScale
        simp only [real_inner_smul_left, integral_const_mul]

end UnforcedLeray.Short.PartIIa
