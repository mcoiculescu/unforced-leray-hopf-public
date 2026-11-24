import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3.Cont

/-!
# `KcGradRep` (leaf A of `PartIII-b:C/flatset/col/4/3`), assembly from continuity

Source of record `the November 2 reference manuscript` 3426-3430.
The joint measurable representative of the gradient path `s ↦ (kcGQ (ξ s), kcGE (ξ s))` is obtained
from the two continuity statements `Continuous (fun ξ => kcGQ ξ)` and
`Continuous (fun ξ => kcGE ξ)` on `Xmc c m`, by `Infra.JointMeasurableRep` applied to each factor
on `Ioi 0` and pairing.  The continuity of the two gradient maps is the remaining input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `KcGradRep` from the continuity of the two gradient maps in `ξ`. -/
theorem kcGradRep_of_continuous {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (hQ : Continuous (fun ξ : Xmc c m => kcGQ ξ))
    (hE : Continuous (fun ξ : Xmc c m => kcGE ξ))
    (ξ : ℝ → Xmc c m) (hξ : ContinuousOn ξ (Ioi 0)) :
    ∃ G0 : ℝ × (ℝ × ℝ) → Merid × Merid, Measurable G0 ∧
      ∀ s : ℝ, 0 < s →
        (fun x => (G0 (s, x)).1) =ᵐ[volume.restrict (B0579.cell c)]
            (kcGQ (ξ s) : ℝ × ℝ → Merid) ∧
          (fun x => (G0 (s, x)).2) =ᵐ[volume.restrict (B0579.cell c)]
            (kcGE (ξ s) : ℝ × ℝ → Merid) := by
  have hcQ : ContinuousOn (fun t => kcGQ (ξ t)) (Ioi 0) := hQ.comp_continuousOn hξ
  have hcE : ContinuousOn (fun t => kcGE (ξ t)) (Ioi 0) := hE.comp_continuousOn hξ
  obtain ⟨F1, hF1m, hF1⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := B0581.cellVol c) (f := fun t => kcGQ (ξ t)) (s := Ioi 0) measurableSet_Ioi hcQ
  obtain ⟨F2, hF2m, hF2⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := B0581.cellVol c) (f := fun t => kcGE (ξ t)) (s := Ioi 0) measurableSet_Ioi hcE
  exact ⟨fun p => (F1 p, F2 p), hF1m.measurable.prodMk hF2m.measurable,
    fun s hs => ⟨hF1 s hs, hF2 s hs⟩⟩

/-- **Leaf A** (source 3426-3430). -/
theorem kcGradRep : KcGradRep := by
  intro c m _ _ ξ hξ _
  exact kcGradRep_of_continuous continuous_kcGQ continuous_kcGE ξ hξ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
