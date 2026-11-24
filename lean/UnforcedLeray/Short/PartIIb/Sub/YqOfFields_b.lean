import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480.

Apply the proved `PartII-a` lemma `periodicFieldToYq_proof` with `r := q0E`
(`q0E = ENNReal.ofReal (11/4)`, `B0412.q0E`). Its finiteness hypothesis is stated with the
exponent `q0E.toReal`; `(ENNReal.ofReal bgp).toReal = bgp = q0E.toReal`, so `hf` transfers.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412

theorem yqOfFields_exists (P : ℝ) [Fact (0 < P)] (W' : ℝ × Space → CVec3)
    (hm : StronglyMeasurable W')
    (hp : ∀ᵐ τ : ℝ, (fun y => W' (τ + P, y)) =ᵐ[volume] fun y => W' (τ, y))
    (hf : ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y, ‖W' (τ, y)‖ₑ ^ (ENNReal.ofReal bgp).toReal < ⊤) :
    ∃ F : Yq P q0E, UnforcedLeray.Short.PartIIa.Rep.IsRep F W' := by
  have hr : (ENNReal.ofReal bgp).toReal = q0E.toReal := by
    rw [ENNReal.toReal_ofReal (by norm_num [bgp]), B0412.q0E_toReal]
    norm_num [bgp]
  have hf' : ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y, ‖W' (τ, y)‖ₑ ^ q0E.toReal < ⊤ := by
    rw [← hr]
    exact hf
  exact UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof q0E q0E_ne_top P W' hm hp hf'

end UnforcedLeray.Short.IIb
