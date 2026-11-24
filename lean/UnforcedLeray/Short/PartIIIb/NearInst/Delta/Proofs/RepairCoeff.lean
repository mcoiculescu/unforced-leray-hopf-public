import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# Proof of `repairCoeffBound` (source 2706-2711, 2775)
`√s|v_b| ≤ ρ_b` at every chart point with `s > 0` (`IIIa.repair_coeff_bound`), hence a.e. for
`ageμ`, which is carried by `s > 0`.  Target: `NearInst/Delta/Lemmas.lean`, `RepairCoeffBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

theorem repairCoeffBound : RepairCoeffBound := by
  intro dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν ρb S_in V rb hsplit
  have hP1 := UnforcedLeray.Short.IIIa.period_le_one_of_small hreg hν
  obtain ⟨z, -, -, -, hco⟩ := hsplit.state
  have hρ : 0 ≤ ρb := (abs_nonneg _).trans (hco 0)
  filter_upwards [UnforcedLeray.Short.IIIa.ae_pos_ageμ p.c (-1 / 2)] with pt hpt
  exact UnforcedLeray.Short.IIIa.repair_coeff_bound hP1 hρ hsplit pt hpt

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
