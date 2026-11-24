import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1.Uniq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1.Exist
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.FreeWeakUniqueness

/-!
# `PartIII-b:C/rep/4/2/org/1/1`: `SepWeakRepresentationThin`

Source `the November 2 reference manuscript` lines 1571, 1580-1583.
Uniqueness comes from the unconditional `freeWeakUniqueness` (PhysLayer), through
`freeWeakUniquenessThin` with `dm > 0` read from `RepairStanding`; existence is
`sepWeakExistenceThin`; both feed `sepWeakRepresentationThin_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepWeakRepresentationThin (dm dp : ℝ) : SepWeakRepresentationThin dm dp := by
  have hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 →
      0 < μ + 1 / 4 → FreeWeakUniqueness c γ ν ε μ :=
    fun c γ ν ε μ hc hν hε hP hμ => freeWeakUniqueness hc hν hε hP hμ
  have hT : FreeWeakUniquenessThin dm dp := by
    intro D hst
    exact freeWeakUniquenessThin hU dm dp hst.dm_pos D hst
  exact sepWeakRepresentationThin_of hT (sepWeakExistenceThin dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
