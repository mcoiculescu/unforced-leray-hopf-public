import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1_PhysDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R2_Change
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R3_Chain
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R4_Ident
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R5_Deriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Proof

/-!
# `PartIII-a:T21/2/2/2/2`: Reynolds' cancellation for `E_0` (assembly)

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3062
(`E_0' + β_min E_1 ≤ C_b E_0`). Assembles the leaves `reyChange` (R2, SP 3036-3037), `reyChain`
(R3, SP 2860), `reyPhysDeriv` (R1, from `adjXDiff`), `reyDeriv` (R5) and `reyIdent` (R4/R6)
through `adjE0Reynolds_of` (`Reynolds/Defs`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- **`E_0` Reynolds cancellation** (SP 3060-3062): the adjoint `E_0` satisfies `AdjE0Reynolds m`
for every `m > 8`, from the leaf statements. -/
theorem adjE0Reynolds (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.AdjE0Reynolds m :=
  adjE0Reynolds_of m (reyChange m)
    (reyDeriv m reyChain (reyPhysDeriv m (adjXDiff m)))
    (reyIdent m hm reyChain)

end UnforcedLeray.Short.IIIa.E0
