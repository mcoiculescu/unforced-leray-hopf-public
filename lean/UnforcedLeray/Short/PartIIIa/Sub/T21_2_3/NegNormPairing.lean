import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3_5.WeakCellMeas

/-!
# Part III-a, task `PartIII-a:T21/2/3/5` (`NegNormPairing`): the target theorem

Source of record: `the November 2 reference manuscript`, lines 2823-2826.
`negNormPairing` is `negNormPairing_of` applied to the measurability input `weakCellMeas`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- The `negNorm` pairing bound (SP 2823-2826). -/
theorem negNormPairing : NegNormPairing := by
  exact negNormPairing_of weakCellMeas

end UnforcedLeray.Short.IIIa
