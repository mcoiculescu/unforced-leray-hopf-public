import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2.SchurOne

/-!
# `CartSchur` from `SchurOne` (`PartIII-b:C/near/masked/14/2/3/2`; source 3996-4011)

The Cartesian Hardy/Schur bound `CartSchur` follows from the `λ = 1` Schur bound `SchurOne`
by the scaling argument proved in `cartSchur_of`.
-/

set_option autoImplicit false

noncomputable section

theorem cartSchur : UnforcedLeray.Short.PartIIIb.NearInst.Masked.CartSchur :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.cartSchur_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.schurOne

end
