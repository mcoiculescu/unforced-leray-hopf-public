import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest.MemH
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest.KernelIdentity

/-!
# `LiftFullOutTest` (`PartIII-b:C/near/masked/18/3/4`, source 3916-3921, 1675, 1688-1689, 2681-2691)

The conjunction of `FullOutMemH` (`fullOutMemH`, `LiftFullOutTest/MemH.lean`) and
`LiftKernelIdentity` (`liftKernelIdentity`, `LiftFullOutTest/KernelIdentity.lean`) is
`LiftFullOutTest` by `liftFullOutTest_of` (`Sub/PartIII-b_C_near_masked_18_3_4.lean`).
-/

set_option autoImplicit false

theorem liftFullOutTest :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LiftFullOutTest :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.liftFullOutTest_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.fullOutMemH
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.liftKernelIdentity
