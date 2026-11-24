import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutMeas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.RealTestApprox
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest

/-!
# `DensityBox` (`PartIII-b:C/near/masked/18/3`, source 1675, 1688-1689, 3916-3921)

`DensityBox` is assembled from the four leaves by `densityBox_of` (`Sub3.lean`):
`fullOutMeas` (`Proofs/DB/FullOutMeas.lean`), `fullOutLip` (`Proofs/DB/FullOutLip.lean`),
`realTestApprox` (`Proofs/DB/RealTestApprox.lean`) and the root-namespace theorem `liftFullOutTest`
(`Proofs/DB/LiftFullOutTest.lean`).
-/

set_option autoImplicit false

theorem densityBox :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.DensityBox :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.densityBox_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.fullOutMeas
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.fullOutLip
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.realTestApprox
    liftFullOutTest

#print axioms densityBox
