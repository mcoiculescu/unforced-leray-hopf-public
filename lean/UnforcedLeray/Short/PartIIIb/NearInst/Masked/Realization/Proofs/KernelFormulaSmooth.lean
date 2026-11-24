import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf5a
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf5b
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf6
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf7

/-!
# `kernelFormulaSmooth : KernelFormulaSmooth`

Assembly of the six leaves `kf2 : KF2pos`, `kf3 : KF3`, `kf5a`, `kf5b`, `kf6`, `kf7` through
`kernelFormulaSmooth_of'` of `Sub2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- **KernelFormulaSmooth** (assembly of the proved leaves `kf2`, `kf3`, `kf5a`, `kf5b`, `kf6`,
`kf7` through `kernelFormulaSmooth_of'`). -/
theorem kernelFormulaSmooth : KernelFormulaSmooth :=
  kernelFormulaSmooth_of' kf2 kf3 kf5a kf5b kf6 kf7

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
