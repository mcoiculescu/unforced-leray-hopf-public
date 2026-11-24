import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RABoundExistsOf
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.SplitMult
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPAdjointC2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPDivC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPGradC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPContC
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAPhysAxi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RALinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RPerBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAConvBound
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof

/-!
# `PartIII-b:C/rep/9/1`: `RABoundExists` from the repair standing (reduction to `short-bg:strong`)

Source `the November 2 reference manuscript` 5001-5016, 5022-5079 (Lemma
`ret:physical-affine` with the second line of `ret:general-affine-bounds` along the sequence).

STATUS: blocked.  Every leaf of `repairStanding_rABoundExists_of` is discharged below by an
accepted theorem except `IIb.StrongRegularity` (`short-bg:strong`, source 2525-2562): the accepted
`PartII-b:S3` proves only `IIb.strongRegularity_of (hS1 : StrongFirstDerivative)
(hS2 : StrongAllOrders)`; the unconditional version waits on `PartII-b:S1`, `PartII-b:S2` and
`PartII-b:G4` (`affineInletFacts_proof`).  Once `strongRegularity_proof : IIb.StrongRegularity`
exists, the target is `repairStanding_rABoundExists_of_strongRegularity D hst strongRegularity_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RABoundExists D dm dp` from the repair standing and `short-bg:strong`** (source 5001-5016,
5022-5079, 2538-2541): all other leaves of `repairStanding_rABoundExists_of` are the accepted
`NearInst.splitMultBound_of` (with `IIIa.stressSpacesExactSplit`), `hhatCoefBound`, `faCoefBound`
and the affine-source leaves `ibpAdjointC2`, `ibpDivC1`, `ibpGradC1`, `ibpContC`,
`affineLiftReg`, `raPhysAxi`, `raLinear`, `rPerBound`, `raGeoBound`, `raConvBound`. -/
theorem repairStanding_rABoundExists_of_strongRegularity (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) (hSR : UnforcedLeray.Short.IIb.StrongRegularity) :
    RABoundExists D dm dp :=
  repairStanding_rABoundExists_of D hst hSR
    (NearInst.splitMultBound_of UnforcedLeray.Short.IIIa.stressSpacesExactSplit.1)
    (hhatCoefBound _ _ hst.chiF) (faCoefBound _ _ hst.chiF)
    ibpAdjointC2 ibpDivC1 ibpGradC1 ibpContC (affineLiftReg _ _) (raPhysAxi _ _)
    (raLinear _ _) (rPerBound _ _) (raGeoBound _ _) (raConvBound _ _)

/-- **`PartIII-b:C/rep/9/1`**: unconditional `RABoundExists D dm dp` from `D.RepairStanding`
and `strongRegularity_proof` (`PartIII-b:C/rep/9/1/sr`). -/
theorem repairStanding_rABoundExists (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : RABoundExists D dm dp :=
  repairStanding_rABoundExists_of_strongRegularity D hst
    UnforcedLeray.Short.IIb.strongRegularity_proof

end UnforcedLeray.Short.PartIIIb.Concrete
