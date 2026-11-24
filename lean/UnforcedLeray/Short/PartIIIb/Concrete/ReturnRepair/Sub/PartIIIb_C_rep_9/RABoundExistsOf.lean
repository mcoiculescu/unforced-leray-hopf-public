import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Seq
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound

/-!
# `PartIII-b:C/rep/9/1`: `RABoundExists` from the repair standing, up to the open leaves

Source `the November 2 reference manuscript` 5001-5016, 5022-5079 (Lemma
`ret:physical-affine` with the second line of `ret:general-affine-bounds` along the sequence).

`raBoundExists_of_bg'` (`Concrete/ReturnInst/Background/Seq.lean`) with every hypothesis that is a
field of `SeqData.RepairStanding` or an accepted theorem discharged:

* the fixed choices from the standing: `IsGrowingEigenpair` from `hst.planar.eigenpair`,
  `ω ≠ 0`, `γ > 0`, `σ₀ ∈ (0, 1/4)`, `IsSourceCutoffC χ_f`, `C₀ > 0`, `a_s > 0`, `m₀ > 0`,
  `2m₀ < 3d₋/11` (`m0_ball`), `m_Z > 3/2`;
* the accepted leaves `NearInst.multPinOfLink` (`PartIII-b:C/near/link/2`), `hhatCoefLinear`
  (`C/inst/8`), `faCoefLinear` (`C/inst/6`), `eaCoefLinear` (`C/inst/7`), `eaCoefBound`
  (`C/inst/10`).

The remaining hypotheses are the leaves still in the queue: `IIb.StrongRegularity`
(`PartII-b:S3`), `NearInst.SplitMultBound` (`C/near/4` with `PartIII-a:T23`), `HhatCoefBound`
(`C/inst/11`), `FACoefBound` (`C/inst/9`) and the ten `C/asrc/ra/1-10` leaves.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RABoundExists D dm dp` from the repair standing** (source 5001-5016, 5022-5079), given the
-/
theorem repairStanding_rABoundExists_of (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity) (hSB : NearInst.SplitMultBound)
    (bh : HhatCoefBound D.K.as D.K.χf) (bF : FACoefBound D.K.as D.K.χf)
    (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1) (hCont : IBPContC)
    (hreg : AffineLiftReg D.K.as D.K.χf) (haxi : RAPhysAxi D.K.as D.K.χf)
    (hlin : RALinear D.K.as D.K.χf) (hper : RPerBound D.K.as D.K.χf)
    (hgeo : RAGeoBound D.K.as D.K.χf) (hcv : RAConvBound D.K.as D.K.χf) :
    RABoundExists D dm dp :=
  raBoundExists_of_bg' D dm dp hst.dm_pos hst.omega_ne hst.gamma_pos hst.sigma_pos
    hst.sigma_lt hst.chiF hst.C0_pos hst.as_pos.le hst.m0_pos hst.m0_ball hst.mZ_gt
    hst.planar.eigenpair hSR hSB NearInst.multPinOfLink
    (hhatCoefLinear D.K.as D.K.χf hst.chiF) (faCoefLinear D.K.as D.K.χf hst.chiF)
    (eaCoefLinear D.K.as D.K.χf hst.chiF) bh bF (eaCoefBound D.K.as D.K.χf hst.chiF)
    hAdj hDiv hGrad hCont hreg haxi hlin hper hgeo hcv

end UnforcedLeray.Short.PartIIIb.Concrete
