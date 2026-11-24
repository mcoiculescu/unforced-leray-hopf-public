import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Transport
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.FriedDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.FriedZero

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: `StaticMollEnergy` from the leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071,
3044-3050.  The composition of `staticMollEnergy_of` (`Assembly.lean`), `stTransWord_of`
(`Transport.lean`), `stTransComm_of` (`Comm.lean`), `stFriedJet_of` (`Fried.lean`),
`stFriedDeriv_of` (`FriedDeriv.lean`) and `stFriedZero_of` (`FriedZero.lean`).  The remaining
hypotheses are the six leaves `(1)`-`(6)` of `Defs.lean` (`StAdjComm`, `StCellIbp`, `StReynolds`,
`StVelWords`, `StMolMoment`, `StFriedPointwise`) and the shared leaves `CellMollSmooth`,
`CellMollBound`, `CellMollWeakDeriv`, `CellConvDeriv`, `CellConvBound`, `CellPeriodicLocInt`
(`HkStep/Shared.lean`) and `KTWeakLeibniz` (`HkStep/KT/Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`StaticMollEnergy` from the leaves** (SP 3060-3071). -/
theorem staticMollEnergy_of_leaves (m : ℝ) (hS : CellMollSmooth) (hB : CellMollBound)
    (hW : CellMollWeakDeriv) (hCD : CellConvDeriv) (hCB : CellConvBound)
    (hL : CellPeriodicLocInt) (hKW : KTWeakLeibniz) (hComm : StAdjComm) (hIbp : StCellIbp)
    (hR : StReynolds) (hVW : StVelWords) (hMom : StMolMoment) (hPw : StFriedPointwise) :
    StaticMollEnergy m :=
  staticMollEnergy_of m hS hB hW hCD hComm hIbp
    (stTransWord_of hS hCD hIbp hR (stTransComm_of hComm hVW)
      (stFriedJet_of hCD (stFriedZero_of hCB hMom hPw)
        (stFriedDeriv_of hCD hS hW hL hComm hKW) hVW))

end UnforcedLeray.Short.IIIa
