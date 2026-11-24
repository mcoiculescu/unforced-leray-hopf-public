import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Of
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollWeakDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakLeibniz
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StAdjComm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StCellIbp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StReynolds
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StVelWords
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StMolMoment
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StFriedPointwise

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: `StaticMollEnergy` from the leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071,
3044-3050.  The six `Static` leaves, the shared leaves and `ktWeakLeibniz` are supplied by their
theorem modules; the statement is `staticMollEnergy_of_leaves` with those leaves plugged in.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`StaticMollEnergy` from the leaves** (SP 3060-3071), with every leaf discharged. -/
theorem staticMollEnergy (m : ℝ) : UnforcedLeray.Short.IIIa.StaticMollEnergy m :=
  staticMollEnergy_of_leaves m cellMollSmooth cellMollBound cellMollWeakDeriv cellConvDeriv
    cellConvBound cellPeriodicLocInt ktWeakLeibniz stAdjComm stCellIbp stReynolds stVelWords
    stMolMoment stFriedPointwise

end UnforcedLeray.Short.IIIa
