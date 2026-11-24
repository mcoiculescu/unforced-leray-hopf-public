import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollKerProps
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.SmoothCellJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollConvJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollRateJetAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.VelMulMemX
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.VelMulCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.ChiCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollDual
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollTestedAdj
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollRateTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.AdjIntegrandSplit
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.CellIBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.XMulTestInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.EnergyDerivAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.EnergyContAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.XDerivOfTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TestedOfXDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/1`: `MollRateDeriv m` (composition of the leaves)

Source of record: `the November 2 reference manuscript` lines 3060-3071, 3052-3058.
Proof: `mollRateDeriv_of` (`Dyn/Assembly.lean`) applied to the accepted leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mollRateDeriv (m : ℝ) (hm : 8 < m) : MollRateDeriv m :=
  mollRateDeriv_of m hm mollKerProps
    (mollConvJet smoothCellJet cellConvDeriv cellConvBound cellPeriodicLocInt)
    (mollRateJetAbs (mollConvJet smoothCellJet cellConvDeriv cellConvBound cellPeriodicLocInt)
      cellConvDeriv)
    (velMulMemX m) (velMulCont m) (chiCont m)
    (mollDual cellPeriodicLocInt cellConvDeriv)
    kernelBSExists
    (mollTestedAdj m (mollDual cellPeriodicLocInt cellConvDeriv))
    (mollRateTested m (mollDual cellPeriodicLocInt cellConvDeriv) cellIBP
      (adjIntegrandSplit m xMulTestInt (velMulMemX m)) (velMulMemX m) xMulTestInt
      cellConvDeriv cellMollSmooth)
    xDerivOfTested
    (xDerivUpgrade_of xDerivOfTested testedOfXDeriv)
    energyDerivAbs
    (energyContAbs cellConvBound cellConvDeriv cellPeriodicLocInt mollKerProps)

end UnforcedLeray.Short.IIIa
