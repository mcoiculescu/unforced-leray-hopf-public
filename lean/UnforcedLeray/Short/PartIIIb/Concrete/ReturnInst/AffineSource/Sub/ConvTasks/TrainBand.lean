import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.TrainBandSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.TBChartVel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.TBChartRaised
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet

/-!
# `TrainBand` from the Part I hypotheses (`PartIII-b:C/asrc/ra/9/2/2/11`)

Source of record: `the November 2 reference manuscript`, 2419-2423, 2075-2077, 4371.

Composition of `trainBand_of_charts` (`TrainBandSub`) with the Part II-b jet bound
`rawJetBound_of` (from `TrainTransverseTails` and `TrainFixedBand`) and the two chart
comparisons `tbChartVel`, `tbChartRaised`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem trainBand_of_partI (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : TrainBand :=
  trainBand_of_charts (UnforcedLeray.Short.IIb.rawJetBound_of hT hF) tbChartVel tbChartRaised

end UnforcedLeray.Short.PartIIIb.Concrete

end
