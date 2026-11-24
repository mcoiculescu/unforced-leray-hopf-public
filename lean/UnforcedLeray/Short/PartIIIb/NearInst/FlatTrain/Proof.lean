import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Bridge
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Measurable
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Fluct
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.MeanVel
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.MeanDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Mean

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **Flat train multiplier bound** (source 2714-2729, 270-288, 2040): assembly of the BUC train
bound from the fluctuation, mean-velocity and mean-derivative leaves. -/
theorem flatTrainMultBound_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : FlatTrainMultBound :=
  flatTrainMultBound_iff_buc.mpr
    (flatTrainMultBoundBUC_of trainMerMeasurable (flatFluctBound_of hF)
      (flatMeanBound_of (meanVelNorm_of hE) (meanStreamDerivBound_of hM hE)))

end UnforcedLeray.Short.PartIIIb.NearInst
