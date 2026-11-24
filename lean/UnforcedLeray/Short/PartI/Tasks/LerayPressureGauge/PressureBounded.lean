import UnforcedLeray.Short.PartI.Sub.T02_2_3
import UnforcedLeray.Short.PartI.Sub.T02_2_3.OscLinear
import UnforcedLeray.Short.PartI.Sub.T02_2_3.TimeGrad
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressurePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.SourceBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.ModeC2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.ModeLaplace
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.QModeEstimates
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.FourierPointwise
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.QAvgReal
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.MeanBounded
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.GradToGrowth
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.MaxPrincipleLinear
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.TimeAvgSmooth
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.ConvViscBound
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.MomentumIntegrated
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.HmeanTimeIntegral
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.HmeanTimeContinuous
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.RealAvgLimit

/-! Assembly of `PressureBounded` from the compiled leaves (Sub/T02_2.lean, `PressureBounded`). -/

namespace UnforcedLeray.Short.PartI

theorem pressureBounded : PressureBounded :=
  pressureBounded_of pressurePoisson cylPoisSourceBound pbMeanBounded
    (pbOscLinear_of cylPoisModeC2 cylPoisModeLaplace cylPoisQModeEstimates cylPoisFourierPointwise
      cylPoisQAvgReal pbGradToGrowth pbMaxPrincipleLinear)
    pbTimeAvgSmooth
    (pbTimeGrad_of pbConvViscBound pbMomentumIntegrated)
    (pbAvgLimit_of pbHmeanTimeIntegral pbHmeanTimeContinuous pbRealAvgLimit)

end UnforcedLeray.Short.PartI
