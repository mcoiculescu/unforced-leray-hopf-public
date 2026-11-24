import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Green.Smooth
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Green.Inner
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Green.Outer
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Green.ODE
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Sector.Smooth
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Sector.Lap
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Sector.Origin
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Sector.OuterDecay

namespace UnforcedLeray.Short.PartI

theorem secStreamPsi : UnforcedLeray.Short.PartI.SecStreamPsi :=
  secStreamPsi_of secGreenSmooth_proof secGreenInner_proof secGreenOuter_proof
    secGreenODE_proof secSectorSmooth_proof secSectorLap_proof secOrigin_proof
    secOuterDecay_proof

end UnforcedLeray.Short.PartI
