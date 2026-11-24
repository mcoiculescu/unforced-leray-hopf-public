import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth.Theta0
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth.Theta1

/-!
Task `PartII-b:G4/3/6/1/4`.  `VcSmooth` from the two lattice-sum smoothness leaves
(`thetaSmooth0_proof` in `VcSmooth/JointDecay.lean`, `thetaSmooth1_proof` in
`VcSmooth/PeriodizeParam.lean`) via `vcSmooth_of_theta` (`Sub/PartII-b_G4_3_6_1_4.lean`, SP 2205).
-/

namespace UnforcedLeray.Short.IIb

theorem vcSmooth_proof : UnforcedLeray.Short.IIb.VcSmooth :=
  vcSmooth_of_theta thetaSmooth0_proof thetaSmooth1_proof

end UnforcedLeray.Short.IIb
