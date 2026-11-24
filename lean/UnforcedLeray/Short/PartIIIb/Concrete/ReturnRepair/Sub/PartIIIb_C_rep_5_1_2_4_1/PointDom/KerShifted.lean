import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4.GradKHeat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4.GradKEuler
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4.KernelPartialHeat

/-!
# `pdKerShifted` (`PartIII-b:C/rep/5/1/2/4/1/2/4`; source 4198-4201, 3600-3610, 3708-3709)

`PDKerShifted` from the heat equation for the partial kernels (`kernelPartialHeat`, via
`gradKHeat_of_partial`) and the parabolic homogeneity `gradKEuler`, through `pdKerShifted_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdKerShifted : PDKerShifted :=
  pdKerShifted_of (gradKHeat_of_partial kernelPartialHeat) gradKEuler

end UnforcedLeray.Short.PartIIIb.Concrete
