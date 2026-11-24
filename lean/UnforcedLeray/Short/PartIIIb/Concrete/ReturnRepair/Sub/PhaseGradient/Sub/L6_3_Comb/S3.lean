import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.ParamHasFDeriv1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapInt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KerIntProd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KerFFderiv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KerIntD1_of

/-!
# `sepX0YGrad` (`PartIII-b:C/rep/2/6/3/3`)

Source of record: `the November 2 reference manuscript` lines 3603-3626,
3800-3807, 4171-4200, 5223. The statement `SepX0YGrad` (the `y`-gradient of `X₀ = Re kerInt Kd`
off the old disk) is `sepX0YGrad_of` applied to `sepX0KerInt` and the first `y`-derivative
`kerIntD1_of` of `kerInt` under the integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`sepX0YGrad`** (`PartIII-b:C/rep/2/6/3/3`): the `y·∇_y` identity of `X₀` off the old disk. -/
theorem sepX0YGrad : SepX0YGrad :=
  sepX0YGrad_of sepX0KerInt
    (kerIntD1_of paramHasFDeriv1 kdGapPt kdGapInt kdGapMeas kdGapSmooth kerIntProd kerFFderiv)

end UnforcedLeray.Short.PartIIIb.Concrete
