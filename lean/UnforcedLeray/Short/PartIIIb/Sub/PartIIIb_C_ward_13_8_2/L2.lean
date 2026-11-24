import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2.L3

/-!
# `PartIII-b:C/ward/13/8/2/2/L2`: the scale-invariant annular Poincare inequality

Source `the November 2 reference manuscript`
117-118, 2641-2642. The statement `AnnularPoincare` is from `Sub/PartIII-b_C_ward_13_8_2.lean`.
The proof is the scaling step `annularPoincare_of` (file `PartIII-b_C_ward_13_8_2_2.lean`) applied
to the scaling `annularScaling` (file `PartIII-b_C_ward_13_8_2_2/L3.lean`) and the unit-annulus
inequality `unitAnnularPoincare` (file `PartIII-b_C_ward_13_8_2_2/L2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem annularPoincare : AnnularPoincare :=
  AnnPoinSub.annularPoincare_of annularScaling unitAnnularPoincare

end UnforcedLeray.Short.PartIIIb.Concrete
