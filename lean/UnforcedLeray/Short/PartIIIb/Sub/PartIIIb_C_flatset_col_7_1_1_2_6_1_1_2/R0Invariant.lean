import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.R0Invariant_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1.T0Invariant

/-!
# `R0SolenoidalInvariant` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/2/1`)

Source `the November 2 reference manuscript`
1650-1656. The resolvent preserves the solenoidal subspace, because the semigroup does
(`T0SolenoidalInvariant`, proved in `T0Invariant`) and the reduction
`r0SolenoidalInvariant_of` transfers this to `R0SolenoidalInvariant`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

theorem r0SolenoidalInvariant :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.R0SolenoidalInvariant :=
  UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.r0SolenoidalInvariant_of
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.t0SolenoidalInvariant

end
