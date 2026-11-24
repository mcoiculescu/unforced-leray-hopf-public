import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

/-!
# `wardX0Smooth_of` (`PartIII-b:IIIb-D2/3/1/1`), unconditional assembly

The conditional theorem `UnforcedLeray.Short.PartIIIb.Concrete.wardX0Smooth_of`
(`Sub/IIIb-D2_3_1_1.lean`) is applied with
* `hreg := oldSourceReg_all` (`Sub/IIIb-D2_3_1_1/L1.lean`), and
* `hW := sepWSmoothOn_of IIIa.sepKernelBounds` (`Sub/IIIb-D2_3_1_1/L2.lean`,
  `PartIII-a/T15_SepKernelBounds.lean`).

The target is stated in the namespace `...Concrete.Final` because the name
`wardX0Smooth_of` is already taken in `...Concrete` by the imported conditional theorem.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.Final

theorem wardX0Smooth_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    WardX0Smooth c mZ ρb γ ν ε μ hχo :=
  UnforcedLeray.Short.PartIIIb.Concrete.wardX0Smooth_of c mZ ρb γ ν ε μ hχo
    (UnforcedLeray.Short.PartIIIb.Concrete.oldSourceReg_all c mZ ρb γ ν ε hχo)
    (UnforcedLeray.Short.PartIIIb.Concrete.sepWSmoothOn_of
      UnforcedLeray.Short.IIIa.sepKernelBounds)

end UnforcedLeray.Short.PartIIIb.Concrete.Final
