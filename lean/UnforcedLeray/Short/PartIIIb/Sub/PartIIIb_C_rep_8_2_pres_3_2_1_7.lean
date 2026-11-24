import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1

/-!
# The data-free leaf `DmuDivFreeSol` (`PartIII-b:C/rep/8/2/pres/3/2/1/7`)

Source of record: `the November 2 reference manuscript` (4140-4141, 5254-5257:
`D₀` preserves solenoidality).  For a jointly `C^∞` field `X` with pointwise vanishing divergence,
`D₀X(τ)` is `C¹` and has pointwise vanishing divergence (`pwDmuDivFree_proved`, `PwDmuDivFree`
of `Sub/IIIb-D2_3_2/Pw6.lean`), hence is weakly solenoidal (`isSolenoidal_of_pointwise`,
`Sub/PartIII-b_C_ward_13_8_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`DmuDivFreeSol`** (source 4140-4141, 5254-5257): `D₀` maps pointwise divergence-free jointly
smooth fields to solenoidal slices. -/
theorem dmuDivFreeSol : DmuDivFreeSol := by
  intro ν X hX hdiv τ
  have hD := pwDmuDivFree_proved ν 0 X hX hdiv
  have hsm : ContDiff ℝ 1 (physDmu ν 0 X τ) :=
    (contDiff_physDmu ν 0 X hX τ).of_le (by exact_mod_cast le_top)
  exact isSolenoidal_of_pointwise hsm (hD τ)

end UnforcedLeray.Short.PartIIIb.Concrete
