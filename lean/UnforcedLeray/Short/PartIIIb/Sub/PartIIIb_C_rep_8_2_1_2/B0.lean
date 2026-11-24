import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B0.Bound

/-!
# `RawD1Bound0`: the `j = 0` bound of the raw ring derivative (`PartIII-b:C/rep/8/2/1/2/7`)

Source `the November 2 reference manuscript`, lines 2073-2077 and 5462-5476.
The argument is the common core in `B0/Bound.lean` (`rawD1Core`): with `b = v + εH e_z`, the
difference `s[∂_q b - ε(b + 2s∂_s b + η∂_η b)] - s∂_q v` is `s ε (∂_q H e_z - (b + K b))`, bounded
by `18 ε s 𝔴₃` for `ε ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawD1Bound0 : RawD1Bound0 := by
  refine ⟨18, fun L hε p hp => ?_⟩
  exact rawD1Core L hε hp

end UnforcedLeray.Short.PartIIIb.Concrete
