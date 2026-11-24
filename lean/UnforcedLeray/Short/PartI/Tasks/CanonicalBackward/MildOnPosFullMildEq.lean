import UnforcedLeray.Short.PartI.Sub.PartI_C08_1

/-!
# `PartI:C08/1/2`: proof of `MildOnPosFullMildEq`

Source `the November 2 reference manuscript`,
lines 1094-1125.  The mild identity `V' θ = S θ θ' (V' θ')` together with the Duhamel form
`Cons.G3b.S_mild` of `S` gives `FullMildEq`, after the mild identity is applied at the
intermediate points `-u` of the integral.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray Set

theorem mildOnPosFullMildEq_proof : UnforcedLeray.Short.PartI.MildOnPosFullMildEq := by
  intro b V' hb hV θ θ' hbθ hθθ'
  have hθ : 0 < θ := lt_of_lt_of_le hb hbθ
  rw [hV θ θ' hθ hθθ', Cons.G3b.S_mild hθ hθθ']
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le (show -θ' ≤ -θ by linarith)] at hu
  have hu0 : 0 < -u := by linarith [hu.2]
  rw [hV (-u) θ' hu0 (by linarith [hu.1])]

end UnforcedLeray.Short.PartI
