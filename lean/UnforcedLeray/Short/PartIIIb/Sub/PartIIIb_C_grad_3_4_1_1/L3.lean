import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L6

/-!
# `PartIII-b:C/grad/3/4/1/1/3` (leaf B, `h^p`): termwise differentiation of the lattice sum

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`gradHpTsum` is the `GradHpTsum` leaf: the operators `∂_q, ∂_η, 𝒦` commute with the lattice sum
defining `h^p_A`.  It follows from the x-local majorants `hpXData` (`L2.lean`) and the s-local
majorants `hpSData` (`L6.lean`) through the general lemma `gradHpTsum_of` (`tsumOps_of`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf B (`h^p`): `∂_q, ∂_η, 𝒦` commute with the lattice sum defining `h^p_A`
(source 5036-5039, 5063-5079). -/
theorem gradHpTsum : GradHpTsum :=
  gradHpTsum_of hpXData hpSData

end UnforcedLeray.Short.PartIIIb.Concrete
