import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.ZetaMemSolenoidal
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.InnerZetaUnwind
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.DivEpsRecentre

/-!
# `PartII-a:N01/9/2/3`: `WeakProjectionInvisible`

Source `the November 2 reference manuscript` lines 1669-1676.
The three step Props `ZetaMemSolenoidal`, `InnerZetaUnwind`, `DivEpsRecentre` are proved in
their own files; this file composes them through the assembly `weakProjectionInvisible_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem weakProjectionInvisible : UnforcedLeray.Short.PartIIa.N01.WeakProjectionInvisible :=
  weakProjectionInvisible_of zetaMemSolenoidal innerZetaUnwind divEpsRecentre

end UnforcedLeray.Short.PartIIa.N01
