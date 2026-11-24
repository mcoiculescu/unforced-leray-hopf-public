import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Vanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Commutator
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Jet

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1` (`DualRemPointwise`): assembly.

Source: `the November 2 reference manuscript` lines 1923-1927.
The four leaves supply the hypotheses of `dualRemPointwise_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem dualRemPointwise : UnforcedLeray.Short.IIb.DualRemPointwise :=
  dualRemPointwise_of dualRemVanish dualPsiInfSmooth genericCommBound dualPsiInfJet

end UnforcedLeray.Short.IIb
