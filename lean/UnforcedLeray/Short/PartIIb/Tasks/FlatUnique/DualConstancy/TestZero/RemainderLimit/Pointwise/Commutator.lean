import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1_3_easy
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Commutator.Formula

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/3`: assembly of `GenericCommBound`.

Source: `the November 2 reference manuscript` lines 1923-1927.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem genericCommBound : UnforcedLeray.Short.IIb.GenericCommBound :=
  genericCommBound_of commFormula cutoffDerivBound commJetBound

end UnforcedLeray.Short.IIb
