import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials.BasisExpansion
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials.IterSymm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials.SortedIdent
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials.SortPerm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials.CountWords

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `jetNormOfPartials`: the jet norm of partials

Proves `JetNormOfPartials` (defined in `Sub/PartIII-a_T21_2_7_2_1_2.lean`, SP 3060-3073, calculus
only) by applying `jetNormOfPartials_of` to the five lemma theorems `basisExpansion`, `iterSymm`,
`sortedIdent`, `sortPerm`, `countWords`, each proved in `JetNormOfPartials/<Name>.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem jetNormOfPartials : UnforcedLeray.Short.IIIa.JetNormOfPartials :=
  jetNormOfPartials_of basisExpansion iterSymm sortedIdent sortPerm countWords

end UnforcedLeray.Short.IIIa
