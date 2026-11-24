import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Framework

/-!
# Part II-a, task `PartII-a:R01`, leaf `profileJetAdd`: additivity of the mixed jet

Source of record: `the November 2 reference manuscript`, lines 439-459 (the
decomposition `ψ = ψ̃ + S` read at ages `0 < s ≤ 1`) and lines 1294-1297.

Proves `ProfileJetAdd` (`Sub/R01_1.lean`) from the calculus helpers `EarlyCalc.jet_add` of
`Tasks/R01/EarlyCalculus/Framework.lean`. The iterates `partialAge^[ℓ] (partialEta^[a] (partialQ^[b] ·))`
are definitionally `EarlyCalc.jet ℓ a b` (`EarlyCalc.jet_eq` is `rfl`), and the domain
`{y | 0 < y.2.2}` is `EarlyCalc.AgeSet`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem profileJetAdd : ProfileJetAdd := by
  intro ℓ a b f g hf hg x hx
  exact EarlyCalc.jet_add ℓ a b hf hg hx

end UnforcedLeray.Short.PartIIa
