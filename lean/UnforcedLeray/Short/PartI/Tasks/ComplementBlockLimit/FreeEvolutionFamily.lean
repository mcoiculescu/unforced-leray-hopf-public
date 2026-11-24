import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Stability

/-!
# Target `PartI:C03/5`: `freeEvolutionFamily`

Source of record: `the November 2 reference manuscript`, lines 1019-1021
("the evolution exists for measurable `β` by the Dyson series based on `exp(D∫β)`").
This file proves the `Prop` `FreeEvolutionFamily` of `Short/PartI/Sub/C03.lean` with no extra
hypothesis.

Method. Fix `[a,b]`. The Dyson family `E := dyson (fdsFam a b βs β ..) (fdsA lam κ a b βs β ..)`
is an `Evolution.EvolutionFamily` on `[a,b]`. A free evolution `F` with `IsFreeDiffusionEvolution`
satisfies the left Duhamel identity on every triangle of `[a,b]` (the `duhamel` field, with the
definitions `fdsFam` and `fdsA` unfolding to the free family and the bounded interaction), and
`F t s x` is continuous in `t` on `[s,b]` (the `cont` field). Hence `Evolution.dyson_unique`
identifies `F` with `E.U` on the triangle `a ≤ u ≤ v ≤ b`. This is the same call as in
`fds_hasSum` (`Tasks/FreeDiffusionEvolution/Stability.lean`), on the block `[a,b]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C03/5`** (source lines 1019-1021): for measurable `0 ≤ β ≤ β_*` and every
free evolution `F` of `IsFreeDiffusionEvolution`, on every block `[a,b]` there is an evolution
family `E` with `E.U v u = F v u` whenever `a ≤ u ≤ v ≤ b`. -/
theorem freeEvolutionFamily : FreeEvolutionFamily := by
  intro lam kappa βs β hβm hβb F hF a b
  refine ⟨UnforcedLeray.Evolution.dyson (fdsFam a b βs β hβm hβb)
    (fdsA lam kappa a b βs β hβm hβb), ?_⟩
  intro p q hap hpq hqb
  exact (UnforcedLeray.Evolution.dyson_unique (fdsFam a b βs β hβm hβb)
    (fdsA lam kappa a b βs β hβm hβb) F
    (fun u _ _ y => (hF.cont y u).mono Icc_subset_Ici_self)
    (fun u v _ huv _ y => hF.duhamel u v huv y) p q hap hpq hqb).symm

end UnforcedLeray.Short.PartI
