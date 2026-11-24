import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `GELinPairDeriv`: the weak derivative against a phase test in `pairF` form (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/5`.  The hypothesis `HasPhaseOp (-∂_m) v v'` tested at the
phase test `Θ` gives `⟪-∂_mΘ, v⟫ = ⟪Θ, v'⟫`; the pairing is then rewritten to `pairF` on the
periodic representatives, and `pairF` is linear in its first argument.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseCell)

theorem gELinPairDeriv : GELinPairDeriv := by
  intro P _ v v' m hop Θ hΘ
  have h1 := hop Θ hΘ
  beta_reduce at h1
  rw [phasePair_neg (hΘ.dy m)] at h1
  rw [UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep (hΘ.dy m),
    UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΘ] at h1
  linear_combination -h1

end UnforcedLeray.Short.PartIIIb.Concrete
