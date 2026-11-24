import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest.Smooth

/-!
# `CartLiftIsTest` (source 1639-1650, 2666-2668, 2682)

The Cartesian tensor lift `𝒩_T m = cartLift ε⁻¹ c m` of a smooth chart tensor test is a smooth,
`P`-periodic (`P = 2εc`), spatially bounded Cartesian tensor test.  Smoothness and boundedness come
from `CartLiftIsTest/Smooth.lean` and `CartLiftIsTest/Basic.lean`; periodicity from the exact
invariance of `chartOf` under `τ ↦ τ + 2εc` (`cl_chartOf_period`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

/-- **The tensor lift of a smooth test is a smooth Cartesian tensor** (source 1639-1650). -/
theorem cartLiftIsTest : CartLiftIsTest := by
  intro ε c P hε hc hP m hm
  subst hP
  obtain ⟨s0, s1, L, hs0, hb⟩ := hm.band
  exact
    { smooth := fun i j => cs_smooth ε c hε m hm i j
      periodic := fun τ z => by
        unfold cartLift
        rw [cl_chartOf_period ε c hε hc z τ]
      bounded := by
        obtain ⟨r, hr⟩ := cl_cartLift_bdd ε c hε m s0 s1 L hs0 hb
        exact ⟨r, hr⟩ }

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
