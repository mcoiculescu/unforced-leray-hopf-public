import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0

/-!
# Proof-independent age indexing for the actual physical heat family

The physical S₀ family is parameterized by an age and interval-bound proofs. This helper records
that its value depends only on the age, so semigroup age equalities can be used without proof-term
coercion noise.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Actual physical `S₀` has the same value for equal ages, independently of the proofs that the
ages lie in the short strip. -/
theorem actualWeightedHeatS0_age_congr {c m a b : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hab : a = b)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    actualWeightedHeatS0 (c := c) hc1 hm ha0 ha1 =
      actualWeightedHeatS0 (c := c) hc1 hm hb0 hb1 := by
  subst b
  congr 1

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_age_congr
