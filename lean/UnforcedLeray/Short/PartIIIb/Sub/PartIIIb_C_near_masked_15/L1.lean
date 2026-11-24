import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15.Helpers

/-!
# Leaf 1 of `PartIII-b:C/near/masked/15`: `MaskedLiftSource`

Source `the November 2 reference manuscript`
3905-3912 (masked `sep:resolvent`), 3604-3610.

The masked lift of a box tensor is measurable (mask set measurable, `measurable_cartLift_entry`),
`2c/R`-periodic (`chartOf_period`), and vanishes for `|z'| > R e^{-δ/2}/√s` (the mask
`e^δ s < R²/|z'|²` is then false).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst

theorem maskedLiftSource : MaskedLiftSource := by
  intro R c δ s hR hc hδ hs f hf
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hfun : (fun p : ℝ × Space => maskedLift R c δ s f p.1 p.2 i j) =
        fun p : ℝ × Space => if Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2)
          then cartLift R c f p.1 p.2 i j else 0 := by
      funext p
      unfold maskedLift
      split_ifs <;> simp
    rw [hfun]
    have hset : MeasurableSet {p : ℝ × Space |
        Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2)} := by
      apply measurableSet_lt measurable_const
      fun_prop
    exact Measurable.ite hset
      (UnforcedLeray.Short.PartIIIb.Concrete.T8_1.measurable_cartLift_entry R c f hf.measurable i j)
      measurable_const
  · intro τ z
    simp only [maskedLift, cartLift, H15.chartOf_period R c hR hc]
  · intro τ z hz
    have hq : 0 ≤ R * Real.exp (-δ / 2) / Real.sqrt s :=
      div_nonneg (mul_nonneg hR.le (Real.exp_pos _).le) (Real.sqrt_nonneg _)
    have hsq := (Real.lt_sqrt hq).1 hz
    rw [div_pow, mul_pow, Real.sq_sqrt hs.le] at hsq
    have h1 : R ^ 2 * Real.exp (-δ / 2) ^ 2 < (z 0 ^ 2 + z 1 ^ 2) * s := (div_lt_iff₀ hs).1 hsq
    have he2 : Real.exp (-δ / 2) ^ 2 * Real.exp δ = 1 := by
      rw [sq, mul_assoc, ← Real.exp_add, ← Real.exp_add,
        show -δ / 2 + (-δ / 2 + δ) = 0 by ring, Real.exp_zero]
    have h2 : R ^ 2 * Real.exp (-δ / 2) ^ 2 * Real.exp δ < (z 0 ^ 2 + z 1 ^ 2) * s * Real.exp δ :=
      mul_lt_mul_of_pos_right h1 (Real.exp_pos δ)
    have h3 : R ^ 2 * Real.exp (-δ / 2) ^ 2 * Real.exp δ = R ^ 2 := by
      rw [mul_assoc, he2, mul_one]
    unfold maskedLift
    dsimp only
    rw [if_neg]
    intro hm
    have hx0 : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := by positivity
    have hxpos : 0 < z 0 ^ 2 + z 1 ^ 2 := by
      rcases hx0.eq_or_lt with h | h
      · rw [← h, div_zero] at hm
        nlinarith [Real.exp_pos δ]
      · exact h
    have hm' : Real.exp δ * s * (z 0 ^ 2 + z 1 ^ 2) < R ^ 2 := (lt_div_iff₀ hxpos).1 hm
    nlinarith [h2, h3, hm']
