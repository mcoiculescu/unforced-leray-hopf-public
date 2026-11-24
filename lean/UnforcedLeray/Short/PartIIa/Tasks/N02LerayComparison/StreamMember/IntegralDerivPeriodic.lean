import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
(integration by parts in `q` by periodicity). Target: `IntegralDerivPeriodic`
(`Sub/N02_2.lean`). Proof: for `c ≤ 0` the interval `Ioc 0 c` is empty. For `0 < c` the set
integral is the interval integral `∫ t in 0..c, deriv h t = h c - h 0`, and `h c = h (0 + c) = h 0`
by periodicity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

theorem integralDerivPeriodic : UnforcedLeray.Short.PartIIa.IntegralDerivPeriodic := by
  intro c h hh hper
  by_cases hc : 0 < c
  · have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) c, DifferentiableAt ℝ h x :=
      fun x _ => (hh.differentiable (by simp)) x
    have hint : IntervalIntegrable (deriv h) MeasureTheory.volume 0 c :=
      (hh.continuous_deriv (by simp)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_of_le hc.le,
      intervalIntegral.integral_deriv_eq_sub hdiff hint]
    have hc0 : h c = h 0 := by
      have := hper 0
      rwa [zero_add] at this
    rw [hc0, sub_self]
  · rw [Set.Ioc_eq_empty hc]
    simp
