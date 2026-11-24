import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_polyExp` (source: `the November 2 reference manuscript`, lines 4823-4830, 5900-5904)

Let `ν_n → 0⁺` and `c > 0`. Then `x_n := c / ν_n → +∞`, and
`ν_n⁻¹^k e^{-c/ν_n} = c⁻¹^k (x_n^k e^{-x_n})` with `x^k e^{-x} → 0` (Mathlib
`tendsto_pow_mul_exp_neg_atTop_nhds_zero`).
For the square-root version, `ν_n⁻¹^k = (√ν_n)⁻¹^(2k)`, and the same argument applies
with `√ν_n → 0⁺` and the exponent `2k`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- If `ν_n → 0` with `ν_n > 0`, then `ν_n⁻¹ → +∞`. -/
theorem polyExp_recip_atTop {ν : ℕ → ℝ} (hpos : ∀ n, 0 < ν n) (hν : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun n => (ν n)⁻¹) atTop atTop := by
  have h1 : Tendsto ν atTop (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hν, Eventually.of_forall (fun n => Set.mem_Ioi.mpr (hpos n))⟩
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- If `ν_n → 0` with `ν_n > 0` and `c > 0`, then `c / ν_n → +∞`. -/
theorem polyExp_div_atTop {c : ℝ} (hc : 0 < c) {ν : ℕ → ℝ} (hpos : ∀ n, 0 < ν n)
    (hν : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun n => c / ν n) atTop atTop := by
  have h := Filter.Tendsto.const_mul_atTop hc (polyExp_recip_atTop hpos hν)
  have e : (fun n => c / ν n) = fun n => c * (ν n)⁻¹ := by
    funext n
    rw [div_eq_mul_inv]
  rw [e]
  exact h

/-- The algebraic identity `t⁻¹^k e^{-c/t} = c⁻¹^k ((c/t)^k e^{-c/t})` for `c ≠ 0`. -/
theorem polyExp_key {c t : ℝ} (hc : 0 < c) (k : ℕ) :
    t⁻¹ ^ k * Real.exp (-c / t) = c⁻¹ ^ k * ((c / t) ^ k * Real.exp (-(c / t))) := by
  have hc0 : c ≠ 0 := hc.ne'
  have h1 : t⁻¹ = c⁻¹ * (c / t) := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  rw [neg_div, h1, mul_pow]
  ring

/-- `T_polyExp`: polynomial times exponential decay in `ν⁻¹` tends to zero. -/
theorem polyExp : UnforcedLeray.Short.PartIIIb.T_polyExp := by
  intro k c ν hc hpos hν
  refine ⟨?_, ?_⟩
  · have hx := polyExp_div_atTop hc hpos hν
    have hpoly : Tendsto (fun x : ℝ => x ^ k * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have hcomp := (hpoly.comp hx).const_mul (c⁻¹ ^ k)
    rw [mul_zero] at hcomp
    refine hcomp.congr (fun n => ?_)
    exact (polyExp_key (t := ν n) hc k).symm
  · have hspos : ∀ n, 0 < Real.sqrt (ν n) := fun n => Real.sqrt_pos.mpr (hpos n)
    have hsν : Tendsto (fun n => Real.sqrt (ν n)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hν
      rw [Real.sqrt_zero] at h
      exact h
    have hx := polyExp_div_atTop hc hspos hsν
    have hpoly : Tendsto (fun x : ℝ => x ^ (2 * k) * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * k)
    have hcomp := (hpoly.comp hx).const_mul (c⁻¹ ^ (2 * k))
    rw [mul_zero] at hcomp
    have hsq : ∀ n, (ν n)⁻¹ ^ k = (Real.sqrt (ν n))⁻¹ ^ (2 * k) := by
      intro n
      have h : Real.sqrt (ν n) ^ 2 = ν n := Real.sq_sqrt (le_of_lt (hpos n))
      rw [pow_mul]
      congr 1
      rw [inv_pow, h]
    refine hcomp.congr (fun n => ?_)
    have e := polyExp_key (t := Real.sqrt (ν n)) hc (2 * k)
    rw [← hsq n] at e
    exact e.symm

end UnforcedLeray.Short.PartIIIb
