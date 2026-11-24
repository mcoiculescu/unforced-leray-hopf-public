import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Lib.CylinderB.Periodize
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Gaussian lattice sum `n ↦ e^{-B n²}` over `ℤ`, `B > 0`. -/
theorem pm_summable (B : ℝ) (hB : 0 < B) :
    Summable (fun n : ℤ => Real.exp (-(B * (n : ℝ) ^ 2))) := by
  have hr : Real.exp (-B) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hr0 : 0 ≤ Real.exp (-B) := (Real.exp_pos _).le
  have hnat : Summable (fun n : ℕ => Real.exp (-(B * ((n : ℤ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr)
    rw [Int.cast_natCast, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have h1 : 1 ≤ n := h
        have : (1 : ℝ) ≤ n := by exact_mod_cast h1
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le]
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun n => ?_
  push_cast
  ring_nf

/-- Weight comparison: `(1+ρ)² e^{-ρ/(4A)} ≤ (1+16A)² e^{-ρ/(8A)}` for `ρ ≥ 0`, `A > 0`. -/
theorem pm_weight (A ρ : ℝ) (hA : 0 < A) (hρ : 0 ≤ ρ) :
    (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * A)) ≤ (1 + 16 * A) ^ 2 * Real.exp (-ρ / (8 * A)) := by
  have hA16 : (0 : ℝ) < 16 * A := by linarith
  have ht : 0 ≤ ρ / (16 * A) := div_nonneg hρ hA16.le
  have h1 := Real.add_one_le_exp (ρ / (16 * A))
  have h2 : ρ / (16 * A) * (16 * A) = ρ := div_mul_cancel₀ ρ hA16.ne'
  have hE1 : 1 + ρ ≤ (1 + 16 * A) * Real.exp (ρ / (16 * A)) := by
    have hpos : (0 : ℝ) ≤ 1 + 16 * A := by linarith
    nlinarith [mul_nonneg hpos (sub_nonneg.2 h1), h2, ht, hA]
  have hsq : (1 + ρ) ^ 2 ≤ ((1 + 16 * A) * Real.exp (ρ / (16 * A))) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hE1 2
  have hE : Real.exp (ρ / (16 * A)) * Real.exp (ρ / (16 * A)) * Real.exp (-ρ / (4 * A))
      = Real.exp (-ρ / (8 * A)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hEpos : 0 ≤ Real.exp (-ρ / (4 * A)) := (Real.exp_pos _).le
  calc (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * A))
      ≤ ((1 + 16 * A) * Real.exp (ρ / (16 * A))) ^ 2 * Real.exp (-ρ / (4 * A)) :=
        mul_le_mul_of_nonneg_right hsq hEpos
    _ = (1 + 16 * A) ^ 2 * (Real.exp (ρ / (16 * A)) * Real.exp (ρ / (16 * A)) *
          Real.exp (-ρ / (4 * A))) := by ring
    _ = (1 + 16 * A) ^ 2 * Real.exp (-ρ / (8 * A)) := by rw [hE]

/-- Pointwise domination of one lattice term, uniform in the summation index through the
Gaussian lattice sum: for `g` with the Gaussian bound (constant `K ≥ 0`), `A > 0`, `c > 0`:
`‖g(x₁ - nc, x₂)‖ ≤ K(1+16A)² e^{x₁²/(8A)} e^{-(c²/(16A)) n²}`. -/
theorem pm_term_bound (A c K : ℝ) (g : ℝ × ℝ → ℂ) (hA : 0 < A) (hK : 0 ≤ K)
    (hb : ∀ x : ℝ × ℝ, ‖g x‖ ≤
      K * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))
    (x : ℝ × ℝ) (n : ℤ) :
    ‖g (x.1 - n * c, x.2)‖ ≤
      K * (1 + 16 * A) ^ 2 * Real.exp (x.1 ^ 2 / (8 * A)) *
        Real.exp (-((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)) := by
  have hb' := hb (x.1 - n * c, x.2)
  dsimp only at hb'
  have e : 1 + (x.1 - n * c) ^ 2 + x.2 ^ 2 = 1 + ((x.1 - n * c) ^ 2 + x.2 ^ 2) := by ring
  rw [e] at hb'
  have hρ : 0 ≤ (x.1 - n * c) ^ 2 + x.2 ^ 2 := by positivity
  have h1 := pm_weight A ((x.1 - n * c) ^ 2 + x.2 ^ 2) hA hρ
  have h8 : (0 : ℝ) < 8 * A := by linarith
  have h2 : Real.exp (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (8 * A)) ≤
      Real.exp (x.1 ^ 2 / (8 * A)) * Real.exp (-((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hdiff : x.1 ^ 2 / (8 * A) + -((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)
        - (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (8 * A))
        = (x.1 ^ 2 + ((x.1 - n * c) ^ 2 + x.2 ^ 2) - c ^ 2 / 2 * (n : ℝ) ^ 2) / (8 * A) := by
      field_simp
      ring
    have hnum : 0 ≤ x.1 ^ 2 + ((x.1 - n * c) ^ 2 + x.2 ^ 2) - c ^ 2 / 2 * (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (x.1 - n * c / 2), sq_nonneg x.2]
    have : 0 ≤ x.1 ^ 2 / (8 * A) + -((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)
        - (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (8 * A)) := by
      rw [hdiff]
      exact div_nonneg hnum h8.le
    linarith
  calc ‖g (x.1 - n * c, x.2)‖
      ≤ K * (1 + ((x.1 - n * c) ^ 2 + x.2 ^ 2)) ^ 2 *
          Real.exp (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)) := hb'
    _ = K * ((1 + ((x.1 - n * c) ^ 2 + x.2 ^ 2)) ^ 2 *
          Real.exp (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A))) := by ring
    _ ≤ K * ((1 + 16 * A) ^ 2 * Real.exp (-((x.1 - n * c) ^ 2 + x.2 ^ 2) / (8 * A))) :=
        mul_le_mul_of_nonneg_left h1 hK
    _ ≤ K * ((1 + 16 * A) ^ 2 * (Real.exp (x.1 ^ 2 / (8 * A)) *
          Real.exp (-((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hK
    _ = K * (1 + 16 * A) ^ 2 * Real.exp (x.1 ^ 2 / (8 * A)) *
          Real.exp (-((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2)) := by ring

/-- Summability of the periodization series at every point. -/
theorem pm_summable_term (A c K : ℝ) (g : ℝ × ℝ → ℂ) (hA : 0 < A) (hc : 0 < c) (hK : 0 ≤ K)
    (hb : ∀ x : ℝ × ℝ, ‖g x‖ ≤
      K * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))
    (x : ℝ × ℝ) : Summable (fun n : ℤ => g (x.1 - n * c, x.2)) := by
  have hB : 0 < c ^ 2 / (16 * A) := by positivity
  have hS := (pm_summable (c ^ 2 / (16 * A)) hB).mul_left
    (K * (1 + 16 * A) ^ 2 * Real.exp (x.1 ^ 2 / (8 * A)))
  exact Summable.of_norm_bounded hS (fun n => pm_term_bound A c K g hA hK hb x n)

/-- **Measurability of a periodization of a Gaussian-bounded measurable function** (source 4568).
Route: the finite partial sums over `s : Finset ℤ` are measurable and converge pointwise along
`atTop` (`HasSum` is exactly this limit, and the series is summable by `pm_summable_term`);
`measurable_of_tendsto_metrizable'` on the countably generated filter `atTop` on `Finset ℤ`. -/
theorem periodizeMeas : PeriodizeMeas := by
  intro c A K g hc hA hg hb
  have hK : 0 ≤ K := by
    have h0 := hb (0, 0)
    norm_num at h0
    linarith [norm_nonneg (g (0, 0))]
  refine measurable_of_tendsto_metrizable' (u := (atTop : Filter (Finset ℤ)))
    (f := fun (s : Finset ℤ) (x : ℝ × ℝ) => ∑ n ∈ s, g (x.1 - n * c, x.2)) (fun s => ?_) ?_
  · exact Finset.measurable_sum s fun n _ => hg.comp (UnforcedLeray.Cyl.measurable_shift c n)
  · rw [tendsto_pi_nhds]
    intro x
    have hs := (pm_summable_term A c K g hA hc hK hb x).hasSum
    unfold IIIa.periodizeC
    exact hs

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
