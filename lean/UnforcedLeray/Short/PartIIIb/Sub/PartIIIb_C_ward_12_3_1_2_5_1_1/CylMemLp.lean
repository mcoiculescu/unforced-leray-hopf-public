import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/1`: `cylProfile R₀ ∈ L^{q0E}(ℝ³)`

Source `the November 2 reference manuscript`
lines 2547-2549.

With `ϱ = √(y₀²+y₁²)`, `s = |y₃|` (here `y 2`), the profile is `1/(ϱ (ϱ+s)²)` for `ϱ > R₀`
and `(1+s)⁻²` for `ϱ ≤ R₀`.  Both are bounded by `C (1+‖y‖)⁻²`, using `‖y‖ ≤ ϱ + s`, so the
`q0E = 11/4` power is dominated by `C' (1+‖y‖)⁻⁴`, which is integrable on `ℝ³`
(`integrable_one_add_norm`, since `3 < 4`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma cyl_norm_le_sum (y : UnforcedLeray.Space) :
    ‖y‖ ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_iff]
  have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ y 0 ^ 2 + y 1 ^ 2 by positivity)
  have h3 : 0 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_nonneg _
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg (y 2), mul_nonneg h3 (abs_nonneg (y 2)), sq_abs (y 2)]

lemma cyl_rpow_neg_two {a : ℝ} (ha : 0 < a) : a ^ (-2 : ℝ) = 1 / a ^ 2 := by
  rw [Real.rpow_neg ha.le, Real.rpow_two, one_div]

lemma cyl_rpow_neg_three {a : ℝ} (ha : 0 < a) : a ^ (-3 : ℝ) = 1 / a ^ 3 := by
  rw [Real.rpow_neg ha.le, Real.rpow_ofNat, one_div]

lemma cylProfile_nonneg (R0 : ℝ) (y : UnforcedLeray.Space) : 0 ≤ cylProfile R0 y := by
  unfold cylProfile
  split_ifs
  · exact Real.rpow_nonneg (by positivity) _
  · apply mul_nonneg
    · exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
    · exact Real.rpow_nonneg (by positivity) _

/-- Real-variable core: `ϱ = √(y₀²+y₁²)`, `s = |y₃|`, `N = ‖y‖ ≤ ϱ + s`. -/
lemma cyl_core (R0 ρ s N : ℝ) (hR0 : 0 < R0) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (hN0 : 0 ≤ N)
    (hN : N ≤ ρ + s) :
    (if ρ ≤ R0 then (1 + s) ^ (-2 : ℝ) else ρ ^ (-3 : ℝ) * (1 + s / ρ) ^ (-2 : ℝ))
      ≤ ((1 + R0) ^ 2 + (1 + 1 / R0) ^ 2 / R0) * (1 + N) ^ (-2 : ℝ) := by
  have hD : 0 ≤ (1 + 1 / R0) ^ 2 / R0 := by positivity
  have hC1 : (1 + R0) ^ 2 ≤ (1 + R0) ^ 2 + (1 + 1 / R0) ^ 2 / R0 := by linarith
  rw [cyl_rpow_neg_two (by positivity : (0 : ℝ) < 1 + N)]
  split_ifs with h
  · rw [cyl_rpow_neg_two (by positivity : (0 : ℝ) < 1 + s), mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 + N ≤ (1 + R0) * (1 + s) := by nlinarith
    have h2 : (1 + N) ^ 2 ≤ ((1 + R0) * (1 + s)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) h1
    have h3 : 0 ≤ (1 + s) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hC1 h3]
  · have h' : R0 < ρ := not_le.mp h
    have hpos : 0 < ρ := by linarith
    have hT : 0 < ρ + s := by linarith
    rw [cyl_rpow_neg_three hpos, cyl_rpow_neg_two (by positivity : (0 : ℝ) < 1 + s / ρ)]
    have e : 1 / ρ ^ 3 * (1 / (1 + s / ρ) ^ 2) = 1 / (ρ * (ρ + s) ^ 2) := by
      field_simp
    rw [e]
    have hq : 1 ≤ (ρ + s) / R0 := by
      rw [le_div_iff₀ hR0]; linarith
    have hK : (1 + N) ^ 2 ≤ (1 + 1 / R0) ^ 2 * (ρ + s) ^ 2 := by
      have hA : 1 + N ≤ (1 + 1 / R0) * (ρ + s) := by
        have : (1 + 1 / R0) * (ρ + s) = (ρ + s) + (ρ + s) / R0 := by ring
        linarith
      have hA0 : 0 ≤ 1 + N := by linarith
      calc (1 + N) ^ 2 ≤ ((1 + 1 / R0) * (ρ + s)) ^ 2 := pow_le_pow_left₀ hA0 hA 2
        _ = (1 + 1 / R0) ^ 2 * (ρ + s) ^ 2 := by ring
    have hstep1 : 1 / (ρ * (ρ + s) ^ 2) ≤ 1 / (R0 * (ρ + s) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right h'.le (by positivity)
    have hstep2 : 1 / (R0 * (ρ + s) ^ 2) ≤ (1 + 1 / R0) ^ 2 / R0 * (1 / (1 + N) ^ 2) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hK hR0.le]
    have hfin : (1 + 1 / R0) ^ 2 / R0 * (1 / (1 + N) ^ 2) ≤
        ((1 + R0) ^ 2 + (1 + 1 / R0) ^ 2 / R0) * (1 / (1 + N) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [sq_nonneg (1 + R0)]
    calc 1 / (ρ * (ρ + s) ^ 2) ≤ 1 / (R0 * (ρ + s) ^ 2) := hstep1
      _ ≤ (1 + 1 / R0) ^ 2 / R0 * (1 / (1 + N) ^ 2) := hstep2
      _ ≤ ((1 + R0) ^ 2 + (1 + 1 / R0) ^ 2 / R0) * (1 / (1 + N) ^ 2) := hfin

lemma cylProfile_bound (R0 : ℝ) (hR0 : 0 < R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space,
      cylProfile R0 y ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
  refine ⟨(1 + R0) ^ 2 + (1 + 1 / R0) ^ 2 / R0, by positivity, fun y => ?_⟩
  have hN := cyl_norm_le_sum y
  have hρ0 : 0 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ |y 2| := abs_nonneg _
  have hN0 : 0 ≤ ‖y‖ := norm_nonneg _
  unfold cylProfile
  exact cyl_core R0 _ _ _ hR0 hρ0 hs0 hN0 hN

lemma measurable_cylProfile (R0 : ℝ) : Measurable (cylProfile R0) := by
  unfold cylProfile
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le (by fun_prop) measurable_const
  · fun_prop
  · fun_prop

/-- **Leaf 1** (`PartIII-b:C/ward/12/3/1/2/5/1/1/1`, source 2547-2549): the cylindrical profile is
in `L^{q0E}(ℝ³)`. -/
theorem cylProfile_memLp : CylProfileMemLp := by
  intro R0 hR0
  obtain ⟨C, hC, hle⟩ := cylProfile_bound R0 hR0
  have hmeas : AEStronglyMeasurable (cylProfile R0) volume :=
    (measurable_cylProfile R0).aestronglyMeasurable
  have hne0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    (zero_lt_one.trans UnforcedLeray.B0412.one_lt_q0E).ne'
  have hnetop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  refine (integrable_norm_rpow_iff hmeas hne0 hnetop).1 ?_
  rw [UnforcedLeray.B0412.q0E_toReal]
  have hint : Integrable (fun y : UnforcedLeray.Space => C ^ (11 / 4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ))
      volume := by
    apply Integrable.const_mul
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine hint.mono' ?_ ?_
  · exact ((measurable_cylProfile R0).norm.pow_const _).aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ fun y => ?_
    have hf0 := cylProfile_nonneg R0 y
    rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg (Real.rpow_nonneg hf0 _)]
    have hN0 : 0 ≤ ‖y‖ := norm_nonneg _
    have hbase : (0 : ℝ) < 1 + ‖y‖ := by linarith
    calc cylProfile R0 y ^ (11 / 4 : ℝ)
        ≤ (C * (1 + ‖y‖) ^ (-2 : ℝ)) ^ (11 / 4 : ℝ) :=
          Real.rpow_le_rpow hf0 (hle y) (by norm_num)
      _ = C ^ (11 / 4 : ℝ) * (1 + ‖y‖) ^ (-11 / 2 : ℝ) := by
          rw [Real.mul_rpow hC (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le]
          norm_num
      _ ≤ C ^ (11 / 4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC _)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete
