import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold.Fubini
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramTail.Bound

/-!
# `PartIII-a:T21/c5/2/1/2`, helper: unfolding a periodized pairing and its `O(d⁻²)` tail

Source: `the November 2 reference manuscript` (SP), lines 2893-2897 (the
periodization `P_d f(y) = Σ_n f(y₁ + nd, y₂)` on the cell of period `d`).

For a continuous kernel `Ψ = O((1 + |y₁| + |y₂|)⁻²)` and a continuous field
`Φ = O(e^{-|y|²/8})`, the cell pairing of the periodizations unfolds,
`∫_{cell d} P_d Ψ · P_d Φ = Σ_n ∫_{ℝ²} Ψ(y) Φ(y₁ + nd, y₂) dy`, and differs from the planar pairing
`∫ Ψ Φ` (the term `n = 0`) by at most `K / d²` for `d ≥ 1`, with `K` explicit in the two decay
constants. This is the pattern of `Clock/FrameFacts/GramUnfold.lean` and `GramTail.lean` for
general `Ψ, Φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.OscGramDual

variable {Ψ Φ : ℝ × ℝ → ℂ}

/-- The cross integral `∫ Ψ(y) Φ(y₁ + a, y₂) dy` converges absolutely with `L¹` norm
`≤ |C₁||C₂| 2080π / (1 + |a|)²`. -/
theorem cross_int (hΨc : Continuous Ψ) (hΦc : Continuous Φ) {C1 C2 : ℝ}
    (hΨ : ∀ y : ℝ × ℝ, ‖Ψ y‖ ≤ C1 * (1 + |y.1| + |y.2|)⁻¹ ^ 2)
    (hΦ : ∀ y : ℝ × ℝ, ‖Φ y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) (a : ℝ) :
    Integrable (fun y : ℝ × ℝ => Ψ y * Φ (y.1 + a, y.2)) ∧
    ∫ y : ℝ × ℝ, ‖Ψ y * Φ (y.1 + a, y.2)‖ ≤ |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by
  have hA : 0 ≤ |C1| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖Ψ y * Φ (y.1 + a, y.2)‖ ≤
      (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have h1 : ‖Ψ y‖ ≤ |C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      (hΨ y).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity))
    have h2 : ‖Φ (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hΦ (y.1 + a, y.2)
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖Ψ y‖ * ‖Φ (y.1 + a, y.2)‖
        ≤ (|C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) *
            (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C1| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
          mul_le_mul_of_nonneg_left (gram_pt a y.1 y.2) hA
  have G8 := integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (|C1| * |C2|) *
      (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (4 / (1 + |a|) ^ 2)).add
      (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hcont : Continuous (fun y : ℝ × ℝ => Ψ y * Φ (y.1 + a, y.2)) :=
    hΨc.mul (hΦc.comp (by fun_prop))
  refine ⟨Integrable.mono' hint hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have hE := exp_neg_sq_mul_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 128 / (1 + |a|) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ∫ y : ℝ × ℝ, ‖Ψ y * Φ (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (|C1| * |C2|) *
          (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_shift_gauss (c := a) (t := 2) (by norm_num),
          integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          128 / (1 + |a|) ^ 2 * (4 * Real.pi * 4)) := by
        gcongr
    _ = |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by ring

/-- Lattice shift summability of a Gaussian-bounded field at any period `d > 0`. -/
theorem summable_shift {C2 : ℝ}
    (hΦ : ∀ y : ℝ × ℝ, ‖Φ y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) {d : ℝ} (hd : 0 < d)
    (y : ℝ × ℝ) :
    Summable (fun n : ℤ => ‖Φ (y.1 + n * d, y.2)‖) := by
  have hs := (UnforcedLeray.Gaussian.summable_translate (s := 2) (c := -d) (by norm_num)
    (neg_ne_zero.2 hd.ne') y.1).mul_left (|C2| * 128)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  have h1 := hΦ (y.1 + n * d, y.2)
  have hq : y.1 - (n : ℝ) * (-d) = y.1 + n * d := by ring
  rw [hq]
  generalize y.1 + (n : ℝ) * d = s at h1 ⊢
  have hE := exp_neg_sq_mul_le s
  have hpos : 0 < (1 + |s|) ^ 2 := by positivity
  have hE' : Real.exp (-s ^ 2 / (4 * 16)) ≤ 128 / (1 + |s|) ^ 2 := by
    rw [le_div_iff₀ hpos]; linarith
  have h2 : Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) ≤ Real.exp (-s ^ 2 / (4 * 16)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ y.2 ^ 2 := sq_nonneg y.2
    linarith [sq_nonneg s]
  have h3 : (1 + |s|) ^ (-(2 : ℝ)) = 1 / (1 + |s|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), inv_eq_one_div]; norm_cast
  rw [h3]
  calc ‖Φ (s, y.2)‖ ≤ C2 * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) := h1
    _ ≤ |C2| * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    _ ≤ |C2| * (128 / (1 + |s|) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans hE') (abs_nonneg C2)
    _ = |C2| * 128 * (1 / (1 + |s|) ^ 2) := by ring

/-- **Unfolding** (SP 2893-2897): `∫_{cell d} P_d Ψ · P_d Φ = Σ_n ∫ Ψ(y) Φ(y₁ + nd, y₂) dy`,
a summable series, for `d > 0`. -/
theorem unfold (hΨc : Continuous Ψ) (hΦc : Continuous Φ) {C1 C2 : ℝ}
    (hΨ : ∀ y : ℝ × ℝ, ‖Ψ y‖ ≤ C1 * (1 + |y.1| + |y.2|)⁻¹ ^ 2)
    (hΦ : ∀ y : ℝ × ℝ, ‖Φ y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) {d : ℝ} (hd : 0 < d) :
    Summable (fun n : ℤ => ∫ y : ℝ × ℝ, Ψ y * Φ (y.1 + (n : ℝ) * d, y.2)) ∧
    ∫ x in B0579.cell d, perSum d Ψ x * perSum d Φ x =
      ∑' n : ℤ, ∫ y : ℝ × ℝ, Ψ y * Φ (y.1 + (n : ℝ) * d, y.2) := by
  set K : ℝ := |C1| * |C2| * (2080 * Real.pi)
  set Fn : ℤ → ℝ × ℝ → ℂ := fun n y => Ψ y * Φ (y.1 + (n : ℝ) * d, y.2) with hFn
  have hint : ∀ n, Integrable (Fn n) := fun n => (cross_int hΨc hΦc hΨ hΦ ((n : ℝ) * d)).1
  have hnorm : ∀ n, ∫ y, ‖Fn n y‖ ≤ K / (1 + |(n : ℝ) * d|) ^ 2 := fun n =>
    (cross_int hΨc hΦc hΨ hΦ ((n : ℝ) * d)).2
  have hb := summable_cross_bound (K := K) hd
  have hsumI : Summable (fun n => ∫ y, ‖Fn n y‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hnorm hb
  have hsum : Summable (fun n : ℤ => ∫ y : ℝ × ℝ, Ψ y * Φ (y.1 + (n : ℝ) * d, y.2)) :=
    hsumI.of_norm_bounded fun n => norm_integral_le_integral_norm _
  have hPdSum : ∀ y : ℝ × ℝ, Summable (fun n : ℤ => Φ (y.1 + n * d, y.2)) := fun y =>
    (summable_shift hΦ hd y).of_norm
  have hPdMeas : Measurable (perSum d Φ) := measurable_perSum hΦc hPdSum
  have hFsum : ∀ y, Ψ y * perSum d Φ y = ∑' n : ℤ, Fn n y := by
    intro y
    simp only [perSum, hFn]
    exact tsum_mul_left.symm
  have hlin : ∀ n, ∫⁻ y, ‖Fn n y‖ₑ = ENNReal.ofReal (∫ y, ‖Fn n y‖) := fun n =>
    (ofReal_integral_norm_eq_lintegral_enorm (hint n)).symm
  have hsumL : ∑' n, ∫⁻ y, ‖Fn n y‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun y => norm_nonneg _) hsumI]
    exact ENNReal.ofReal_ne_top
  have hmeasF : ∀ n, AEStronglyMeasurable (Fn n) volume := fun n => (hint n).1
  have hInt : Integrable (fun y => ∑' n, Fn n y) := by
    refine ⟨?_, ?_⟩
    · have : (fun y => ∑' n, Fn n y) = fun y => Ψ y * perSum d Φ y :=
        funext fun y => (hFsum y).symm
      rw [this]
      exact (hΨc.measurable.mul hPdMeas).aestronglyMeasurable
    · calc ∫⁻ y, ‖∑' n, Fn n y‖ₑ ≤ ∫⁻ y, ∑' n, ‖Fn n y‖ₑ :=
            lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ y, ‖Fn n y‖ₑ := lintegral_tsum (fun n => (hmeasF n).enorm)
        _ < ⊤ := lt_top_iff_ne_top.2 hsumL
  have hcell : ∫ x in B0579.cell d, perSum d Ψ x * perSum d Φ x = ∫ y, ∑' n, Fn n y := by
    have h1 : ∀ x : ℝ × ℝ,
        perSum d Ψ x * perSum d Φ x = perSum d (fun y => ∑' n, Fn n y) x := by
      intro x
      simp only [perSum]
      rw [← tsum_mul_right]
      refine tsum_congr fun m => ?_
      rw [← hFsum]
      congr 1
      exact (perSum_int_period d Φ m x).symm
    rw [← integral_bcell_perSum hInt hd]
    exact setIntegral_congr_fun (measurableSet_Ico.prod MeasurableSet.univ) fun x _ => h1 x
  refine ⟨hsum, ?_⟩
  rw [hcell, integral_tsum hmeasF hsumL]

/-- **`O(d⁻²)` tail** (SP 2893-2897): for `d ≥ 1` the periodized pairing differs from the planar
pairing by at most `K / d²`, `K = |C₁||C₂| 2080π Σ_n n⁻²`. -/
theorem sub_zero_term_bound (hΨc : Continuous Ψ) (hΦc : Continuous Φ) {C1 C2 : ℝ}
    (hΨ : ∀ y : ℝ × ℝ, ‖Ψ y‖ ≤ C1 * (1 + |y.1| + |y.2|)⁻¹ ^ 2)
    (hΦ : ∀ y : ℝ × ℝ, ‖Φ y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) {d : ℝ} (hd : 1 ≤ d) :
    ‖(∫ x in B0579.cell d, perSum d Ψ x * perSum d Φ x) - ∫ y : ℝ × ℝ, Ψ y * Φ y‖ ≤
      (|C1| * |C2| * (2080 * Real.pi) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2) / d ^ 2 := by
  set K : ℝ := |C1| * |C2| * (2080 * Real.pi) with hK
  have hK0 : 0 ≤ K := by positivity
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hsum, hunf⟩ := unfold hΨc hΦc hΨ hΦ hdpos
  set T : ℤ → ℂ := fun n => ∫ y : ℝ × ℝ, Ψ y * Φ (y.1 + (n : ℝ) * d, y.2) with hT
  have hsplit := hsum.tsum_eq_add_tsum_ite 0
  have h0 : T 0 = ∫ y : ℝ × ℝ, Ψ y * Φ y := by
    simp [hT]
  have hrest : (∫ x in B0579.cell d, perSum d Ψ x * perSum d Φ x) - ∫ y : ℝ × ℝ, Ψ y * Φ y =
      ∑' n : ℤ, (if n = 0 then (0 : ℂ) else T n) := by
    rw [hunf, hsplit, h0, add_sub_cancel_left]
  rw [hrest]
  have hS : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hterm : ∀ n : ℤ, ‖(if n = 0 then (0 : ℂ) else T n)‖ ≤ K / d ^ 2 * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, ↓reduceIte]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hb : ‖T n‖ ≤ K / (1 + |(n : ℝ) * d|) ^ 2 :=
        (norm_integral_le_integral_norm _).trans (cross_int hΨc hΦc hΨ hΦ ((n : ℝ) * d)).2
      have hnd : (0 : ℝ) < ((n : ℝ) * d) ^ 2 := by
        have : (n : ℝ) * d ≠ 0 := mul_ne_zero hnR hdpos.ne'
        positivity
      calc ‖T n‖ ≤ K / (1 + |(n : ℝ) * d|) ^ 2 := hb
        _ ≤ K / ((n : ℝ) * d) ^ 2 := by
            apply div_le_div_of_nonneg_left hK0 hnd
            nlinarith [sq_abs ((n : ℝ) * d), abs_nonneg ((n : ℝ) * d)]
        _ = K / d ^ 2 * (1 / (n : ℝ) ^ 2) := by field_simp
  have hnorm : Summable (fun n : ℤ => ‖(if n = 0 then (0 : ℂ) else T n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hS.mul_left _)
  calc ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else T n)‖
      ≤ ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else T n)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ, K / d ^ 2 * (1 / (n : ℝ) ^ 2) := hnorm.tsum_le_tsum hterm (hS.mul_left _)
    _ = K / d ^ 2 * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := tsum_mul_left
    _ = (K * ∑' n : ℤ, 1 / (n : ℝ) ^ 2) / d ^ 2 := by ring

end UnforcedLeray.Short.IIIa.OscGramDual
