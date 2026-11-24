import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Leaf (c) helper: `X_{m,d}` duality against bounded band-supported tests

Source `the November 2 reference manuscript` lines 2823-2826 (duality of
`X_{m,d}` and `X_{-m,d}` under the unweighted pairing), 2953-2958.

For a measurable `F`, if `|∫_{C_d} F Φ| ≤ A ‖Φ‖_{X_{-m,d}}` for every bounded measurable `Φ`
vanishing for `|η|` large, then `‖F‖_{X_{m,d}} ≤ A`: test with
`Φ_n = 1_{S_n} conj(F) ⟨y⟩^{2m}`, `S_n = C_d ∩ {|F| ≤ n, |η| ≤ n}`, and let `n → ∞`
(monotone convergence).  No a priori finiteness of `‖F‖_{X_{m,d}}` is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf3Aux

open UnforcedLeray.Short.IIIa

/-- The weighted `L²` integral against `cellMeasure` as a set integral with the density
`⟨y⟩^{2m}`. -/
theorem lintegral_cellMeasure (d m : ℝ) {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂(B0579.cellMeasure d m) =
      ∫⁻ y in B0579.cell d, ENNReal.ofReal (B0579.jb y ^ m) * g y := by
  rw [B0579.cellMeasure, lintegral_withDensity_eq_lintegral_mul _
    (B0579.measurable_density m).coe_nnreal_ennreal hg]
  rfl

theorem xNorm_sq_eq (d m : ℝ) {F : ℝ × ℝ → ℂ} (hF : Measurable F) :
    xNorm d m F ^ 2 = ∫⁻ y in B0579.cell d, ENNReal.ofReal (B0579.jb y ^ m) * ‖F y‖ₑ ^ 2 := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hpow : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    intro X
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]
  rw [one_div, ← one_div, hpow]
  exact lintegral_cellMeasure d m ((hF.enorm).pow_const 2)

theorem sq_le_of_le_mul {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A) (h : s ^ 2 ≤ A * s) :
    s ^ 2 ≤ A ^ 2 := by
  rcases eq_or_lt_of_le hs with h0 | h0
  · nlinarith [sq_nonneg A, h0]
  · have : s ≤ A := by nlinarith
    nlinarith

/-- **Duality against bounded band-supported tests.** -/
theorem xNorm_le_of_pairing {d m A : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ A) {F : ℝ × ℝ → ℂ}
    (hF : StronglyMeasurable F)
    (hpair : ∀ Φ : ℝ × ℝ → ℂ, StronglyMeasurable Φ → ∀ B R : ℝ, (∀ y, ‖Φ y‖ ≤ B) →
      (∀ y, R < |y.2| → Φ y = 0) →
      ‖∫ y in B0579.cell d, F y * Φ y‖ ≤ A * (xNorm d (-m) Φ).toReal) :
    xNorm d m F ≤ ENNReal.ofReal A := by
  have hFm : Measurable F := hF.measurable
  set S : ℕ → Set (ℝ × ℝ) := fun n => B0579.cell d ∩ {y | ‖F y‖ ≤ n ∧ |y.2| ≤ n} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (B0579.measurableSet_cell d).inter
      ((measurableSet_le hFm.norm measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))
  set w : ℝ × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (B0579.jb y ^ m) * ‖F y‖ₑ ^ 2 with hw
  have hwm : Measurable w :=
    (ENNReal.measurable_ofReal.comp (B0579.continuous_jb_rpow m).measurable).mul
      ((hFm.enorm).pow_const 2)
  set I : ℕ → ℝ≥0∞ := fun n => ∫⁻ y in B0579.cell d, (S n).indicator w y with hI
  -- the bound on each truncation
  have hIb : ∀ n : ℕ, I n ≤ ENNReal.ofReal (A ^ 2) := by
    intro n
    set Φ : ℝ × ℝ → ℂ :=
      (S n).indicator (fun y => conj (F y) * ((B0579.jb y ^ m : ℝ) : ℂ)) with hΦ
    have hΦs : StronglyMeasurable Φ :=
      ((Complex.continuous_conj.comp_stronglyMeasurable hF).mul
        (Complex.continuous_ofReal.comp
          (B0579.continuous_jb_rpow m)).stronglyMeasurable).indicator (hSm n)
    set Bd : ℝ := (1 + (d / 2) ^ 2 + (n : ℝ) ^ 2) ^ m with hBd
    have hBd0 : 0 ≤ Bd := Real.rpow_nonneg (by positivity) m
    have hjb : ∀ y ∈ S n, B0579.jb y ^ m ≤ Bd := by
      intro y hy
      obtain ⟨⟨⟨h1, h2⟩, -⟩, -, h3⟩ := hy
      refine Real.rpow_le_rpow (B0579.jb_pos y).le ?_ hm
      have hy1 : y.1 ^ 2 ≤ (d / 2) ^ 2 := by nlinarith
      have hy2 : y.2 ^ 2 ≤ (n : ℝ) ^ 2 := by
        have := abs_nonneg y.2
        nlinarith [sq_abs y.2]
      unfold B0579.jb
      linarith
    have hΦb : ∀ y, ‖Φ y‖ ≤ n * Bd := by
      intro y
      by_cases hy : y ∈ S n
      · rw [hΦ, indicator_of_mem hy, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le m)]
        exact mul_le_mul hy.2.1 (hjb y hy) (Real.rpow_nonneg (B0579.jb_pos y).le m)
          (Nat.cast_nonneg n)
      · rw [hΦ, indicator_of_notMem hy, norm_zero]
        positivity
    have hΦv : ∀ y, (n : ℝ) < |y.2| → Φ y = 0 := by
      intro y hy
      have : y ∉ S n := fun h => absurd h.2.2 (not_le.2 hy)
      rw [hΦ, indicator_of_notMem this]
    have hP := hpair Φ hΦs (n * Bd) n hΦb hΦv
    -- the pairing is `I n`
    set fR : ℝ × ℝ → ℝ := (S n).indicator (fun y => ‖F y‖ ^ 2 * B0579.jb y ^ m) with hfR
    have hFΦ : ∀ y, F y * Φ y = ((fR y : ℝ) : ℂ) := by
      intro y
      by_cases hy : y ∈ S n
      · rw [hΦ, hfR, indicator_of_mem hy, indicator_of_mem hy, ← mul_assoc, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        push_cast
        ring
      · rw [hΦ, hfR, indicator_of_notMem hy, indicator_of_notMem hy]
        simp
    have hfRnn : ∀ y, 0 ≤ fR y := by
      intro y
      rw [hfR]
      by_cases hy : y ∈ S n
      · rw [indicator_of_mem hy]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos y).le m)
      · rw [indicator_of_notMem hy]
    have hfRm : Measurable fR :=
      ((hFm.norm.pow_const 2).mul (B0579.continuous_jb_rpow m).measurable).indicator (hSm n)
    have hofR : ∀ y, ENNReal.ofReal (fR y) = (S n).indicator w y := by
      intro y
      rw [hfR]
      by_cases hy : y ∈ S n
      · rw [indicator_of_mem hy, indicator_of_mem hy, hw]
        dsimp only
        rw [mul_comm,
          ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos y).le m),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]
    have hint : ∫ y in B0579.cell d, F y * Φ y = (((I n).toReal : ℝ) : ℂ) := by
      rw [show (fun y => F y * Φ y) = fun y => ((fR y : ℝ) : ℂ) from funext hFΦ,
        integral_complex_ofReal]
      congr 1
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfRnn)
        hfRm.aestronglyMeasurable]
      rw [hI]
      congr 1
      exact lintegral_congr hofR
    -- the norm of `Φ` is `I n ^ (1/2)`
    have hnorm : xNorm d (-m) Φ ^ 2 = I n := by
      rw [xNorm_sq_eq d (-m) hΦs.measurable, hI]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ S n
      · rw [hΦ, indicator_of_mem hy, indicator_of_mem hy, hw]
        dsimp only
        have hj := B0579.jb_pos y
        have hjm : 0 ≤ B0579.jb y ^ m := Real.rpow_nonneg hj.le m
        have e1 : ‖conj (F y) * ((B0579.jb y ^ m : ℝ) : ℂ)‖ₑ ^ 2 =
            ENNReal.ofReal (‖F y‖ ^ 2 * (B0579.jb y ^ m) ^ 2) := by
          rw [← ofReal_norm, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hjm, ← ENNReal.ofReal_pow (by positivity)]
          ring_nf
        rw [e1, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hj.le _),
          ← ENNReal.ofReal_mul hjm]
        congr 1
        have hneg : B0579.jb y ^ (-m) * B0579.jb y ^ m = 1 := by
          rw [Real.rpow_neg hj.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hj m).ne']
        calc B0579.jb y ^ (-m) * (‖F y‖ ^ 2 * (B0579.jb y ^ m) ^ 2)
            = (B0579.jb y ^ (-m) * B0579.jb y ^ m) * (B0579.jb y ^ m * ‖F y‖ ^ 2) := by ring
          _ = B0579.jb y ^ m * ‖F y‖ ^ 2 := by rw [hneg, one_mul]
      · rw [hΦ, indicator_of_notMem hy, indicator_of_notMem hy]
        simp
    -- `I n` is finite
    have hfin : I n ≠ ⊤ := by
      have hb : ∀ y, (S n).indicator w y ≤
          (B0579.box d n).indicator (fun _ => ENNReal.ofReal (Bd * (n : ℝ) ^ 2)) y := by
        intro y
        by_cases hy : y ∈ S n
        · have hbox : y ∈ B0579.box d n := B0579.mem_box_of_mem_cell hy.1 hy.2.2
          rw [indicator_of_mem hy, indicator_of_mem hbox, hw]
          dsimp only
          rw [← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos y).le m)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul (hjb y hy) ?_ (sq_nonneg _) hBd0)
          exact pow_le_pow_left₀ (norm_nonneg _) hy.2.1 2
        · rw [indicator_of_notMem hy]
          exact zero_le
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
      rw [lintegral_indicator_const (B0579.isCompact_box d n).measurableSet]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      rw [Measure.restrict_apply (B0579.isCompact_box d n).measurableSet]
      exact ne_top_of_le_ne_top (B0579.isCompact_box d n).measure_lt_top.ne
        (measure_mono inter_subset_left)
    -- conclude
    have hnorm' : ((xNorm d (-m) Φ).toReal) ^ 2 = (I n).toReal := by
      rw [← ENNReal.toReal_pow, hnorm]
    rw [hint, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ← hnorm'] at hP
    have hsq := sq_le_of_le_mul ENNReal.toReal_nonneg hA hP
    rw [hnorm'] at hsq
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hsq
  -- monotone convergence
  have hsup : xNorm d m F ^ 2 = ⨆ n, I n := by
    rw [xNorm_sq_eq d m hFm, hI]
    rw [← lintegral_iSup (fun n => hwm.indicator (hSm n)) ?_]
    · refine setLIntegral_congr_fun (B0579.measurableSet_cell d) fun y hy => ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (max ‖F y‖ |y.2|)
      have hyN : y ∈ S N := ⟨hy, le_trans (le_max_left _ _) hN, le_trans (le_max_right _ _) hN⟩
      refine le_antisymm (le_iSup_of_le N (by rw [indicator_of_mem hyN])) (iSup_le fun n => ?_)
      exact indicator_le_self _ _ y
    · intro a b hab y
      refine indicator_le_indicator_of_subset ?_ (fun _ => zero_le) y
      intro x hx
      exact ⟨hx.1, le_trans hx.2.1 (by exact_mod_cast hab),
        le_trans hx.2.2 (by exact_mod_cast hab)⟩
  have hle : xNorm d m F ^ 2 ≤ ENNReal.ofReal A ^ 2 := by
    rw [hsup, ← ENNReal.ofReal_pow hA]
    exact iSup_le hIb
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf3Aux
