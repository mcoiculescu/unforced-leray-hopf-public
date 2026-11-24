import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I, task `PartI:T01/constZero`: the constant in the mean stream equation vanishes

Pure real analysis, the leaf `ConstZeroLemma` of `Sub/T01.lean`. Source of record:
`the November 2 reference manuscript`, lines 397-404: the constant `C` in
`S_s - ν S_ηη - g = C` vanishes.

Proof sketch. Suppose `C ≠ 0`. Since `a → 0` at `+∞`, there is `R0` with `|a x| ≤ |C|/4` for
`x ≥ R0`. The function `ν b` has derivative `a - g - C`, so for `R ≥ R0`

  `ν (b R - b R0) = ∫_{R0}^R a - ∫_{R0}^R g - C (R - R0)`,

and `|∫_{R0}^R a| ≤ |C|/4 (R - R0)`, `|∫_{R0}^R g| ≤ ∫ |g|` give
`ν |b R| ≥ (3/4)|C| R - const`. Hence `|b R| ≥ 1` for all large `R`, so `b² ≥ 1` on a half-line,
contradicting `b² ∈ L¹` (from `b ∈ L²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

theorem constZeroLemma : ConstZeroLemma := by
  unfold ConstZeroLemma
  intro ν C a b b' g hν hb ha hg hbL2 hta hEq
  by_contra hC
  have hCpos : 0 < |C| := abs_pos.2 hC
  -- Step 1: `a` is eventually at most `|C|/4` in absolute value
  have hev_a : ∀ᶠ x in atTop, |a x| ≤ |C| / 4 := by
    filter_upwards [(Metric.tendsto_nhds.1 hta) (|C| / 4) (div_pos hCpos (by norm_num))]
      with x hx
    rw [Real.dist_eq, sub_zero] at hx
    exact hx.le
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 hev_a
  -- Step 2: `ν b` has derivative `a - g - C`
  have hD : ∀ x, HasDerivAt (fun y => ν * b y) (a x - g x - C) x := fun x =>
    ((hb x).const_mul ν).congr_deriv (by linarith [hEq x])
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun x => a x - g x - C) volume u v := fun u v =>
    ((ha.intervalIntegrable u v).sub hg.intervalIntegrable).sub intervalIntegrable_const
  -- Step 3: fundamental theorem of calculus
  have hFTC : ∀ R : ℝ, ∫ x in R0..R, (a x - g x - C) = ν * b R - ν * b R0 := fun R => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) (hint R0 R)]
  -- Step 4: split the integral
  have hsplit : ∀ R : ℝ, ∫ x in R0..R, (a x - g x - C) =
      (∫ x in R0..R, a x) - (∫ x in R0..R, g x) - C * (R - R0) := fun R => by
    rw [intervalIntegral.integral_sub ((ha.intervalIntegrable R0 R).sub hg.intervalIntegrable)
        intervalIntegrable_const,
      intervalIntegral.integral_sub (ha.intervalIntegrable R0 R) hg.intervalIntegrable,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- Step 5: bounds on the two pieces
  have hKg : ∀ R : ℝ, R0 ≤ R → ‖∫ x in R0..R, g x‖ ≤ ∫ x, ‖g x‖ := fun R hR => by
    refine (intervalIntegral.norm_integral_le_integral_norm hR).trans ?_
    rw [intervalIntegral.integral_of_le hR]
    exact setIntegral_le_integral hg.norm (ae_of_all _ fun x => norm_nonneg (g x))
  have hIa : ∀ R : ℝ, R0 ≤ R → ‖∫ x in R0..R, a x‖ ≤ |C| / 4 * (R - R0) := by
    intro R hR
    have hx : ∀ x ∈ Set.uIoc R0 R, ‖a x‖ ≤ |C| / 4 := by
      intro x hx
      rw [Set.uIoc_of_le hR] at hx
      rw [Real.norm_eq_abs]
      exact hR0 x hx.1.le
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := a) hx
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ R - R0)] at h
    exact h
  -- Step 6: the key lower bound for `ν |b R|`
  have hkey : ∀ R : ℝ, R0 ≤ R →
      (3 / 4 * |C|) * R - ((3 / 4 * |C|) * R0 + (∫ x, ‖g x‖) + ν * |b R0|) ≤ ν * |b R| := by
    intro R hR
    have hG := hKg R hR
    have hA := hIa R hR
    rw [Real.norm_eq_abs] at hG hA
    obtain ⟨hA1, hA2⟩ := abs_le.1 hA
    obtain ⟨hG1, hG2⟩ := abs_le.1 hG
    have hFT := hFTC R
    have hSp := hsplit R
    have h1 : ν * (-b R) ≤ ν * |b R| := by
      have : -b R ≤ |b R| := by rw [← abs_neg]; exact le_abs_self _
      exact mul_le_mul_of_nonneg_left this hν.le
    have h2 : ν * (-b R0) ≤ ν * |b R0| := by
      have : -b R0 ≤ |b R0| := by rw [← abs_neg]; exact le_abs_self _
      exact mul_le_mul_of_nonneg_left this hν.le
    have h3 : ν * b R ≤ ν * |b R| := mul_le_mul_of_nonneg_left (le_abs_self _) hν.le
    have h4 : ν * b R0 ≤ ν * |b R0| := mul_le_mul_of_nonneg_left (le_abs_self _) hν.le
    rcases abs_cases C with ⟨hCa, _⟩ | ⟨hCa, _⟩
    · simp only [hCa] at hA2 ⊢
      linarith
    · simp only [hCa] at hA1 hA2 ⊢
      linarith
  -- Step 7: `|b R| ≥ 1` eventually
  have hlim : Tendsto (fun R : ℝ => (3 / 4 * |C|) * R) atTop atTop :=
    Tendsto.const_mul_atTop (mul_pos (by norm_num) hCpos) tendsto_id
  have hev_lin : ∀ᶠ R in atTop,
      (3 / 4 * |C|) * R0 + (∫ x, ‖g x‖) + ν * |b R0| + ν ≤ (3 / 4 * |C|) * R :=
    hlim.eventually_ge_atTop _
  have hev : ∀ᶠ R in atTop, 1 ≤ |b R| := by
    filter_upwards [hev_lin, eventually_ge_atTop R0] with R hR1 hR2
    have hk := hkey R hR2
    have h5 : ν * 1 ≤ ν * |b R| := by linarith
    exact le_of_mul_le_mul_left h5 hν
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  -- Step 8: `b²` is integrable, but bounded below by `1` on `[X, ∞)`
  have hsq : Integrable (fun x => b x ^ 2) volume :=
    (memLp_two_iff_integrable_sq hbL2.aestronglyMeasurable).1 hbL2
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici X) volume := by
    refine Integrable.mono' hsq.integrableOn aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have h1 := hX x (Set.mem_Ici.1 hx)
    simp only [Real.norm_eq_abs, abs_one]
    nlinarith [sq_abs (b x), abs_nonneg (b x)]
  have hfin : volume (Ici X) < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℝ))).1 hconst with h | h
    · simp at h
    · exact h
  rw [Real.volume_Ici] at hfin
  exact lt_irrefl _ hfin

end UnforcedLeray.Short.PartI
