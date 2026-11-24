import UnforcedLeray.Units.B0079.CauchySchwarz
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Unit B0079, helper: the two Cauchy–Schwarz estimates of `eq:st18-t00060`

Blueprint unit `B0079`, `paper/main.tex` lines 1374–1379. For a profile `w` with
`N² = ∫₀^∞ |w|² (1+s²)^M s ds < ∞`, the two integrals of the Green formula are estimated by
`setIntegral_mul_norm_le` (weight `⟨s⟩^{2M} s ds`), with explicit majorants `q` whose integrals
are computed exactly:

* inner integral `∫₀^r s^{n+1} |w|`: `inner_near` (any `r > 0`, `q = s^{2n+1}`),
  `inner_far_lt` (`M < n+1`, `q = s^{2n+1-2M}`), `inner_far_ge` (`M ≥ n+1`, `q = s/(1+s²)`);
* outer integral `∫_r^∞ s^{1-n} |w|`: `outer_far` (`M > 1`, `q = s^{1-2n-2M}`),
  `outer_near` (`n ≥ 2`, `q = s^{1-2n}`), `outer_near_one` (`n = 1`, `r ≤ 1`, split at `1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.B0079

variable {M : ℝ} {w : ℝ → ℂ}

theorem one_le_one_add_sq_rpow {M : ℝ} (hM : 0 ≤ M) (s : ℝ) : 1 ≤ (1 + s ^ 2) ^ M :=
  Real.one_le_rpow (by nlinarith [sq_nonneg s]) hM

theorem rpow_le_one_add_sq_rpow {M s : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) :
    s ^ (2 * M) ≤ (1 + s ^ 2) ^ M := by
  rw [Real.rpow_mul hs, Real.rpow_two]
  exact Real.rpow_le_rpow (by positivity) (by linarith) hM

/-! ### The inner integral `∫₀^r s^{n+1} |w(s)| ds` -/

/-- For every `r > 0`: `∫₀^r s^{n+1}|w| ≤ (r^{2n+2}/(2n+2))^{1/2} N`. -/
theorem inner_near (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    (hM : 0 ≤ M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s => s ^ (n + 1) * ‖w s‖) (Ioc 0 r) ∧
      ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
        √(r ^ (2 * n + 2) / (2 * n + 2)) *
          √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  have hq : IntegrableOn (fun s : ℝ => s ^ (2 * n + 1)) (Ioc 0 r) :=
    (continuous_pow _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : ∫ s in Ioc 0 r, s ^ (2 * n + 1) = r ^ (2 * n + 2) / (2 * n + 2) := by
    rw [← intervalIntegral.integral_of_le hr.le, integral_pow]
    norm_num
    ring
  have hpq : ∀ s ∈ Ioc (0 : ℝ) r, (s ^ (n + 1)) ^ 2 ≤ s ^ (2 * n + 1) * ((1 + s ^ 2) ^ M * s) :=
    fun s hs => by
      calc (s ^ (n + 1)) ^ 2 = s ^ (2 * n + 1) * (1 * s) := by ring
        _ ≤ s ^ (2 * n + 1) * ((1 + s ^ 2) ^ M * s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (one_le_one_add_sq_rpow hM s) hs.1.le)
            (pow_nonneg hs.1.le _)
  have h := setIntegral_mul_norm_le hwm hwi measurableSet_Ioc (fun s hs => hs.1)
    (p := fun s => s ^ (n + 1)) (q := fun s => s ^ (2 * n + 1))
    (continuous_pow _).aestronglyMeasurable (fun s hs => pow_nonneg hs.1.le _) hq
    (fun s hs => pow_nonneg hs.1.le _) hpq
  rw [hint] at h
  exact h

/-- For `M < n + 1` and `r > 0`: `∫₀^r s^{n+1}|w| ≤ (r^{α}/α)^{1/2} N`, `α = 2n+2-2M > 0`. -/
theorem inner_far_lt (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    (hM0 : 0 ≤ M) {n : ℕ} (hM : M < n + 1) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
      √(r ^ ((2 : ℝ) * n + 2 - 2 * M) / ((2 : ℝ) * n + 2 - 2 * M)) *
        √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  set β : ℝ := (2 : ℝ) * n + 1 - 2 * M with hβ
  have hβ1 : -1 < β := by rw [hβ]; linarith
  have hβe : β + 1 = (2 : ℝ) * n + 2 - 2 * M := by rw [hβ]; ring
  have hq : IntegrableOn (fun s : ℝ => s ^ β) (Ioc 0 r) :=
    (intervalIntegral.intervalIntegrable_rpow' hβ1 (a := 0) (b := r)).1
  have hint : ∫ s in Ioc 0 r, s ^ β = r ^ ((2 : ℝ) * n + 2 - 2 * M) / ((2 : ℝ) * n + 2 - 2 * M) := by
    rw [← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl hβ1), hβe,
      Real.zero_rpow (by linarith), sub_zero]
  have hpq : ∀ s ∈ Ioc (0 : ℝ) r, (s ^ (n + 1)) ^ 2 ≤ s ^ β * ((1 + s ^ 2) ^ M * s) :=
    fun s hs => by
      have hs0 := hs.1
      have e : s ^ β * (s ^ (2 * M) * s) = (s ^ (n + 1)) ^ 2 := by
        rw [← mul_assoc, ← Real.rpow_add hs0, ← Real.rpow_add_one hs0.ne', ← pow_mul,
          ← Real.rpow_natCast]
        congr 1
        rw [hβ]; push_cast; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (rpow_le_one_add_sq_rpow hM0 hs0.le) hs0.le)
        (Real.rpow_nonneg hs0.le _)
  have h := setIntegral_mul_norm_le hwm hwi measurableSet_Ioc (fun s hs => hs.1)
    (p := fun s => s ^ (n + 1)) (q := fun s => s ^ β)
    (continuous_pow _).aestronglyMeasurable (fun s hs => pow_nonneg hs.1.le _) hq
    (fun s hs => Real.rpow_nonneg hs.1.le _) hpq
  rw [hint] at h
  exact h.2

/-- For `M ≥ n + 1` and `r > 0`: `∫₀^r s^{n+1}|w| ≤ (log(1+r²)/2)^{1/2} N`. -/
theorem inner_far_ge (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    {n : ℕ} (hM : (n : ℝ) + 1 ≤ M) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioc 0 r, s ^ (n + 1) * ‖w s‖ ≤
      √(Real.log (1 + r ^ 2) / 2) * √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  have hc : Continuous fun s : ℝ => s / (1 + s ^ 2) :=
    continuous_id.div (continuous_const.add (continuous_pow 2)) fun s => by positivity
  have hq : IntegrableOn (fun s : ℝ => s / (1 + s ^ 2)) (Ioc 0 r) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : ∫ s in Ioc 0 r, s / (1 + s ^ 2) = Real.log (1 + r ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hr.le]
    have hd : ∀ x ∈ uIcc (0 : ℝ) r, HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 2) / 2)
        (x / (1 + x ^ 2)) x := fun x _ => by
      have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x).const_add 1
      have h2 := (h1.log (by positivity)).div_const 2
      exact h2.congr_deriv (by field_simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
    simp
  have hpq : ∀ s ∈ Ioc (0 : ℝ) r,
      (s ^ (n + 1)) ^ 2 ≤ s / (1 + s ^ 2) * ((1 + s ^ 2) ^ M * s) := fun s hs => by
    have hpos : 0 < 1 + s ^ 2 := by positivity
    have h1 := Real.rpow_add_one hpos.ne' (M - 1)
    rw [sub_add_cancel] at h1
    have h2 : (1 + s ^ 2) ^ n ≤ (1 + s ^ 2) ^ (M - 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg s]) (by linarith)
    have h3 : (s ^ 2) ^ n ≤ (1 + s ^ 2) ^ n :=
      pow_le_pow_left₀ (sq_nonneg s) (by linarith) n
    calc (s ^ (n + 1)) ^ 2 = s ^ 2 * (s ^ 2) ^ n := by ring
      _ ≤ s ^ 2 * (1 + s ^ 2) ^ (M - 1) :=
          mul_le_mul_of_nonneg_left (h3.trans h2) (sq_nonneg s)
      _ = s / (1 + s ^ 2) * ((1 + s ^ 2) ^ M * s) := by
          rw [h1]; field_simp
  have h := setIntegral_mul_norm_le hwm hwi measurableSet_Ioc (fun s hs => hs.1)
    (p := fun s => s ^ (n + 1)) (q := fun s => s / (1 + s ^ 2))
    (continuous_pow _).aestronglyMeasurable (fun s hs => pow_nonneg hs.1.le _) hq
    (fun s hs => div_nonneg hs.1.le (by positivity)) hpq
  rw [hint] at h
  exact h.2

/-! ### The outer integral `∫_r^∞ s^{1-n} |w(s)| ds` -/

/-- For `M > 1` and `r > 0`: `∫_r^∞ s^{1-n}|w| ≤ (r^{2-2n-2M}/(2n+2M-2))^{1/2} N`. -/
theorem outer_far (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s => s ^ (1 - (n : ℝ)) * ‖w s‖) (Ioi r) ∧
      ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
        √(r ^ ((2 : ℝ) - 2 * n - 2 * M) / ((2 : ℝ) * n + 2 * M - 2)) *
          √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  set a : ℝ := (1 : ℝ) - 2 * n - 2 * M with ha
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : a < -1 := by rw [ha]; linarith
  have hq : IntegrableOn (fun s : ℝ => s ^ a) (Ioi r) := integrableOn_Ioi_rpow_of_lt ha1 hr
  have hint : ∫ s in Ioi r, s ^ a = r ^ ((2 : ℝ) - 2 * n - 2 * M) / ((2 : ℝ) * n + 2 * M - 2) := by
    rw [integral_Ioi_rpow_of_lt ha1 hr]
    have e1 : a + 1 = (2 : ℝ) - 2 * n - 2 * M := by rw [ha]; ring
    have e2 : (2 : ℝ) * n + 2 * M - 2 = -((2 : ℝ) - 2 * n - 2 * M) := by ring
    rw [e1, e2, div_neg, neg_div]
  have hA0 : Ioi r ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hr.le
  have hpq : ∀ s ∈ Ioi r, (s ^ (1 - (n : ℝ))) ^ 2 ≤ s ^ a * ((1 + s ^ 2) ^ M * s) :=
    fun s hs => by
      have hs0 : 0 < s := hr.trans hs
      have e : s ^ a * (s ^ (2 * M) * s) = (s ^ (1 - (n : ℝ))) ^ 2 := by
        rw [← mul_assoc, ← Real.rpow_add hs0, ← Real.rpow_add_one hs0.ne', sq,
          ← Real.rpow_add hs0]
        congr 1
        rw [ha]; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (rpow_le_one_add_sq_rpow (by linarith) hs0.le) hs0.le)
        (Real.rpow_nonneg hs0.le _)
  have hpm : AEStronglyMeasurable (fun s : ℝ => s ^ (1 - (n : ℝ))) (volume.restrict (Ioi r)) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hr.trans hx))).aestronglyMeasurable
      measurableSet_Ioi
  have h := setIntegral_mul_norm_le hwm hwi measurableSet_Ioi hA0
    (p := fun s => s ^ (1 - (n : ℝ))) (q := fun s => s ^ a) hpm
    (fun s hs => Real.rpow_nonneg (hr.trans hs).le _) hq
    (fun s hs => Real.rpow_nonneg (hr.trans hs).le _) hpq
  rw [hint] at h
  exact h

/-- For `n ≥ 2` and every `r > 0`: `∫_r^∞ s^{1-n}|w| ≤ (r^{2-2n}/(2n-2))^{1/2} N`. -/
theorem outer_near (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    (hM : 0 ≤ M) {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioi r, s ^ (1 - (n : ℝ)) * ‖w s‖ ≤
      √(r ^ ((2 : ℝ) - 2 * n) / ((2 : ℝ) * n - 2)) *
        √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  set a : ℝ := (1 : ℝ) - 2 * n with ha
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 : a < -1 := by rw [ha]; linarith
  have hq : IntegrableOn (fun s : ℝ => s ^ a) (Ioi r) := integrableOn_Ioi_rpow_of_lt ha1 hr
  have hint : ∫ s in Ioi r, s ^ a = r ^ ((2 : ℝ) - 2 * n) / ((2 : ℝ) * n - 2) := by
    rw [integral_Ioi_rpow_of_lt ha1 hr]
    have e1 : a + 1 = (2 : ℝ) - 2 * n := by rw [ha]; ring
    have e2 : (2 : ℝ) * n - 2 = -((2 : ℝ) - 2 * n) := by ring
    rw [e1, e2, div_neg, neg_div]
  have hA0 : Ioi r ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hr.le
  have hpq : ∀ s ∈ Ioi r, (s ^ (1 - (n : ℝ))) ^ 2 ≤ s ^ a * ((1 + s ^ 2) ^ M * s) :=
    fun s hs => by
      have hs0 : 0 < s := hr.trans hs
      have e : s ^ a * (1 * s) = (s ^ (1 - (n : ℝ))) ^ 2 := by
        rw [one_mul, ← Real.rpow_add_one hs0.ne', sq, ← Real.rpow_add hs0]
        congr 1
        rw [ha]; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (one_le_one_add_sq_rpow hM s) hs0.le)
        (Real.rpow_nonneg hs0.le _)
  have hpm : AEStronglyMeasurable (fun s : ℝ => s ^ (1 - (n : ℝ))) (volume.restrict (Ioi r)) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hr.trans hx))).aestronglyMeasurable
      measurableSet_Ioi
  have h := setIntegral_mul_norm_le hwm hwi measurableSet_Ioi hA0
    (p := fun s => s ^ (1 - (n : ℝ))) (q := fun s => s ^ a) hpm
    (fun s hs => Real.rpow_nonneg (hr.trans hs).le _) hq
    (fun s hs => Real.rpow_nonneg (hr.trans hs).le _) hpq
  rw [hint] at h
  exact h.2

/-- For `n = 1`, `M > 1` and `0 < r ≤ 1`: `∫_r^∞ |w| ≤ (|log r|^{1/2} + (2M)^{-1/2}) N`
(split at `1`: `q = s⁻¹` on `(r,1]`, `outer_far` on `(1,∞)`). -/
theorem outer_near_one (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    (hM : 1 < M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn (fun s => ‖w s‖) (Ioi r) ∧
      ∫ s in Ioi r, ‖w s‖ ≤
        (√(-Real.log r) + √(1 / (2 * M))) *
          √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  -- the piece `(r, 1]`
  have hcont : ContinuousOn (fun s : ℝ => s⁻¹) (Icc r 1) :=
    continuousOn_inv₀.mono fun x hx => ne_of_gt (hr.trans_le hx.1)
  have hq : IntegrableOn (fun s : ℝ => s⁻¹) (Ioc r 1) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : ∫ s in Ioc r 1, s⁻¹ = -Real.log r := by
    rw [← intervalIntegral.integral_of_le hr1, integral_inv_of_pos hr one_pos, one_div,
      Real.log_inv]
  have hpq : ∀ s ∈ Ioc r 1, ((fun _ : ℝ => (1 : ℝ)) s) ^ 2 ≤ s⁻¹ * ((1 + s ^ 2) ^ M * s) :=
    fun s hs => by
      have hs0 : 0 < s := hr.trans hs.1
      have e : s⁻¹ * ((1 + s ^ 2) ^ M * s) = (1 + s ^ 2) ^ M := by field_simp
      rw [e, one_pow]
      exact one_le_one_add_sq_rpow (by linarith) s
  have hA := setIntegral_mul_norm_le hwm hwi measurableSet_Ioc
    (fun s hs => hr.trans hs.1) (p := fun _ => (1 : ℝ)) (q := fun s => s⁻¹)
    aestronglyMeasurable_const (fun _ _ => zero_le_one) hq
    (fun s hs => inv_nonneg.2 (hr.trans hs.1).le) hpq
  simp only [one_mul] at hA
  rw [hint] at hA
  -- the piece `(1, ∞)`
  have hB := outer_far hwm hwi hM 1 one_pos
  have hcongr : ∀ s ∈ Ioi (1 : ℝ), s ^ (1 - ((1 : ℕ) : ℝ)) * ‖w s‖ = ‖w s‖ := fun s _ => by
    simp
  have hBi : IntegrableOn (fun s => ‖w s‖) (Ioi 1) :=
    hB.1.congr_fun hcongr measurableSet_Ioi
  have hBe : ∫ s in Ioi (1 : ℝ), ‖w s‖ ≤
      √(1 / (2 * M)) * √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
    have e1 : ((2 : ℝ) * ((1 : ℕ) : ℝ) + 2 * M - 2) = 2 * M := by push_cast; ring
    have h2 := hB.2
    rw [e1, Real.one_rpow, setIntegral_congr_fun measurableSet_Ioi hcongr] at h2
    exact h2
  have hU : Ioi r = Ioc r 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi hr1).symm
  refine ⟨hU ▸ hA.1.union hBi, ?_⟩
  rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hA.1 hBi, add_mul]
  exact add_le_add hA.2 hBe

end UnforcedLeray.B0079
