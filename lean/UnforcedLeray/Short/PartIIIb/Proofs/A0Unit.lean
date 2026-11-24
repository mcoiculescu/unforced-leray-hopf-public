import UnforcedLeray.Short.PartIIIb.Tasks
import UnforcedLeray.Lib.SpecialFunctions.EulerGamma

/-!
# Proof of `T_a0Unit` (source: `the November 2 reference manuscript`, lines 4709-4715)

Write `r = rMu chi dchi ν μ`, so `Bmu chi dchi ν μ t = r t • Dzero`, `γ = Re λ`, `b = γ/2`.
* `Bd (Bmu t) = (21/2) r(t)` and `Be (Bmu t) = 0`, so `aZero λ ℓ μ (Bmu) = -(21/4) ℓ ∫₀^∞ G`
  with `G(t) = t^μ e^{-λt} r(t)`.
* `L(μ) = ℓ ∫₀^∞ F` with `F(t) = t^{μ+3/2} e^{-λt}` (`integral_cpow_mul_cexp_laplace`).
* For `0 < ν ≤ 1` and `νt < 1`, `χ(νt) = 1` and `χ'(νt) = 0`, so `r(t) = t^{3/2}` and `F(t) = G(t)`.
* For `νt ≥ 1`, `‖F(t) - G(t)‖ ≤ e^{-b/ν} Φ(t)` with the integrable weight
  `Φ(t) = (1+M) t^{μ+3/2} e^{-bt} + (D/(μ+5/2)) t^{μ+5/2} e^{-bt}`, where `|χ| ≤ M`, `|χ'| ≤ D`
  globally, and `e^{-γt} = e^{-bt} e^{-bt} ≤ e^{-bt} e^{-b/ν}`.

Hence the statement holds with `b = Re λ / 2`, `ν₀ = 1`, `k = 0`, and `C = ‖(21/4) ℓ‖ ∫₀^∞ Φ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

/-- `χ' = 0` where `χ` is locally constant. -/
theorem a0_deriv_eq_zero {chi dchi : ℝ → ℝ} (hd : ∀ x, HasDerivAt chi (dchi x) x)
    {x c : ℝ} (h : ∀ᶠ y in 𝓝 x, chi y = c) : dchi x = 0 := by
  have h1 : HasDerivAt (fun _ : ℝ => c) (dchi x) x :=
    (hd x).congr_of_eventuallyEq (h.mono fun y hy => hy.symm)
  exact h1.unique (hasDerivAt_const x c)

/-- Global bounds `|χ| ≤ M`, `|χ'| ≤ D` for a cutoff with `χ = 1` on `(-∞,1]`, `χ = 0` on `[1.1,∞)`. -/
theorem a0_bounds {chi dchi : ℝ → ℝ} (hd : ∀ x, HasDerivAt chi (dchi x) x)
    (hdc : Continuous dchi) (h1 : ∀ x, x ≤ 1 → chi x = 1) (h2 : ∀ x, 1.1 ≤ x → chi x = 0) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ (∀ x, |chi x| ≤ M) ∧ (∀ x, |dchi x| ≤ D) := by
  have hc : Continuous chi := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hK : IsCompact (Icc (1 : ℝ) 1.1) := isCompact_Icc
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
  have hchi : ∀ x, |chi x| ≤ max 1 C0 := by
    intro x
    rcases le_or_gt x 1 with hx | hx
    · rw [h1 x hx, abs_one]
      exact le_max_left _ _
    rcases le_or_gt x 1.1 with hx' | hx'
    · have := hC0 x ⟨hx.le, hx'⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
    · rw [h2 x hx'.le, abs_zero]
      exact (zero_le_one).trans (le_max_left _ _)
  have hdz1 : ∀ x, x < 1 → dchi x = 0 := fun x hx =>
    a0_deriv_eq_zero hd (c := 1)
      (Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => h1 y (Set.mem_Iio.1 hy).le)
  have hdz2 : ∀ x, 1.1 < x → dchi x = 0 := fun x hx =>
    a0_deriv_eq_zero hd (c := 0)
      (Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => h2 y (Set.mem_Ioi.1 hy).le)
  have hD : ∀ x, |dchi x| ≤ max 0 C1 := by
    intro x
    rcases lt_or_ge x 1 with hx | hx
    · rw [hdz1 x hx, abs_zero]
      exact le_max_left _ _
    rcases le_or_gt x 1.1 with hx' | hx'
    · have := hC1 x ⟨hx, hx'⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _)
    · rw [hdz2 x hx', abs_zero]
      exact le_max_left _ _
  exact ⟨max 1 C0, max 0 C1, (zero_le_one).trans (le_max_left _ _), le_max_left _ _, hchi, hD⟩

/-- Pointwise bound on the amplitude `r_μ`, for `0 ≤ ν ≤ 1`. -/
theorem a0_rMu_bound {chi dchi : ℝ → ℝ} {M D μ ν t : ℝ} (hM : ∀ x, |chi x| ≤ M)
    (hD : ∀ x, |dchi x| ≤ D) (hμ : 0 < μ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (ht : 0 < t) :
    |rMu chi dchi ν μ t| ≤ M * t ^ (3 / 2 : ℝ) + D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ) := by
  have hp : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ t ^ (5 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hK : 0 < μ + 5 / 2 := by linarith
  unfold rMu
  have h1 : |chi (ν * t) * t ^ (3 / 2 : ℝ)| ≤ M * t ^ (3 / 2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (hM _) hp
  have hnd : ν * |dchi (ν * t)| ≤ D := (mul_le_of_le_one_left (abs_nonneg _) hν1).trans (hD _)
  have h2 : |ν * dchi (ν * t) * t ^ (5 / 2 : ℝ) / (μ + 5 / 2)| ≤
      D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hν0, abs_of_pos hK, abs_of_nonneg hq]
    have h3 : ν * |dchi (ν * t)| * t ^ (5 / 2 : ℝ) ≤ D * t ^ (5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hnd hq
    calc ν * |dchi (ν * t)| * t ^ (5 / 2 : ℝ) / (μ + 5 / 2)
        ≤ D * t ^ (5 / 2 : ℝ) / (μ + 5 / 2) := by gcongr
      _ = D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ) := by ring
  calc |chi (ν * t) * t ^ (3 / 2 : ℝ) + ν * dchi (ν * t) * t ^ (5 / 2 : ℝ) / (μ + 5 / 2)|
      ≤ |chi (ν * t) * t ^ (3 / 2 : ℝ)| + |ν * dchi (ν * t) * t ^ (5 / 2 : ℝ) / (μ + 5 / 2)| :=
        abs_add_le _ _
    _ ≤ M * t ^ (3 / 2 : ℝ) + D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ) := add_le_add h1 h2

/-- Splitting `t^{μ+3/2}` for `t > 0`. -/
theorem a0_cpow_split {t : ℝ} (ht : 0 < t) (μ : ℝ) :
    (t : ℂ) ^ ((μ : ℂ) + 3 / 2) = (t : ℂ) ^ (μ : ℂ) * ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow ht.le (3 / 2 : ℝ),
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 ht.ne')]
  congr 1
  norm_num

/-- Norm of `t^a e^{-λt}` for `t > 0`. -/
theorem a0_norm_cpow (lam a : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ a * Complex.exp (-(lam * t))‖ = t ^ a.re * Real.exp (-(lam.re * t)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp

/-- The integrable majorant `Φ`. -/
def a0Phi (M D μ b : ℝ) (t : ℝ) : ℝ :=
  (1 + M) * (t ^ (μ + 3 / 2) * Real.exp (-(b * t))) +
    D / (μ + 5 / 2) * (t ^ (μ + 5 / 2) * Real.exp (-(b * t)))

theorem a0Phi_integrable {M D μ b : ℝ} (hμ : 0 < μ) (hb : 0 < b) :
    IntegrableOn (a0Phi M D μ b) (Ioi 0) := by
  have h1 := UnforcedLeray.Special.integrableOn_rpow_mul_exp_neg_mul_Ioi
    (s := μ + 3 / 2) (b := b) (by linarith) hb
  have h2 := UnforcedLeray.Special.integrableOn_rpow_mul_exp_neg_mul_Ioi
    (s := μ + 5 / 2) (b := b) (by linarith) hb
  exact (Integrable.const_mul h1 (1 + M)).add (Integrable.const_mul h2 (D / (μ + 5 / 2)))

theorem a0Phi_nonneg {M D μ b : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hμ : 0 < μ) {t : ℝ} (ht : 0 < t) :
    0 ≤ a0Phi M D μ b t := by
  unfold a0Phi
  have h1 : 0 ≤ t ^ (μ + 3 / 2) := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ t ^ (μ + 5 / 2) := Real.rpow_nonneg ht.le _
  have h3 : 0 ≤ Real.exp (-(b * t)) := (Real.exp_pos _).le
  have h4 : 0 ≤ D / (μ + 5 / 2) := div_nonneg hD (by linarith)
  have h5 : 0 ≤ 1 + M := by linarith
  exact add_nonneg (mul_nonneg h5 (mul_nonneg h1 h3)) (mul_nonneg h4 (mul_nonneg h2 h3))

/-- `F(t) = t^{μ+3/2} e^{-λt}` (integrand of `integral_cpow_mul_cexp_laplace`). -/
def a0F (lam : ℂ) (μ : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((μ : ℂ) + 3 / 2) * Complex.exp (-(lam * t))

/-- `G(t) = t^μ e^{-λt} r_μ(t)`. -/
def a0G (lam : ℂ) (chi dchi : ℝ → ℝ) (ν μ : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (μ : ℂ) * Complex.exp (-(lam * t)) * ((rMu chi dchi ν μ t : ℝ) : ℂ)

theorem a0F_norm_le {lam : ℂ} (hlam : 0 < lam.re) {M D μ : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hμ : 0 < μ) {t : ℝ} (ht : 0 < t) :
    ‖a0F lam μ t‖ ≤ a0Phi M D μ (lam.re / 2) t := by
  unfold a0F
  rw [a0_norm_cpow lam _ ht]
  have hre : ((μ : ℂ) + 3 / 2).re = μ + 3 / 2 := by simp
  rw [hre]
  have hexp : Real.exp (-(lam.re * t)) ≤ Real.exp (-(lam.re / 2 * t)) :=
    Real.exp_le_exp.2 (by nlinarith [mul_pos hlam ht])
  have h0 : 0 ≤ t ^ (μ + 3 / 2) := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ t ^ (μ + 5 / 2) := Real.rpow_nonneg ht.le _
  have h3 : 0 ≤ Real.exp (-(lam.re / 2 * t)) := (Real.exp_pos _).le
  have hK : 0 ≤ D / (μ + 5 / 2) * (t ^ (μ + 5 / 2) * Real.exp (-(lam.re / 2 * t))) :=
    mul_nonneg (div_nonneg hD (by linarith)) (mul_nonneg h2 h3)
  have hX : 0 ≤ t ^ (μ + 3 / 2) * Real.exp (-(lam.re / 2 * t)) := mul_nonneg h0 h3
  unfold a0Phi
  calc t ^ (μ + 3 / 2) * Real.exp (-(lam.re * t))
      ≤ t ^ (μ + 3 / 2) * Real.exp (-(lam.re / 2 * t)) := mul_le_mul_of_nonneg_left hexp h0
    _ ≤ (1 + M) * (t ^ (μ + 3 / 2) * Real.exp (-(lam.re / 2 * t))) :=
        le_mul_of_one_le_left hX (by linarith)
    _ ≤ _ := le_add_of_nonneg_right hK

theorem a0G_norm_le {lam : ℂ} (hlam : 0 < lam.re) {chi dchi : ℝ → ℝ} {M D μ ν : ℝ}
    (hM : ∀ x, |chi x| ≤ M) (hD : ∀ x, |dchi x| ≤ D)
    (hμ : 0 < μ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) {t : ℝ} (ht : 0 < t) :
    ‖a0G lam chi dchi ν μ t‖ ≤ a0Phi M D μ (lam.re / 2) t := by
  unfold a0G
  rw [norm_mul, a0_norm_cpow lam (μ : ℂ) ht, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re]
  have hr := a0_rMu_bound hM hD hμ hν0 hν1 ht
  have hexp : Real.exp (-(lam.re * t)) ≤ Real.exp (-(lam.re / 2 * t)) :=
    Real.exp_le_exp.2 (by nlinarith [mul_pos hlam ht])
  have hP : 0 ≤ t ^ μ := Real.rpow_nonneg ht.le _
  have h0 : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have h3 : 0 ≤ Real.exp (-(lam.re / 2 * t)) := (Real.exp_pos _).le
  have hX : 0 ≤ t ^ μ * t ^ (3 / 2 : ℝ) * Real.exp (-(lam.re / 2 * t)) :=
    mul_nonneg (mul_nonneg hP h0) h3
  unfold a0Phi
  calc t ^ μ * Real.exp (-(lam.re * t)) * |rMu chi dchi ν μ t|
      ≤ t ^ μ * Real.exp (-(lam.re / 2 * t)) * |rMu chi dchi ν μ t| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hP) (abs_nonneg _)
    _ ≤ t ^ μ * Real.exp (-(lam.re / 2 * t)) *
          (M * t ^ (3 / 2 : ℝ) + D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg hP h3)
    _ = M * (t ^ μ * t ^ (3 / 2 : ℝ) * Real.exp (-(lam.re / 2 * t))) +
          D / (μ + 5 / 2) * (t ^ μ * t ^ (5 / 2 : ℝ) * Real.exp (-(lam.re / 2 * t))) := by
        ring
    _ ≤ (1 + M) * (t ^ (μ + 3 / 2) * Real.exp (-(lam.re / 2 * t))) +
          D / (μ + 5 / 2) * (t ^ (μ + 5 / 2) * Real.exp (-(lam.re / 2 * t))) := by
        rw [Real.rpow_add ht μ (3 / 2), Real.rpow_add ht μ (5 / 2)]
        nlinarith [hX]

theorem a0F_integrableOn {lam : ℂ} (hlam : 0 < lam.re) {M D μ : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hμ : 0 < μ) : IntegrableOn (a0F lam μ) (Ioi 0) := by
  have hmeas : Measurable (a0F lam μ) := by
    unfold a0F
    fun_prop
  refine Integrable.mono' (a0Phi_integrable (M := M) (D := D) hμ (half_pos hlam))
    hmeas.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    a0F_norm_le hlam hM hD hμ (Set.mem_Ioi.1 ht)

theorem a0G_integrableOn {lam : ℂ} (hlam : 0 < lam.re) {chi dchi : ℝ → ℝ} {M D μ ν : ℝ}
    (hchi : Measurable chi) (hdchi : Measurable dchi)
    (hM : ∀ x, |chi x| ≤ M) (hD : ∀ x, |dchi x| ≤ D) (hμ : 0 < μ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    IntegrableOn (a0G lam chi dchi ν μ) (Ioi 0) := by
  have hr : Measurable (fun t : ℝ => rMu chi dchi ν μ t) := by
    unfold rMu
    fun_prop
  have hmeas : Measurable (a0G lam chi dchi ν μ) := by
    unfold a0G
    exact ((by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ (μ : ℂ) * Complex.exp (-(lam * t))).mul
      (Complex.measurable_ofReal.comp hr))
  refine Integrable.mono' (a0Phi_integrable (M := M) (D := D) hμ (half_pos hlam))
    hmeas.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    a0G_norm_le hlam hM hD hμ hν0 hν1 (Set.mem_Ioi.1 ht)

/-- Pointwise bound `‖F(t) - G(t)‖ ≤ e^{-b/ν} Φ(t)` for `0 < ν ≤ 1`, `t > 0`. -/
theorem a0_diff_norm {lam : ℂ} (hlam : 0 < lam.re) {chi dchi : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt chi (dchi x) x) (h1 : ∀ x, x ≤ 1 → chi x = 1)
    {M D μ ν : ℝ} (hM : ∀ x, |chi x| ≤ M) (hD : ∀ x, |dchi x| ≤ D)
    (hM0 : 0 ≤ M) (hD0 : 0 ≤ D) (hμ : 0 < μ) (hν : 0 < ν) (hν1 : ν ≤ 1) {t : ℝ} (ht : 0 < t) :
    ‖a0F lam μ t - a0G lam chi dchi ν μ t‖ ≤
      Real.exp (-(lam.re / 2) / ν) * a0Phi M D μ (lam.re / 2) t := by
  have hsplit : a0F lam μ t - a0G lam chi dchi ν μ t =
      (t : ℂ) ^ (μ : ℂ) * Complex.exp (-(lam * t)) *
        ((t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t : ℝ) : ℂ) := by
    unfold a0F a0G
    rw [a0_cpow_split ht μ, Complex.ofReal_sub]
    ring
  rw [hsplit, norm_mul, a0_norm_cpow lam (μ : ℂ) ht, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re, neg_div]
  rcases lt_or_ge (ν * t) 1 with hνt | hνt
  · have hchi1 : chi (ν * t) = 1 := h1 _ hνt.le
    have hdchi0 : dchi (ν * t) = 0 :=
      a0_deriv_eq_zero hd (c := 1)
        (Filter.eventually_of_mem (Iio_mem_nhds hνt) fun y hy => h1 y (Set.mem_Iio.1 hy).le)
    have hE0 : t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t = 0 := by
      unfold rMu
      rw [hchi1, hdchi0]
      ring
    rw [hE0, abs_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (a0Phi_nonneg hM0 hD0 hμ ht)
  · have hb : 0 < lam.re / 2 := half_pos hlam
    have hbν : lam.re / 2 / ν ≤ lam.re / 2 * t := by
      rw [div_le_iff₀ hν]
      nlinarith [mul_le_mul_of_nonneg_left hνt hb.le]
    have hX : Real.exp (-(lam.re * t)) ≤
        Real.exp (-(lam.re / 2 * t)) * Real.exp (-(lam.re / 2 / ν)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have hE : |t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t| ≤
        (1 + M) * t ^ (3 / 2 : ℝ) + D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ) := by
      have hr := a0_rMu_bound hM hD hμ hν.le hν1 ht
      have hp : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
      have hEb : |t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t| ≤
          t ^ (3 / 2 : ℝ) + |rMu chi dchi ν μ t| :=
        abs_le.2 ⟨by linarith [le_abs_self (rMu chi dchi ν μ t)],
          by linarith [neg_le_abs (rMu chi dchi ν μ t)]⟩
      nlinarith [hEb, hr]
    have hP : 0 ≤ t ^ μ := Real.rpow_nonneg ht.le _
    have he : 0 ≤ Real.exp (-(lam.re / 2 * t)) := (Real.exp_pos _).le
    have hg : 0 ≤ Real.exp (-(lam.re / 2 / ν)) := (Real.exp_pos _).le
    calc t ^ μ * Real.exp (-(lam.re * t)) * |t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t|
        ≤ t ^ μ * (Real.exp (-(lam.re / 2 * t)) * Real.exp (-(lam.re / 2 / ν))) *
            |t ^ (3 / 2 : ℝ) - rMu chi dchi ν μ t| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hP) (abs_nonneg _)
      _ ≤ t ^ μ * (Real.exp (-(lam.re / 2 * t)) * Real.exp (-(lam.re / 2 / ν))) *
            ((1 + M) * t ^ (3 / 2 : ℝ) + D / (μ + 5 / 2) * t ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg hP (mul_nonneg he hg))
      _ = Real.exp (-(lam.re / 2 / ν)) * a0Phi M D μ (lam.re / 2) t := by
          unfold a0Phi
          rw [Real.rpow_add ht μ (3 / 2), Real.rpow_add ht μ (5 / 2)]
          ring

/-- Target `T_a0Unit` (Tasks.lean; source lines 4709-4715). -/
theorem a0Unit : T_a0Unit := by
  unfold T_a0Unit
  intro lam ell chi dchi μ hlam hμ hd hdc h1 h2
  obtain ⟨M, D, hM0, hD0, hM, hD⟩ := a0_bounds hd hdc h1 h2
  have hb : 0 < lam.re / 2 := half_pos hlam
  have hcont : Continuous chi := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hμC : -5 / 2 < (μ : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hFint : ∫ t in Ioi (0 : ℝ), a0F lam μ t =
      Complex.Gamma ((μ : ℂ) + 5 / 2) / lam ^ ((μ : ℂ) + 5 / 2) := by
    unfold a0F
    rw [UnforcedLeray.Special.integral_cpow_mul_cexp_laplace hμC hlam, Complex.cpow_neg]
    ring
  refine ⟨‖(21 / 4 : ℂ) * ell‖ * ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t,
    lam.re / 2, 1, 0, hb, one_pos, ?_⟩
  intro ν hν hν1
  have hFi : IntegrableOn (a0F lam μ) (Ioi 0) := a0F_integrableOn hlam hM0 hD0 hμ
  have hGi : IntegrableOn (a0G lam chi dchi ν μ) (Ioi 0) :=
    a0G_integrableOn hlam hcont.measurable hdc.measurable hM hD hμ hν.le hν1
  have hA : aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) =
      -(21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), a0G lam chi dchi ν μ t := by
    unfold aZero
    have hint : ∀ t : ℝ, (t : ℂ) ^ (μ : ℂ) * Complex.exp (-lam * (t : ℂ)) *
        (((Bd (Bmu chi dchi ν μ t) : ℝ) : ℂ) - Complex.I * ((Be (Bmu chi dchi ν μ t) : ℝ) : ℂ))
        = (21 / 2 : ℂ) * a0G lam chi dchi ν μ t := by
      intro t
      simp [Bd, Be, Bmu, Dzero, a0G, rMu, neg_mul]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hint t),
      MeasureTheory.integral_const_mul]
    ring
  have hkey : aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ)
      = (21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t) := by
    rw [hA, MeasureTheory.integral_sub hFi hGi, hFint, LCoeff]
    ring
  have hint_bd : ‖∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖ ≤
      Real.exp (-(lam.re / 2) / ν) * ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.norm_integral_le_of_norm_le
      (Integrable.const_mul (a0Phi_integrable (M := M) (D := D) hμ hb) _) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      a0_diff_norm hlam hd h1 hM hD hM0 hD0 hμ hν hν1 (Set.mem_Ioi.1 ht)
  rw [hkey]
  calc ‖(21 / 4 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖
      = ‖(21 / 4 : ℂ) * ell‖ * ‖∫ t in Ioi (0 : ℝ), (a0F lam μ t - a0G lam chi dchi ν μ t)‖ :=
        norm_mul _ _
    _ ≤ ‖(21 / 4 : ℂ) * ell‖ *
          (Real.exp (-(lam.re / 2) / ν) * ∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t) :=
        mul_le_mul_of_nonneg_left hint_bd (norm_nonneg _)
    _ = ‖(21 / 4 : ℂ) * ell‖ * (∫ t in Ioi (0 : ℝ), a0Phi M D μ (lam.re / 2) t) *
          ν⁻¹ ^ 0 * Real.exp (-(lam.re / 2) / ν) := by
        ring

end UnforcedLeray.Short.PartIIIb
