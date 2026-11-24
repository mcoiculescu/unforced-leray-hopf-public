import UnforcedLeray.Lib.ComplexODEC.Mode

/-!
# Endpoint orders, far field and the nonzero quadrupole (INF18 O10, O11)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §4 bypass B3, §5 targets O10, O11.
Manuscript `paper/main.tex` lines 1145--1153 (eq. `st18-t00045`, unit B0051) and
1181--1186 (eq. `st18-t00047`, unit B0055).

* `norm_modeRadial_le_sq`, `norm_deriv_modeRadial_le` (O10 at `0⁺`): `φ = O(r²)`,
  `φ' = O(r)` on `(0, 1]`, read off `φ(r) = β₀ r² b(r²)`.
* `tendsto_sq_mul_modeRadial` (O10 at `∞`): `r² φ(r) → -𝔐/4`, so `C_∞ = -𝔐/4`
  (tex eq. `st18-t00047`).
* `modeQuadrupole_ne_zero` (O11, scoping `quadrupole_ne_zero`): `𝔐 = ∫₀^∞ r³ h ≠ 0`.
  Proof (bypass B3): if `𝔐 = 0`, the Green formula gives
  `φ(r) = -¼ ∫_r^∞ (r²/s - s³/r²) h(s) ds`, a contraction in the sup norm on `[T, ∞)` for
  large `T`; so `φ = 0` there, and `F ≡ 0` by uniqueness for `F'' = V F`.

Not proved here: the Gaussian bound on the far-field remainder `r²φ(r) + 𝔐/4` and its
derivatives (the second half of O10).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm
open NonUniqueEuler.LinODE

/-- The quadrupole moment `𝔐(q) = ∫₀^∞ r³ h(r) dr` of the mode (tex eq. `st18-t00047`). -/
def modeQuadrupole (c : ℂ) (F : ℝ → ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * modeVort c F r

/-! ### O10 at the origin -/

/-- **O10, origin** (tex eq. `st18-t00045`, first line): `‖φ(r)‖ ≤ C r²` and
`‖φ'(r)‖ ≤ C r` on `(0, 1]`. -/
theorem modeRadial_orders_zero {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ C : ℝ, ∀ r ∈ Ioc (0 : ℝ) 1,
      ‖modeRadial F r‖ ≤ C * r ^ 2 ∧ ‖deriv (modeRadial F) r‖ ≤ C * r := by
  have hc := hF.im_ne_zero
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  have hb := contDiff_regB hc
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hb.continuous.continuousOn
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hb.continuous_deriv (by simp)).continuousOn
  refine ⟨‖β₀‖ * (2 * |B₀| + 2 * |B₁|), fun r hr => ⟨?_, ?_⟩⟩
  · have hr2 : r ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hr.1.le hr.2⟩
    rw [modeRadial_eq (fun t => (hβ t).1) hr.1, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hB₀ _ hr2
    have h1 : ‖regB c (r ^ 2)‖ ≤ 2 * |B₀| + 2 * |B₁| := by
      linarith [le_abs_self B₀, abs_nonneg B₁, abs_nonneg B₀]
    calc ‖β₀‖ * r ^ 2 * ‖regB c (r ^ 2)‖ ≤ ‖β₀‖ * r ^ 2 * (2 * |B₀| + 2 * |B₁|) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖β₀‖ * (2 * |B₀| + 2 * |B₁|) * r ^ 2 := by ring
  · have hr0 := hr.1
    have hr2 : r ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hr.1.le hr.2⟩
    have hbd : Differentiable ℝ (regB c) := hb.differentiable (by simp)
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have hd : HasDerivAt (fun r : ℝ => β₀ * ((r ^ 2 : ℝ) : ℂ) * regB c (r ^ 2))
        (β₀ * ((2 * r : ℝ) : ℂ) * regB c (r ^ 2) +
          β₀ * ((r ^ 2 : ℝ) : ℂ) * ((2 * r) • deriv (regB c) (r ^ 2))) r :=
      (hsq.ofReal_comp.const_mul β₀).mul ((hbd (r ^ 2)).hasDerivAt.scomp r hsq)
    have heq : modeRadial F =ᶠ[𝓝 r] fun r : ℝ => β₀ * ((r ^ 2 : ℝ) : ℂ) * regB c (r ^ 2) := by
      filter_upwards [Ioi_mem_nhds hr0] with x hx
      exact modeRadial_eq (fun t => (hβ t).1) hx
    rw [heq.deriv_eq, hd.deriv]
    have h0 := hB₀ _ hr2
    have h1 := hB₁ _ hr2
    have hr1 : r ^ 2 ≤ 1 := hr2.2
    calc ‖β₀ * ((2 * r : ℝ) : ℂ) * regB c (r ^ 2) +
          β₀ * ((r ^ 2 : ℝ) : ℂ) * ((2 * r) • deriv (regB c) (r ^ 2))‖
        ≤ ‖β₀‖ * (2 * r) * ‖regB c (r ^ 2)‖ +
            ‖β₀‖ * r ^ 2 * ((2 * r) * ‖deriv (regB c) (r ^ 2)‖) := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hr0, abs_two]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2)]
      _ ≤ ‖β₀‖ * (2 * r) * |B₀| + ‖β₀‖ * 1 * ((2 * r) * |B₁|) := by
          gcongr
          · exact h0.trans (le_abs_self _)
          · exact h1.trans (le_abs_self _)
      _ = ‖β₀‖ * (2 * |B₀| + 2 * |B₁|) * r := by ring

/-! ### O10 at infinity -/

/-- **O10, far field** (tex eq. `st18-t00045`, second line, and eq. `st18-t00047`):
`r² φ(r) → -𝔐/4`, i.e. `C_∞ = -𝔐(q)/4`. -/
theorem tendsto_sq_mul_modeRadial {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * modeRadial F r) atTop
      (𝓝 (-(1 / 4) * modeQuadrupole c F)) := by
  have h := Planar.tendsto_sq_mul_greenN_two (integrableOn_pow_mul_modeVort hF 3)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [mode_eq_green hF r hr]

/-! ### O11: the quadrupole is nonzero -/

theorem integral_interval_eq_sub {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {r : ℝ}
    (hr : 0 ≤ r) :
    ∫ s in (0 : ℝ)..r, f s = (∫ s in Ioi (0 : ℝ), f s) - ∫ s in Ioi r, f s := by
  have hu := setIntegral_union (μ := volume) (f := f) (Ioc_disjoint_Ioi_same (a := 0) (b := r))
    measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hr))
  rw [Ioc_union_Ioi_eq_Ioi hr] at hu
  rw [intervalIntegral.integral_of_le hr, hu]
  ring

/-- The far-field remainder after subtracting its quadrupole limit is an explicit Gaussian tail.
This is the first quantitative O10 reduction: it expresses `r²φ(r)+𝔐/4` only through the
vorticity on `(r,∞)`. -/
theorem modeRadial_farField_remainder_eq_tail {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    (r : ℂ) ^ 2 * modeRadial F r + (1 / 4 : ℂ) * modeQuadrupole c F =
      (1 / 4 : ℂ) *
        ((∫ s in Ioi r, (s : ℂ) ^ 3 * modeVort c F s) -
          (r : ℂ) ^ 4 * (∫ s in Ioi r, (s : ℂ)⁻¹ * modeVort c F s)) := by
  rw [mode_eq_green hF r hr, Planar.greenN_two_eq_R (wprof_modeVort hF) hr,
    B0011.R, modeQuadrupole]
  rw [integral_interval_eq_sub (integrableOn_pow_mul_modeVort hF 3) hr.le]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  ring

theorem integrableOn_pow_mul_norm_kappa {c : ℂ} (hc : c.im ≠ 0) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * ‖kappa c (s ^ 2)‖) (Ioi 0) := by
  have hint : IntegrableOn (fun r : ℝ => 1 / |c.im| * ((r ^ (k + 2) / 4 + 2 * r ^ k) *
      Real.exp (-(r ^ 2 / 4)))) (Ioi 0) := by
    have := ((integrableOn_pow_mul_gauss (k + 2)).div_const 4).add
      ((integrableOn_pow_mul_gauss k).const_mul 2)
    refine IntegrableOn.congr_fun (this.const_mul (1 / |c.im|)) (fun r _ => ?_)
      measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  refine hint.mono' ?_ ?_
  · exact ((continuous_pow k).mul ((contDiff_kappa hc).continuous.comp
      (continuous_pow 2)).norm).aestronglyMeasurable.restrict
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hpos : 0 < |c.im| := abs_pos.mpr hc
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_kappa_le hc (r ^ 2)
    have h2 : |r ^ 2 / 4 - 2| ≤ r ^ 2 / 4 + 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg r]
    calc r ^ k * ‖kappa c (r ^ 2)‖
        ≤ r ^ k * ((r ^ 2 / 4 + 2) * Real.exp (-(r ^ 2 / 4)) / |c.im|) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) hpos.le
      _ = 1 / |c.im| * ((r ^ (k + 2) / 4 + 2 * r ^ k) * Real.exp (-(r ^ 2 / 4))) := by
          field_simp
          ring

/-- The contraction step at infinity: if `𝔐 = 0`, `T ≥ 1`, `∫_T^∞ s³ |κ(s²)| ≤ 1` and
`‖φ‖ ≤ B` on `[T, ∞)`, then `‖φ‖ ≤ B/2` on `[T, ∞)`. -/
theorem norm_modeRadial_le_half {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    (h0 : modeQuadrupole c F = 0) {T : ℝ} (hT : 1 ≤ T)
    (hTint : ∫ s in Ioi T, s ^ 3 * ‖kappa c (s ^ 2)‖ ≤ 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, T ≤ s → ‖modeRadial F s‖ ≤ B) {r : ℝ} (hr : T ≤ r) :
    ‖modeRadial F r‖ ≤ B / 2 := by
  have hc := hF.im_ne_zero
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := le_trans hT hr
  set h := modeVort c F with hh
  set g : ℝ → ℝ := fun s => s ^ 3 * ‖kappa c (s ^ 2)‖ with hg
  have hgint : IntegrableOn g (Ioi 0) := integrableOn_pow_mul_norm_kappa hc 3
  have hgint_r : IntegrableOn g (Ioi r) := hgint.mono_set (Ioi_subset_Ioi hr0.le)
  -- `∫_r^∞ B g ≤ B`
  have hBg : ∫ s in Ioi r, B * g s ≤ B := by
    rw [integral_const_mul]
    have hmono : ∫ s in Ioi r, g s ≤ ∫ s in Ioi T, g s := by
      refine setIntegral_mono_set (hgint.mono_set (Ioi_subset_Ioi (by linarith)))
        ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => ?_)
        (Eventually.of_forall (Ioi_subset_Ioi hr))
      have : (0 : ℝ) < s := lt_of_lt_of_le (by linarith) (le_of_lt hs)
      positivity
    calc B * ∫ s in Ioi r, g s ≤ B * 1 :=
          mul_le_mul_of_nonneg_left (hmono.trans hTint) hB0
      _ = B := mul_one B
  -- pointwise bound `‖s³ h(s)‖ ≤ B g(s)` for `s > r`
  have hpt : ∀ s ∈ Ioi r, ‖(s : ℂ) ^ 3 * h s‖ ≤ B * g s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_trans hr0 hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, hh,
      modeVort, norm_mul]
    have := hB s (le_trans hr (le_of_lt hs))
    calc s ^ 3 * (‖kappa c (s ^ 2)‖ * ‖modeRadial F s‖)
        ≤ s ^ 3 * (‖kappa c (s ^ 2)‖ * B) := by gcongr
      _ = B * g s := by rw [hg]; ring
  have hpt' : ∀ s ∈ Ioi r, ‖(r : ℂ) ^ 2 * ((s : ℂ)⁻¹ * h s)‖ ≤ B * g s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_trans hr0 hs
    have hs1 : 1 ≤ s := le_trans hr1 (le_of_lt hs)
    refine le_trans ?_ (hpt s hs)
    rw [← mul_assoc, norm_mul, norm_mul (((s : ℂ)) ^ 3)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0, abs_of_pos hs0]
    rw [← div_eq_mul_inv, div_le_iff₀ hs0]
    have h1 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr0.le (le_of_lt hs) 2
    have h2 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
    nlinarith
  have I1 : ‖∫ s in Ioi r, (s : ℂ) ^ 3 * h s‖ ≤ B :=
    (norm_integral_le_of_norm_le (hgint_r.const_mul B)
      ((ae_restrict_mem measurableSet_Ioi).mono hpt)).trans hBg
  have I2 : ‖(r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * h s‖ ≤ B := by
    rw [← integral_const_mul]
    exact (norm_integral_le_of_norm_le (hgint_r.const_mul B)
      ((ae_restrict_mem measurableSet_Ioi).mono hpt')).trans hBg
  -- the Green formula with `𝔐 = 0`
  have hgreen : modeRadial F r = -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ *
      (-(∫ s in Ioi r, (s : ℂ) ^ 3 * h s)) + (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * h s) := by
    rw [mode_eq_green hF r hr0, Planar.greenN_two_eq_R (wprof_modeVort hF) hr0, B0011.R,
      integral_interval_eq_sub (integrableOn_pow_mul_modeVort hF 3) hr0.le]
    rw [show (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ 3 * modeVort c F s) = 0 from h0, zero_sub]
  rw [hgreen]
  have hrinv : ‖((r : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
  calc ‖-(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (-(∫ s in Ioi r, (s : ℂ) ^ 3 * h s)) +
        (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * h s)‖
      ≤ 1 / 4 * (1 * B + B) := by
        rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ I2))
          (by norm_num)
        rw [norm_mul, norm_neg]
        exact mul_le_mul hrinv I1 (norm_nonneg _) zero_le_one
    _ = B / 2 := by ring

/-- **O11** (scoping `quadrupole_ne_zero`; tex lines 1181--1186, eq. `st18-t00047`, unit
B0055): the quadrupole moment of the mode is nonzero. -/
theorem modeQuadrupole_ne_zero {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    modeQuadrupole c F ≠ 0 := by
  intro h0
  have hc := hF.im_ne_zero
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  -- a tail with small weight
  have htend := tendsto_integral_Ioi_zero (μ := volume)
    (f := fun s : ℝ => s ^ 3 * ‖kappa c (s ^ 2)‖) (b := id) tendsto_id
  obtain ⟨T, hTint, hT1⟩ := ((htend.eventually (ge_mem_nhds one_pos)).and
    (eventually_ge_atTop 1)).exists
  -- iterate the contraction
  have hn : ∀ n : ℕ, ∀ r, T ≤ r → ‖modeRadial F r‖ ≤ M / 2 ^ n := by
    intro n
    induction n with
    | zero => intro r _; simpa [modeRadial] using hM (Real.log r)
    | succ n ih =>
      intro r hr
      have := norm_modeRadial_le_half hF h0 hT1 hTint (by positivity) ih hr
      rw [pow_succ]
      calc ‖modeRadial F r‖ ≤ M / 2 ^ n / 2 := this
        _ = M / (2 ^ n * 2) := by ring
  have hz : ∀ r, T ≤ r → modeRadial F r = 0 := by
    intro r hr
    by_contra hne
    have hpos := norm_pos_iff.mpr hne
    have hlim : Tendsto (fun n : ℕ => M / 2 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul M
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [div_pow, one_pow]
      ring
    obtain ⟨n, hn'⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
    linarith [hn n r hr]
  have hT0 : 0 < T := by linarith
  have hFz : ∀ t, Real.log T ≤ t → F t = 0 := fun t ht => by
    have := hz (Real.exp t) (by
      rw [← Real.exp_log hT0]
      exact Real.exp_le_exp.mpr ht)
    simpa [modeRadial, Real.log_exp] using this
  set t₀ := Real.log T + 1
  have hF0 : F t₀ = 0 := hFz t₀ (by linarith)
  have hF0' : deriv F t₀ = 0 := by
    have hev : F =ᶠ[𝓝 t₀] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds (by linarith : Real.log T < t₀)] with t ht
      exact hFz t (le_of_lt ht)
    rw [hev.deriv_eq]
    simp
  have hall := IsSolOn.eqOn_zero ordConnected_univ (continuous_logPot hc).continuousOn
    hF.isSolOn (mem_univ t₀) hF0 hF0'
  obtain ⟨t, ht⟩ := hF.mode.nonzero
  exact ht (hall.1 (mem_univ t))

/-- The far-field coefficient `C_∞ = -𝔐/4` is nonzero (tex eq. `st18-t00045`, `C_∞ ≠ 0`). -/
theorem farField_ne_zero {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    -(1 / 4) * modeQuadrupole c F ≠ 0 :=
  mul_ne_zero (by norm_num) (modeQuadrupole_ne_zero hF)

end UnforcedLeray.ComplexODEC
