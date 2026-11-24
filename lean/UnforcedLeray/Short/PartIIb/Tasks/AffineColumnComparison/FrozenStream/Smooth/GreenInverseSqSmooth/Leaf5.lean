import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2

/-!


Source: `the November 2 reference manuscript` lines 2347-2352.

Let `d = g - p` (after replacing `g, p` by their values on `[0,∞)` extended by `max · 0`).  Then
`d(u) = ∫₀^u ¼ ∫₀¹ t² a(vt) d(vt) dt dv` on `[0,∞)`, with `|a| ≤ M` on compacts.  With
`A = sup_{[0,u]} |d|`, induction gives `|d(w)| ≤ A (Mw)^n / n!` for all `n` and `w ∈ [0,u]`, so
`d = 0` there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The real part of the eigen-denominator is `Re lam`. -/
theorem sqVU_den_re (lam : ℂ) (x : ℝ) :
    (lam + 2 * Complex.I * ((x : ℝ) : ℂ)).re = lam.re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The eigen-coefficient is continuous on `ℝ` when `Re lam > 0`. -/
theorem sqVU_coeff_continuous (lam : ℂ) (hl : 0 < lam.re) : Continuous (sqCoeff lam) := by
  unfold sqCoeff
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro u h0
  have := congrArg Complex.re h0
  rw [sqVU_den_re, Complex.zero_re] at this
  linarith

/-- Uniform bound on `[0,u]` for the eigen-coefficient. -/
theorem sqVU_coeff_norm (lam : ℂ) (hl : 0 < lam.re) (u s : ℝ) (hu : 0 ≤ u) (hs0 : 0 ≤ s)
    (hsu : s ≤ u) : ‖sqCoeff lam s‖ ≤ 2 * (u / 4 + 2) / lam.re := by
  unfold sqCoeff
  have hden : lam.re ≤ ‖lam + 2 * Complex.I * ((Real.exp (-s / 4) : ℝ) : ℂ)‖ := by
    have h := Complex.re_le_norm (lam + 2 * Complex.I * ((Real.exp (-s / 4) : ℝ) : ℂ))
    rw [sqVU_den_re] at h
    exact h
  have key : |(s / 4 - 2) * Real.exp (-s / 4)| ≤ u / 4 + 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |s / 4 - 2| ≤ u / 4 + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : Real.exp (-s / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc |s / 4 - 2| * Real.exp (-s / 4) ≤ (u / 4 + 2) * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)
      _ = u / 4 + 2 := mul_one _
  have hnum : ‖2 * Complex.I * (((s / 4 - 2) * Real.exp (-s / 4) : ℝ) : ℂ)‖ ≤ 2 * (u / 4 + 2) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs]
    linarith
  rw [norm_div]
  exact div_le_div₀ (by linarith) hnum hl hden

/-- The Volterra right-hand side with `c = 0` is shift-compatible. -/
theorem sqVU_shift (lam : ℂ) (c : ℂ) (k : ℝ → ℂ) (x : ℝ) :
    sqVolterra lam c k x = c + sqVolterra lam 0 k x := by
  unfold sqVolterra
  ring

/-- The Volterra integral only sees the values of the solution on `[0,∞)`. -/
theorem sqVU_congr (lam : ℂ) (k1 k2 : ℝ → ℂ) (x : ℝ) (hx : 0 ≤ x)
    (h : ∀ w : ℝ, 0 ≤ w → k1 w = k2 w) : sqVolterra lam 0 k1 x = sqVolterra lam 0 k2 x := by
  unfold sqVolterra
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hx] at hv
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  dsimp only
  rw [h _ (mul_nonneg hv.1 ht.1)]

/-- Linearity of the Volterra integral in the solution, for continuous solutions. -/
theorem sqVU_sub (lam : ℂ) (hl : 0 < lam.re) (G P : ℝ → ℂ) (hG : Continuous G)
    (hP : Continuous P) (x : ℝ) :
    sqVolterra lam 0 (fun w => G w - P w) x = sqVolterra lam 0 G x - sqVolterra lam 0 P x := by
  have hA := sqVU_coeff_continuous lam hl
  have hcont : ∀ k : ℝ → ℂ, Continuous k →
      Continuous (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * k (v * t))) := by
    intro k hk
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v t => (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * k (v * t)))
    have : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) ^ 2 * (sqCoeff lam (p.1 * p.2) * k (p.1 * p.2))) :=
      ((Complex.continuous_ofReal.comp continuous_snd).pow 2).mul
        ((hA.comp (continuous_fst.mul continuous_snd)).mul
          (hk.comp (continuous_fst.mul continuous_snd)))
    exact this
  have hinner : ∀ v : ℝ,
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * (G (v * t) - P (v * t)))) =
        (∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * G (v * t))) -
          ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * P (v * t)) := by
    intro v
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      ring
    · have : Continuous (fun t : ℝ => (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * G (v * t))) := by
        fun_prop
      exact this.intervalIntegrable 0 1
    · have : Continuous (fun t : ℝ => (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * P (v * t))) := by
        fun_prop
      exact this.intervalIntegrable 0 1
  have key : (∫ v in (0 : ℝ)..x, (1 / 4 : ℂ) *
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * (G (v * t) - P (v * t)))) =
      (∫ v in (0 : ℝ)..x, (1 / 4 : ℂ) *
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * G (v * t))) -
      ∫ v in (0 : ℝ)..x, (1 / 4 : ℂ) *
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * P (v * t)) := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [hinner v, mul_sub]
    · exact ((hcont G hG).const_mul _).intervalIntegrable _ _
    · exact ((hcont P hP).const_mul _).intervalIntegrable _ _
  unfold sqVolterra
  simp only [zero_add]
  exact key

/-- Gronwall by iteration: `|d(w)| ≤ A (Mw)^n / n!` on `[0,u]` for every `n`. -/
theorem sqVU_gronwall (lam : ℂ) (u M : ℝ) (hu : 0 ≤ u) (hM0 : 0 ≤ M)
    (hM : ∀ s : ℝ, 0 ≤ s → s ≤ u → ‖sqCoeff lam s‖ ≤ M)
    (D : ℝ → ℂ) (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ w ∈ Icc (0 : ℝ) u, ‖D w‖ ≤ A)
    (hid : ∀ w : ℝ, 0 ≤ w → w ≤ u → D w = sqVolterra lam 0 D w) :
    ∀ n : ℕ, ∀ w ∈ Icc (0 : ℝ) u, ‖D w‖ ≤ A * ((M * w) ^ n / (n.factorial : ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact hA w hw
  | succ n ih =>
    intro w hw
    obtain ⟨hw0, hwu⟩ := hw
    rw [hid w hw0 hwu]
    unfold sqVolterra
    rw [zero_add]
    have hn : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    have hinner : ∀ v ∈ Icc (0 : ℝ) w,
        ‖(1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * D (v * t))‖ ≤
          (1 / 4) * (M * (A * ((M * v) ^ n / (n.factorial : ℝ)))) := by
      intro v hv
      obtain ⟨hv0, hvw⟩ := hv
      have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
          ‖(t : ℂ) ^ 2 * (sqCoeff lam (v * t) * D (v * t))‖ ≤
            M * (A * ((M * v) ^ n / (n.factorial : ℝ))) := by
        intro t ht
        rw [Set.uIoc_of_le zero_le_one] at ht
        obtain ⟨ht0, ht1⟩ := ht
        have hvt0 : 0 ≤ v * t := mul_nonneg hv0 ht0.le
        have hvtv : v * t ≤ v := mul_le_of_le_one_right hv0 ht1
        have hvtu : v * t ≤ u := by linarith
        have h1 : ‖(t : ℂ) ^ 2‖ ≤ 1 := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
          exact pow_le_one₀ ht0.le ht1
        have h2 : ‖D (v * t)‖ ≤ A * ((M * v) ^ n / (n.factorial : ℝ)) := by
          have h2a := ih (v * t) ⟨hvt0, hvtu⟩
          have hpow : (M * (v * t)) ^ n ≤ (M * v) ^ n :=
            pow_le_pow_left₀ (mul_nonneg hM0 hvt0) (mul_le_mul_of_nonneg_left hvtv hM0) n
          have hdiv : (M * (v * t)) ^ n / (n.factorial : ℝ) ≤ (M * v) ^ n / (n.factorial : ℝ) :=
            div_le_div_of_nonneg_right hpow (by positivity)
          exact h2a.trans (mul_le_mul_of_nonneg_left hdiv hA0)
        have h3 : ‖sqCoeff lam (v * t)‖ ≤ M := hM _ hvt0 hvtu
        rw [norm_mul, norm_mul]
        have := mul_le_mul h1 (mul_le_mul h3 h2 (norm_nonneg _) hM0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
        simpa only [one_mul] using this
      have hI : ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * D (v * t))‖ ≤
          M * (A * ((M * v) ^ n / (n.factorial : ℝ))) := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        rw [sub_zero, abs_one, mul_one] at this
        exact this
      rw [norm_mul, hn]
      exact mul_le_mul_of_nonneg_left hI (by norm_num)
    have hfun : (fun v : ℝ => (1 / 4 : ℝ) * (M * (A * ((M * v) ^ n / (n.factorial : ℝ))))) =
        fun v : ℝ => ((1 / 4 : ℝ) * M * A / (n.factorial : ℝ) * M ^ n) * v ^ n := by
      funext v
      rw [mul_pow]
      ring
    have hint : ∫ v in (0 : ℝ)..w, (1 / 4 : ℝ) * (M * (A * ((M * v) ^ n / (n.factorial : ℝ)))) =
        (1 / 4 : ℝ) * (A * ((M * w) ^ (n + 1) / ((n + 1).factorial : ℝ))) := by
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
        sub_zero, Nat.factorial_succ]
      push_cast
      rw [mul_pow]
      field_simp
      ring
    have hout := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun v : ℝ =>
        (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * D (v * t)))
      (g := fun v : ℝ => (1 / 4 : ℝ) * (M * (A * ((M * v) ^ n / (n.factorial : ℝ)))))
      hw0
      (ae_of_all _ fun v hv => hinner v ⟨hv.1.le, hv.2⟩)
      (by
        apply Continuous.intervalIntegrable
        fun_prop)
    rw [hint] at hout
    have hnn : 0 ≤ A * ((M * w) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      apply mul_nonneg hA0
      apply div_nonneg
      · exact pow_nonneg (mul_nonneg hM0 hw0) _
      · positivity
    linarith

/-- **Leaf 5** (uniqueness on `[0,∞)`): two continuous-on-`[0,∞)` solutions of the same Volterra
equation agree on `[0,∞)`. -/
theorem sqVolterraUnique : UnforcedLeray.Short.IIb.SqVolterraUnique := by
  unfold UnforcedLeray.Short.IIb.SqVolterraUnique
  intro lam c hl g p hgc hpc hg hp u hu
  -- extend the solutions by their values on `[0,∞)` so that everything is continuous on `ℝ`
  set G : ℝ → ℂ := fun w => g (max w 0) with hGdef
  set P : ℝ → ℂ := fun w => p (max w 0) with hPdef
  have hGc : Continuous G :=
    hgc.comp_continuous (by fun_prop) (fun w => Set.mem_Ici.mpr (le_max_right w 0))
  have hPc : Continuous P :=
    hpc.comp_continuous (by fun_prop) (fun w => Set.mem_Ici.mpr (le_max_right w 0))
  have hGeq : ∀ w : ℝ, 0 ≤ w → G w = g w := by
    intro w hw
    show g (max w 0) = g w
    rw [max_eq_left hw]
  have hPeq : ∀ w : ℝ, 0 ≤ w → P w = p w := by
    intro w hw
    show p (max w 0) = p w
    rw [max_eq_left hw]
  have hGE : ∀ x : ℝ, 0 ≤ x → G x = c + sqVolterra lam 0 G x := by
    intro x hx
    rw [hGeq x hx, hg x hx, sqVU_shift,
      sqVU_congr lam g G x hx (fun w hw => (hGeq w hw).symm)]
  have hPE : ∀ x : ℝ, 0 ≤ x → P x = c + sqVolterra lam 0 P x := by
    intro x hx
    rw [hPeq x hx, hp x hx, sqVU_shift,
      sqVU_congr lam p P x hx (fun w hw => (hPeq w hw).symm)]
  set D : ℝ → ℂ := fun w => G w - P w with hD
  have hDc : Continuous D := hGc.sub hPc
  have hid : ∀ w : ℝ, 0 ≤ w → D w = sqVolterra lam 0 D w := by
    intro w hw
    show G w - P w = sqVolterra lam 0 (fun w => G w - P w) w
    rw [sqVU_sub lam hl G P hGc hPc w, hGE w hw, hPE w hw]
    ring
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := u)).exists_bound_of_continuousOn
    hDc.continuousOn
  have hM0 : 0 ≤ 2 * (u / 4 + 2) / lam.re := div_nonneg (by linarith) hl.le
  have hG := sqVU_gronwall lam u (2 * (u / 4 + 2) / lam.re) hu hM0
    (fun s hs0 hsu => sqVU_coeff_norm lam hl u s hu hs0 hsu) D (max C 0) (le_max_right _ _)
    (fun w hw => (hC w hw).trans (le_max_left _ _)) (fun w hw _ => hid w hw)
  have hlim : Tendsto (fun n : ℕ => max C 0 *
      ((2 * (u / 4 + 2) / lam.re * u) ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (2 * (u / 4 + 2) / lam.re * u)).const_mul (max C 0)
    rw [mul_zero] at this
    exact this
  have hD0 : ‖D u‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hG n u ⟨hu, le_rfl⟩)
  have hDu : D u = 0 := norm_le_zero_iff.mp hD0
  have h2 : G u - P u = 0 := hDu
  rw [hGeq u hu, hPeq u hu] at h2
  exact sub_eq_zero.mp h2

end UnforcedLeray.Short.IIb
