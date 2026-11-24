import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2

/-!


Source: `the November 2 reference manuscript` lines 2347-2352.

Picard iteration `p₀ = c`, `p_{n+1} = sqVolterra lam c p_n` on all of `ℝ`.  On `|u| ≤ T` with
`|a| ≤ M = 4L` there, `|p_{n+1} - p_n|(u) ≤ D (L|u|)^n / n!`; the series converges locally
uniformly, the limit is continuous and solves the equation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem sqEx_coeff_continuous (lam : ℂ) (hl : 0 < lam.re) : Continuous (sqCoeff lam) := by
  unfold sqCoeff
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro u h0
  have := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat] at this
  linarith

/-- The inner integral. -/
def sqPhi (lam : ℂ) (p : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))

theorem sqEx_integrand_continuous (lam : ℂ) (hl : 0 < lam.re) (p : ℝ → ℂ) (hp : Continuous p)
    (v : ℝ) :
    Continuous fun t : ℝ => (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t)) := by
  have ha := sqEx_coeff_continuous lam hl
  fun_prop

theorem sqPhi_continuous (lam : ℂ) (hl : 0 < lam.re) (p : ℝ → ℂ) (hp : Continuous p) :
    Continuous (sqPhi lam p) := by
  have ha := sqEx_coeff_continuous lam hl
  have hf : Continuous (Function.uncurry fun (v : ℝ) (t : ℝ) =>
      (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))) := by
    show Continuous fun x : ℝ × ℝ => ((x.2 : ℝ) : ℂ) ^ 2 * (sqCoeff lam (x.1 * x.2) * p (x.1 * x.2))
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

theorem sqVolterra_continuous (lam c : ℂ) (hl : 0 < lam.re) (p : ℝ → ℂ) (hp : Continuous p) :
    Continuous (sqVolterra lam c p) := by
  have hg : Continuous fun v : ℝ => (1 / 4 : ℂ) * sqPhi lam p v :=
    continuous_const.mul (sqPhi_continuous lam hl p hp)
  have := intervalIntegral.continuous_primitive (μ := volume) (fun a b => hg.intervalIntegrable a b) 0
  exact continuous_const.add this

theorem sqPhi_sub (lam : ℂ) (hl : 0 < lam.re) (p q : ℝ → ℂ) (hp : Continuous p)
    (hq : Continuous q) (v : ℝ) :
    sqPhi lam (fun w => p w - q w) v = sqPhi lam p v - sqPhi lam q v := by
  unfold sqPhi
  rw [← intervalIntegral.integral_sub
    ((sqEx_integrand_continuous lam hl p hp v).intervalIntegrable 0 1)
    ((sqEx_integrand_continuous lam hl q hq v).intervalIntegrable 0 1)]
  congr 1
  ext t
  ring

theorem sqVolterra_sub (lam c : ℂ) (hl : 0 < lam.re) (p q : ℝ → ℂ) (hp : Continuous p)
    (hq : Continuous q) (u : ℝ) :
    sqVolterra lam c p u - sqVolterra lam c q u =
      ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * sqPhi lam (fun w => p w - q w) v := by
  have h1 : Continuous fun v : ℝ => (1 / 4 : ℂ) * sqPhi lam p v :=
    continuous_const.mul (sqPhi_continuous lam hl p hp)
  have h2 : Continuous fun v : ℝ => (1 / 4 : ℂ) * sqPhi lam q v :=
    continuous_const.mul (sqPhi_continuous lam hl q hq)
  show (c + ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * sqPhi lam p v) -
      (c + ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * sqPhi lam q v) = _
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (h1.intervalIntegrable 0 u)
    (h2.intervalIntegrable 0 u)]
  congr 1
  ext v
  rw [sqPhi_sub lam hl p q hp hq v]
  ring

theorem sqPhi_bound (lam : ℂ) (p : ℝ → ℂ) (M E T v : ℝ)
    (hM : ∀ s : ℝ, |s| ≤ T → ‖sqCoeff lam s‖ ≤ M) (hv : |v| ≤ T)
    (hE : ∀ w : ℝ, |w| ≤ |v| → ‖p w‖ ≤ E) : ‖sqPhi lam p v‖ ≤ M * E := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simpa using (abs_nonneg v).trans hv))
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hE 0 (by simp))
  unfold sqPhi
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M * E)
    (f := fun t : ℝ => (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))) (fun t ht => ?_)
  · simpa using this
  · rw [Set.uIoc_of_le zero_le_one] at ht
    have hvt : |v * t| ≤ |v| := by
      rw [abs_mul, abs_of_pos ht.1]
      exact mul_le_of_le_one_right (abs_nonneg v) ht.2
    have h1 : ‖sqCoeff lam (v * t)‖ ≤ M := hM _ (hvt.trans hv)
    have h2 : ‖p (v * t)‖ ≤ E := hE _ hvt
    have h3 : ‖(t : ℂ) ^ 2‖ ≤ 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact pow_le_one₀ ht.1.le ht.2
    rw [norm_mul, norm_mul]
    calc ‖(t : ℂ) ^ 2‖ * (‖sqCoeff lam (v * t)‖ * ‖p (v * t)‖) ≤ 1 * (M * E) :=
          mul_le_mul h3 (mul_le_mul h1 h2 (norm_nonneg _) hM0) (by positivity) zero_le_one
      _ = M * E := one_mul _

theorem int_pow_bound (f : ℝ → ℂ) (K : ℝ) (n : ℕ) (u : ℝ) (hK : 0 ≤ K)
    (h : ∀ v : ℝ, |v| ≤ |u| → ‖f v‖ ≤ K * |v| ^ n) :
    ‖∫ v in (0 : ℝ)..u, f v‖ ≤ K * |u| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 u with hu | hu
  · have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f) (g := fun v => K * v ^ n) hu
      (Filter.Eventually.of_forall fun t ht => ?_)
      ((by fun_prop : Continuous fun v : ℝ => K * v ^ n).intervalIntegrable 0 u)
    · have e : ∫ v in (0 : ℝ)..u, K * v ^ n = K * |u| ^ (n + 1) / (n + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow, abs_of_nonneg hu]
        simp
        ring
      rw [e] at this
      exact this
    · have h1 := h t (by rw [abs_of_pos ht.1, abs_of_nonneg hu]; exact ht.2)
      rwa [abs_of_pos ht.1] at h1
  · rw [intervalIntegral.integral_symm, norm_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f) (g := fun v => K * (-v) ^ n) hu
      (Filter.Eventually.of_forall fun t ht => ?_)
      ((by fun_prop : Continuous fun v : ℝ => K * (-v) ^ n).intervalIntegrable u 0)
    · have e : ∫ v in u..(0 : ℝ), K * (-v) ^ n = K * |u| ^ (n + 1) / (n + 1) := by
        have := intervalIntegral.integral_comp_neg (a := u) (b := 0) (fun x : ℝ => K * x ^ n)
        try simp only at this
        rw [this, intervalIntegral.integral_const_mul, integral_pow, abs_of_nonpos hu]
        simp
        ring
      rw [e] at this
      exact this
    · have hneg : |t| = -t := abs_of_nonpos ht.2
      have h1 := h t (by rw [hneg, abs_of_nonpos hu]; linarith [ht.1])
      rwa [hneg] at h1

theorem sqEx_coeff_bound (lam : ℂ) (hl : 0 < lam.re) (T : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℝ, |s| ≤ T → ‖sqCoeff lam s‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (sqEx_coeff_continuous lam hl).continuousOn
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun s hs => ?_⟩
  exact (hC s (abs_le.mp hs)).trans (le_max_left _ _)

/-- The Picard iterates. -/
def sqPicard (lam c : ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => c
  | n + 1 => sqVolterra lam c (sqPicard lam c n)

/-- Successive differences of the Picard iterates. -/
def sqDiff (lam c : ℂ) (n : ℕ) (u : ℝ) : ℂ := sqPicard lam c (n + 1) u - sqPicard lam c n u

theorem sqPicard_continuous (lam c : ℂ) (hl : 0 < lam.re) :
    ∀ n : ℕ, Continuous (sqPicard lam c n)
  | 0 => continuous_const
  | n + 1 => sqVolterra_continuous lam c hl _ (sqPicard_continuous lam c hl n)

theorem sqDiff_continuous (lam c : ℂ) (hl : 0 < lam.re) (n : ℕ) : Continuous (sqDiff lam c n) :=
  (sqPicard_continuous lam c hl (n + 1)).sub (sqPicard_continuous lam c hl n)

theorem sqPicard_sum (lam c : ℂ) (n : ℕ) (u : ℝ) :
    sqPicard lam c n u = c + ∑ k ∈ Finset.range n, sqDiff lam c k u := by
  induction n with
  | zero => simp [sqPicard]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    unfold sqDiff
    ring

theorem sqDiff_bound (lam c : ℂ) (hl : 0 < lam.re) (T : ℝ) :
    ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧ ∀ (n : ℕ) (u : ℝ), |u| ≤ T →
      ‖sqDiff lam c n u‖ ≤ D * (L * |u|) ^ n / (n.factorial : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := sqEx_coeff_bound lam hl T
  obtain ⟨D0, hD0⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (sqDiff_continuous lam c hl 0).continuousOn
  have hD : ∀ u : ℝ, |u| ≤ T → ‖sqDiff lam c 0 u‖ ≤ max D0 0 := fun u hu =>
    (hD0 u (abs_le.mp hu)).trans (le_max_left _ _)
  set D : ℝ := max D0 0 with hDdef
  have hDnn : 0 ≤ D := le_max_right _ _
  set L : ℝ := M / 4 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hML : M = 4 * L := by rw [hLdef]; ring
  refine ⟨L, D, hL0, hDnn, ?_⟩
  intro n
  induction n with
  | zero => intro u hu; simpa using hD u hu
  | succ n ih =>
    intro u hu
    have hp := sqPicard_continuous lam c hl
    have hsub : sqDiff lam c (n + 1) u =
        ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * sqPhi lam (fun w => sqDiff lam c n w) v :=
      sqVolterra_sub lam c hl (sqPicard lam c (n + 1)) (sqPicard lam c n) (hp _) (hp _) u
    rw [hsub]
    have hfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have key := int_pow_bound (fun v => (1 / 4 : ℂ) * sqPhi lam (fun w => sqDiff lam c n w) v)
      (M * D * L ^ n / (4 * (n.factorial : ℝ))) n u (by positivity) (fun v hv => ?_)
    · refine key.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      push_cast
      rw [hML]
      field_simp
      ring
    · have hvT : |v| ≤ T := hv.trans hu
      have hE : ∀ w : ℝ, |w| ≤ |v| → ‖sqDiff lam c n w‖ ≤ D * (L * |v|) ^ n / (n.factorial : ℝ) := by
        intro w hw
        refine (ih w (hw.trans hvT)).trans ?_
        have : (L * |w|) ^ n ≤ (L * |v|) ^ n :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hw hL0) n
        gcongr
      have hb := sqPhi_bound lam (fun w => sqDiff lam c n w) M _ T v hM hvT hE
      rw [norm_mul]
      have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
      rw [h4]
      calc 1 / 4 * ‖sqPhi lam (fun w => sqDiff lam c n w) v‖
          ≤ 1 / 4 * (M * (D * (L * |v|) ^ n / (n.factorial : ℝ))) := by gcongr
        _ = M * D * L ^ n / (4 * (n.factorial : ℝ)) * |v| ^ n := by
            rw [mul_pow]; field_simp

theorem sqDiff_summable_bound (lam c : ℂ) (hl : 0 < lam.re) (T : ℝ) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ (n : ℕ) (u : ℝ), |u| ≤ T → ‖sqDiff lam c n u‖ ≤ b n := by
  obtain ⟨L, D, hL, hD, h⟩ := sqDiff_bound lam c hl T
  refine ⟨fun n => D * ((L * T) ^ n / (n.factorial : ℝ)), ?_, fun n u hu => ?_⟩
  · exact (Real.summable_pow_div_factorial (L * T)).mul_left D
  · refine (h n u hu).trans ?_
    have : (L * |u|) ^ n ≤ (L * T) ^ n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hu hL) n
    show D * (L * |u|) ^ n / (n.factorial : ℝ) ≤ D * ((L * T) ^ n / (n.factorial : ℝ))
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this (by positivity)) hD

/-- **Leaf 3** (existence on all of `ℝ`, Picard iteration). -/
theorem sqVolterraExists : UnforcedLeray.Short.IIb.SqVolterraExists := by
  intro lam c hl
  have hp := sqPicard_continuous lam c hl
  -- summability pointwise
  have hsum : ∀ u : ℝ, Summable fun k => sqDiff lam c k u := by
    intro u
    obtain ⟨b, hb, hbd⟩ := sqDiff_summable_bound lam c hl |u|
    exact Summable.of_norm_bounded hb (fun k => hbd k u le_rfl)
  set p : ℝ → ℂ := fun u => c + ∑' k, sqDiff lam c k u with hpdef
  have hconv : ∀ u : ℝ, Tendsto (fun n => sqPicard lam c n u) atTop (𝓝 (p u)) := by
    intro u
    have := ((hsum u).hasSum.tendsto_sum_nat).const_add c
    simpa [sqPicard_sum, hpdef] using this
  -- continuity
  have pcont : Continuous p := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨b, hb, hbd⟩ := sqDiff_summable_bound lam c hl (|x| + 1)
    have hon : ContinuousOn (fun u => ∑' k, sqDiff lam c k u) (Icc (-(|x| + 1)) (|x| + 1)) :=
      continuousOn_tsum (fun k => (sqDiff_continuous lam c hl k).continuousOn) hb
        (fun k u hu => hbd k u (abs_le.mpr hu))
    have hmem : Icc (-(|x| + 1)) (|x| + 1) ∈ 𝓝 x := by
      apply Icc_mem_nhds
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    exact (continuousAt_const.add (hon.continuousAt hmem))
  refine ⟨p, pcont, fun u => ?_⟩
  -- tail estimate
  obtain ⟨b, hb, hbd⟩ := sqDiff_summable_bound lam c hl |u|
  obtain ⟨M, hM0, hM⟩ := sqEx_coeff_bound lam hl |u|
  set r : ℕ → ℝ := fun n => ∑' k, b (k + n) with hr
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_sum_nat_add b
  have htail : ∀ n : ℕ, ∀ w : ℝ, |w| ≤ |u| → ‖p w - sqPicard lam c n w‖ ≤ r n := by
    intro n w hw
    have hs := hsum w
    have h1 := hs.sum_add_tsum_nat_add n
    have hbs : Summable fun k => b (k + n) := (summable_nat_add_iff n).mpr hb
    have h2 : ‖∑' k, sqDiff lam c (k + n) w‖ ≤ r n :=
      tsum_of_norm_bounded hbs.hasSum (fun k => hbd (k + n) w hw)
    have : p w - sqPicard lam c n w = ∑' k, sqDiff lam c (k + n) w := by
      rw [hpdef, sqPicard_sum]
      simp only
      rw [← h1]
      ring
    rwa [this]
  have hdiff : ∀ n : ℕ, ‖sqVolterra lam c p u - sqVolterra lam c (sqPicard lam c n) u‖ ≤
      (1 / 4 * (M * r n)) * |u| := by
    intro n
    rw [sqVolterra_sub lam c hl p (sqPicard lam c n) pcont (hp n) u]
    have key := int_pow_bound (fun v => (1 / 4 : ℂ) *
      sqPhi lam (fun w => p w - sqPicard lam c n w) v) (1 / 4 * (M * r n)) 0 u
      (by
        have : 0 ≤ r n := le_trans (norm_nonneg _) (htail n 0 (by simp))
        positivity) (fun v hv => ?_)
    · simpa using key
    · have hb' := sqPhi_bound lam (fun w => p w - sqPicard lam c n w) M (r n) |u| v hM hv
        (fun w hw => htail n w (hw.trans hv))
      rw [norm_mul]
      have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
      rw [h4]
      simp only [pow_zero, mul_one]
      gcongr
  have hlim1 : Tendsto (fun n => sqVolterra lam c (sqPicard lam c n) u) atTop
      (𝓝 (sqVolterra lam c p u)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (g := fun n => (1 / 4 * (M * r n)) * |u|) ?_
    · rw [norm_sub_rev]; exact hdiff _
    · have := ((hr0.const_mul M).const_mul (1 / 4 : ℝ)).mul_const |u|
      simpa using this
  have hlim2 : Tendsto (fun n => sqVolterra lam c (sqPicard lam c n) u) atTop (𝓝 (p u)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hconv u)
  exact tendsto_nhds_unique hlim2 hlim1

end UnforcedLeray.Short.IIb
