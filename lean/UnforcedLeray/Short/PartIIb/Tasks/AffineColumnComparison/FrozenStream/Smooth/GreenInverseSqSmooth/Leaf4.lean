import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2

/-!


Source: `the November 2 reference manuscript` lines 2347-2352.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The eigen-coefficient is smooth on `ℝ` when `Re lam > 0`. -/
theorem sqCoeff_contDiff_aux (lam : ℂ) (hl : 0 < lam.re) (n : WithTop ℕ∞) :
    ContDiff ℝ n (sqCoeff lam) := by
  unfold sqCoeff
  have hexp : ContDiff ℝ n (fun u : ℝ => Real.exp (-u / 4)) := by fun_prop
  have hexpC : ContDiff ℝ n (fun u : ℝ => ((Real.exp (-u / 4) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp
  have hpoly : ContDiff ℝ n (fun u : ℝ => (u / 4 - 2) * Real.exp (-u / 4)) := by fun_prop
  have hnum : ContDiff ℝ n (fun u : ℝ => (((u / 4 - 2) * Real.exp (-u / 4) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hpoly
  have hden : ContDiff ℝ n (fun u : ℝ => lam + 2 * Complex.I * ((Real.exp (-u / 4) : ℝ) : ℂ)) := by
    fun_prop
  have hne : ∀ u : ℝ, lam + 2 * Complex.I * ((Real.exp (-u / 4) : ℝ) : ℂ) ≠ 0 := by
    intro u h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat] at this
    linarith
  have hinv := hden.inv hne
  simp only [div_eq_mul_inv]
  exact ((contDiff_const.mul contDiff_const).mul hnum).mul hinv

/-- Parametric smoothness of `v ↦ ∫₀¹ tᵐ h(vt) dt` when `h` is `C^k`. -/
theorem param_contDiff_aux (k : ℕ) :
    ∀ (m : ℕ) (h : ℝ → ℂ), ContDiff ℝ (k : WithTop ℕ∞) h →
      ContDiff ℝ (k : WithTop ℕ∞) (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * h (v * t)) := by
  induction k with
  | zero =>
    intro m h hh
    have hc : Continuous h := hh.continuous
    have hf : Continuous (Function.uncurry fun (v : ℝ) (t : ℝ) => (t : ℂ) ^ m * h (v * t)) := by
      have : Continuous (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ m * h (p.1 * p.2)) :=
        ((Complex.continuous_ofReal.comp continuous_snd).pow m).mul
          (hc.comp (continuous_fst.mul continuous_snd))
      exact this
    simp only [Nat.cast_zero]
    exact contDiff_zero.mpr (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1)
  | succ k ih =>
    intro m h hh
    have hh' : ContDiff ℝ ((k : WithTop ℕ∞) + 1) h := by exact_mod_cast hh
    obtain ⟨hdiff, -, hdh⟩ := contDiff_succ_iff_deriv.mp hh'
    have hcont : Continuous h := hh'.continuous
    have hcd : Continuous (deriv h) := hdh.continuous
    have hderiv : ∀ v0 : ℝ, HasDerivAt (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * h (v * t))
        (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (m + 1) * deriv h (v0 * t)) v0 := by
      intro v0
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(|v0| + 1)) (b := |v0| + 1)).exists_bound_of_continuousOn
        hcd.continuousOn
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (F := fun x t => (t : ℂ) ^ m * h (x * t))
        (F' := fun x t => (t : ℂ) ^ (m + 1) * deriv h (x * t))
        (x₀ := v0) (s := Metric.ball v0 1) (bound := fun _ => C) (a := 0) (b := 1)
        (Metric.ball_mem_nhds v0 one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
      · exact Eventually.of_forall fun x => (by fun_prop : Continuous fun t : ℝ =>
          (t : ℂ) ^ m * h (x * t)).aestronglyMeasurable
      · exact (by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ m * h (v0 * t)).intervalIntegrable 0 1
      · exact (by fun_prop : Continuous fun t : ℝ =>
          (t : ℂ) ^ (m + 1) * deriv h (v0 * t)).aestronglyMeasurable
      · refine Eventually.of_forall fun t ht x hx => ?_
        have ht' : 0 < t ∧ t ≤ 1 := by
          rw [Set.uIoc_of_le zero_le_one] at ht
          exact ht
        have h1 : |x - v0| < 1 := by
          have := Metric.mem_ball.mp hx
          rwa [Real.dist_eq] at this
        have h2 : |x| ≤ |v0| + |x - v0| := by
          calc |x| = |v0 + (x - v0)| := by congr 1; ring
            _ ≤ |v0| + |x - v0| := abs_add_le _ _
        have habs : |x * t| ≤ |v0| + 1 := by
          rw [abs_mul, abs_of_pos ht'.1]
          nlinarith [abs_nonneg x]
        have hxt : x * t ∈ Icc (-(|v0| + 1)) (|v0| + 1) := abs_le.mp habs
        have hd : ‖deriv h (x * t)‖ ≤ C := hC (x * t) hxt
        have htp : ‖(t : ℂ) ^ (m + 1)‖ ≤ 1 := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'.1]
          exact pow_le_one₀ ht'.1.le ht'.2
        calc ‖(t : ℂ) ^ (m + 1) * deriv h (x * t)‖
            = ‖(t : ℂ) ^ (m + 1)‖ * ‖deriv h (x * t)‖ := norm_mul _ _
          _ ≤ 1 * C := mul_le_mul htp hd (norm_nonneg _) zero_le_one
          _ = C := one_mul C
      · refine Eventually.of_forall fun t _ x _ => ?_
        have hlin : HasDerivAt (fun x : ℝ => x * t) t x := by
          simpa using (hasDerivAt_id x).mul_const t
        have hcomp := (hdiff (x * t)).hasDerivAt.scomp x hlin
        have := hcomp.const_mul ((t : ℂ) ^ m)
        have e : (t : ℂ) ^ (m + 1) * deriv h (x * t) = (t : ℂ) ^ m * (t • deriv h (x * t)) := by
          rw [Complex.real_smul]; ring
        rw [e]
        exact this
    have hderivEq : deriv (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * h (v * t)) =
        fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (m + 1) * deriv h (v * t) :=
      funext fun v => (hderiv v).deriv
    have hIH := ih (m + 1) (deriv h) hdh
    have hgoal : ContDiff ℝ ((k : WithTop ℕ∞) + 1)
        (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * h (v * t)) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun v => (hderiv v).differentiableAt, fun h' => absurd h' (WithTop.natCast_ne_top k), ?_⟩
      rw [hderivEq]
      exact hIH
    exact_mod_cast hgoal

/-- **Leaf 4** (bootstrap): a continuous solution of the Volterra equation on `ℝ` is `C^∞`. -/
theorem sqVolterraSmooth : UnforcedLeray.Short.IIb.SqVolterraSmooth := by
  intro lam c hl p hp hvol
  have key : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) p := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero]
      exact contDiff_zero.mpr hp
    | succ n ih =>
      have hh : ContDiff ℝ (n : WithTop ℕ∞) (fun s => sqCoeff lam s * p s) :=
        (sqCoeff_contDiff_aux lam hl _).mul ih
      have hΦ : ContDiff ℝ (n : WithTop ℕ∞) (fun v : ℝ => ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))) := param_contDiff_aux n 2 _ hh
      have hΦc : Continuous (fun v : ℝ => ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))) := hΦ.continuous
      have hcomp : ∀ u : ℝ, HasDerivAt
          (fun u : ℝ => c + ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
            (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t)))
          ((1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * (sqCoeff lam (u * t) * p (u * t))) u :=
        fun u => (((hΦc.const_mul (1 / 4 : ℂ)).integral_hasStrictDerivAt 0 u).hasDerivAt).const_add c
      have hfun : (fun u : ℝ => c + ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))) = p :=
        funext fun u => (hvol u).symm
      have hdiffp : ∀ u : ℝ, HasDerivAt p ((1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * (sqCoeff lam (u * t) * p (u * t))) u := by
        intro u
        have h1 := hcomp u
        rw [hfun] at h1
        exact h1
      have hderivp : deriv p = fun u : ℝ => (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * (sqCoeff lam (u * t) * p (u * t)) :=
        funext fun u => (hdiffp u).deriv
      have hpdiff : ContDiff ℝ ((n : WithTop ℕ∞) + 1) p := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨fun u => (hdiffp u).differentiableAt, fun h' => absurd h' (WithTop.natCast_ne_top n), ?_⟩
        rw [hderivp]
        exact contDiff_const.mul hΦ
      exact_mod_cast hpdiff
  exact contDiff_infty.mpr key

end UnforcedLeray.Short.IIb
