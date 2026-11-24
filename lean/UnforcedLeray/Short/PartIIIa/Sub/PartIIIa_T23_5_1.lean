import UnforcedLeray.Short.PartIIIa.Sub.T23_5_Leaves
import Mathlib.Analysis.Complex.Exponential

/-!
# `PeriodicStreamTail` from three analytic leaves (SP 2349-2358)

Source `the November 2 reference manuscript` 2349-2358: for `r ≥ 1` the Green
inverse of the Gaussian angular-two eigenprofile is a harmonic quadrupole plus a Gaussian remainder,
`R q(r) = -(M/4) r⁻² + G(r)`, `M = ∫₀^∞ s³ q`, `|G| + |G'| ≲ e^{-r²/16}`; the quadrupole
`r⁻²e^{2iϑ} = (x₁ - i x₂)⁻²` periodizes to `c⁻² (π/c)... csc²`-type sums with decay
`e^{-2π|η|/c}` (`∑_n (w+n)⁻² = π² csc²(πw)`); the Gaussian part periodizes with the bound
`∑_k e^{-(ξ+kc)²/16} ≤ C` for `c ≥ 1`.

Leaves (Prop definitions, each with its source): `HarmonicPeriodicDecay` (2354-2356),
`GaussianPeriodicDecay` (2356-2358), `GreenRemainder` (2349-2352).  Proved here:
`periodicStreamTail_of` (termwise splitting of the tsum, differentiation of the sum, weight
absorption).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Blueprint

/-- The `k`-th term `(u_k - iη)⁻²`, `u_k = ξ + kc`, of the periodized harmonic quadrupole
`r⁻²e^{2iϑ} = (ξ - iη)⁻²`. -/
def harmTerm (c : ℝ) (y : ℝ × ℝ) (k : ℤ) : ℂ :=
  ((((y.1 + (k : ℝ) * c : ℝ) : ℂ) - (y.2 : ℂ) * Complex.I)⁻¹) ^ 2

/-- The periodized harmonic quadrupole `∑_k (ξ + kc - iη)⁻²`. -/
def harmPeriodic (c : ℝ) (y : ℝ × ℝ) : ℂ := ∑' k : ℤ, harmTerm c y k

/-- The `k`-th term `G(|(ξ+kc, η)|) e^{2iϑ}` of the periodized Gaussian remainder. -/
def gaussTerm (Gf : ℝ → ℂ) (c : ℝ) (y : ℝ × ℝ) (k : ℤ) : ℂ :=
  Gf (Real.sqrt ((y.1 + (k : ℝ) * c) ^ 2 + y.2 ^ 2)) * angularTwo (y.1 + (k : ℝ) * c, y.2)

/-- The periodized Gaussian remainder. -/
def gaussPeriodic (Gf : ℝ → ℂ) (c : ℝ) (y : ℝ × ℝ) : ℂ := ∑' k : ℤ, gaussTerm Gf c y k

/-- The Gaussian remainder `G(s) = R q(s) + (M/4) s⁻²` of the Green inverse. -/
def greenRem (q : Planar.Profile) (M : ℂ) (s : ℝ) : ℂ :=
  Planar.greenInverse q s + (M / 4) * (((s : ℂ) ^ 2)⁻¹)

/-- **Leaf 1: the periodized harmonic quadrupole** (SP 2354-2356: `∑_n (q+nc+iη)^{-2} =
(π/c)² csc²(π(q+iη)/c)`, exponentially small for `|η| ≥ c`).  For `c > 0` and `η ≠ 0` the series
`∑_k (ξ+kc-iη)⁻²` converges absolutely and defines a function differentiable at `(ξ,η)`; and
there is `C_h` with `|H_c(y)| + ‖DH_c(y)‖ ≤ C_h e^{-2π|η|/c}` for `c ≥ 1`, `|η| ≥ c`
(`H_c = c⁻²∑_n (w+n)⁻²`, `w = (ξ-iη)/c`, `|Im w| ≥ 1`; route: Mathlib
`iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`, `pi_mul_cot_pi_q_exp`). -/
def HarmonicPeriodicDecay : Prop :=
  (∀ c : ℝ, 0 < c → ∀ y : ℝ × ℝ, y.2 ≠ 0 →
      Summable (harmTerm c y) ∧ DifferentiableAt ℝ (harmPeriodic c) y) ∧
  ∃ Ch : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ y : ℝ × ℝ, c ≤ |y.2| →
    ‖harmPeriodic c y‖ + ‖fderiv ℝ (harmPeriodic c) y‖ ≤
      Ch * Real.exp (-(2 * Real.pi * (|y.2| / c)))

/-- **Leaf 2: the periodized Gaussian remainder** (SP 2356-2358: `|G| + |G'| ≲ e^{-r²/16}` and
`∑_k e^{-(ξ+kc)²/16} ≤ C` for `c ≥ 1`; `|∇(G e^{2iϑ})| ≤ |G'| + 2|G|/r`).  For every
`G : ℝ → ℂ` differentiable with `|G| + |G'| ≤ C_G e^{-r²/16}` on `r ≥ 1/2`: for `c > 0` and
`|η| > 1/2` the series `∑_k G(r_k)e^{2iϑ_k}` converges absolutely and is differentiable at
`(ξ,η)`; and there is `C_p` with `|P(y)| + ‖DP(y)‖ ≤ C_p e^{-η²/16}` for `c ≥ 1`, `|η| ≥ c`
(`hasFDerivAt_tsum` with the Gaussian majorant). -/
def GaussianPeriodicDecay : Prop :=
  ∀ (Gf : ℝ → ℂ) (CG : ℝ),
    (∀ r : ℝ, 1 / 2 ≤ r → DifferentiableAt ℝ Gf r ∧
      ‖Gf r‖ + ‖deriv Gf r‖ ≤ CG * Real.exp (-(r ^ 2 / 16))) →
    (∀ c : ℝ, 0 < c → ∀ y : ℝ × ℝ, 1 / 2 < |y.2| →
      Summable (gaussTerm Gf c y) ∧ DifferentiableAt ℝ (gaussPeriodic Gf c) y) ∧
    ∃ Cp : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ y : ℝ × ℝ, c ≤ |y.2| →
      ‖gaussPeriodic Gf c y‖ + ‖fderiv ℝ (gaussPeriodic Gf c) y‖ ≤ Cp * Real.exp (-(y.2 ^ 2 / 16))

/-- **Leaf 3: the Green inverse of the eigenprofile = harmonic quadrupole + Gaussian remainder**
(SP 2349-2352; `M = ∫₀^∞ s³ q`, convergent by Cauchy-Schwarz against the Gaussian weight of
`MemXG`; `G(r) = ¼[r⁻²∫_r^∞ s³q - r²∫_r^∞ q/s]`, in `G'` the terms `r q(r)` cancel).  For the
growing eigenpair `(λ, q)` there are `M, C_G` with `G = greenRem q M` differentiable on `r ≥ 1/2`
and `|G| + |G'| ≤ C_G e^{-r²/16}` there. -/
def GreenRemainder : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∃ (M : ℂ) (CG : ℝ), ∀ r : ℝ, 1 / 2 ≤ r → DifferentiableAt ℝ (greenRem q M) r ∧
      ‖greenRem q M r‖ + ‖deriv (greenRem q M) r‖ ≤ CG * Real.exp (-(r ^ 2 / 16))

/-! ## Termwise splitting -/

theorem harm_id (u v : ℝ) (hv : v ≠ 0) :
    (((Real.sqrt (u ^ 2 + v ^ 2) : ℝ) : ℂ) ^ 2)⁻¹ * angularTwo (u, v) =
      (((u : ℂ) - (v : ℂ) * Complex.I)⁻¹) ^ 2 := by
  have hs : 0 < u ^ 2 + v ^ 2 := by positivity
  have hr : ((Real.sqrt (u ^ 2 + v ^ 2) : ℝ) : ℂ) ^ 2 = ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]; push_cast; ring
  have hzw : ((u : ℂ) + v * Complex.I) * ((u : ℂ) - v * Complex.I) = (u : ℂ) ^ 2 + (v : ℂ) ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  have hw : (u : ℂ) - v * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hv this
  have hz : (u : ℂ) + v * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hv this
  unfold angularTwo
  have hang : (((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 / (((u ^ 2 + v ^ 2 : ℝ)) : ℂ)) =
      ((u : ℂ) + v * Complex.I) ^ 2 / ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) := by push_cast; ring
  dsimp only
  rw [hang, hr, ← hzw]
  field_simp

theorem planarStream_split (q : Planar.Profile) (M : ℂ) (c : ℝ) (y : ℝ × ℝ) (k : ℤ)
    (hy : y.2 ≠ 0) :
    planarStream q (y.1 + (k : ℝ) * c, y.2) =
      (-(M / 4)) * harmTerm c y k + gaussTerm (greenRem q M) c y k := by
  have hid := harm_id (y.1 + (k : ℝ) * c) y.2 hy
  unfold planarStream gaussTerm harmTerm greenRem
  dsimp only
  linear_combination (-(M / 4)) * hid

/-! ## Weight absorption -/

theorem weight_absorb (m : ℕ) {a : ℝ} (ha : 0 < a) {c η : ℝ} (hc : 1 ≤ c) (hη : c ≤ η) :
    (1 + η) ^ m * Real.exp (-(2 * a * η / c)) ≤
      (2 ^ m * (m.factorial / a ^ m)) * c ^ m * Real.exp (-(a * η / c)) := by
  have hc0 : 0 < c := by linarith
  set t : ℝ := η / c with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hc0]; linarith
  have hη' : η = c * t := by rw [ht]; field_simp
  have h1 : (1 + η) ^ m ≤ (2 * c * t) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    rw [hη']; nlinarith
  have h2 : (a * t) ^ m / m.factorial ≤ Real.exp (a * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h3 : t ^ m ≤ m.factorial / a ^ m * Real.exp (a * t) := by
    have : (a * t) ^ m ≤ m.factorial * Real.exp (a * t) :=
      ((div_le_iff₀ hfac).1 h2).trans_eq (mul_comm _ _)
    rw [mul_pow] at this
    have hpa : 0 < a ^ m := pow_pos ha m
    rw [div_mul_eq_mul_div, le_div_iff₀ hpa]
    linarith
  have e1 : Real.exp (-(2 * a * η / c)) = Real.exp (-(a * t)) * Real.exp (-(a * t)) := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have e2 : Real.exp (-(a * η / c)) = Real.exp (-(a * t)) := by congr 1; rw [ht]; ring
  have hEa : Real.exp (-(a * t)) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 + η) ^ m * Real.exp (-(2 * a * η / c))
      ≤ (2 * c * t) ^ m * Real.exp (-(2 * a * η / c)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 ^ m * c ^ m * t ^ m * (Real.exp (-(a * t)) * Real.exp (-(a * t))) := by
        rw [e1, mul_pow, mul_pow]
    _ ≤ 2 ^ m * c ^ m * (m.factorial / a ^ m * Real.exp (a * t)) *
          (Real.exp (-(a * t)) * Real.exp (-(a * t))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (2 ^ m * (m.factorial / a ^ m)) * c ^ m * Real.exp (-(a * η / c)) := by
        rw [e2]
        have : Real.exp (a * t) * (Real.exp (-(a * t)) * Real.exp (-(a * t))) =
            Real.exp (-(a * t)) := by
          rw [← mul_assoc, mul_comm (Real.exp (a * t)), hEa, one_mul]
        calc 2 ^ m * c ^ m * (↑m.factorial / a ^ m * Real.exp (a * t)) *
              (Real.exp (-(a * t)) * Real.exp (-(a * t)))
            = 2 ^ m * c ^ m * (↑m.factorial / a ^ m) *
              (Real.exp (a * t) * (Real.exp (-(a * t)) * Real.exp (-(a * t)))) := by ring
          _ = _ := by rw [this]; ring

/-! ## The reduction -/

theorem periodicStreamTail_of (h1 : HarmonicPeriodicDecay) (h2 : GaussianPeriodicDecay)
    (h3 : GreenRemainder) : PeriodicStreamTail := by
  intro lam q hq m
  obtain ⟨M, CG, hG⟩ := h3 lam q hq
  obtain ⟨hHs, Ch, hH⟩ := h1
  obtain ⟨hGs, Cp, hP⟩ := h2 (greenRem q M) CG hG
  set a : ℝ := 1 / 32 with ha
  have ha0 : 0 < a := by norm_num [ha]
  set B : ℝ := ‖M / 4‖ * |Ch| + |Cp| with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨a, 2 ^ m * (m.factorial / a ^ m) * B, m, ha0, ?_⟩
  intro c hc x hx
  have hc0 : 0 < c := by linarith
  have hx1 : 1 ≤ |x.2| := hc.trans hx
  have hx2 : (1 / 2 : ℝ) < |x.2| := by linarith
  -- equality of the periodized stream with the two pieces near `x`
  have hEq : ∀ y : ℝ × ℝ, 1 / 2 < |y.2| →
      periodicStream q c y = (-(M / 4)) * harmPeriodic c y + gaussPeriodic (greenRem q M) c y := by
    intro y hy
    have hy0 : y.2 ≠ 0 := by
      intro h; rw [h] at hy; simp at hy; linarith
    obtain ⟨s1, -⟩ := hHs c hc0 y hy0
    obtain ⟨s2, -⟩ := hGs c hc0 y hy
    unfold periodicStream harmPeriodic gaussPeriodic
    rw [← tsum_mul_left, ← Summable.tsum_add (s1.mul_left _) s2]
    exact tsum_congr fun k => planarStream_split q M c y k hy0
  have hnhds : {y : ℝ × ℝ | 1 / 2 < |y.2|} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_abs.comp continuous_snd)).mem_nhds hx2
  have hev : periodicStream q c =ᶠ[𝓝 x]
      fun y => (-(M / 4)) * harmPeriodic c y + gaussPeriodic (greenRem q M) c y :=
    Filter.eventually_of_mem hnhds fun y hy => hEq y hy
  have hx0 : x.2 ≠ 0 := by intro h; rw [h] at hx1; simp at hx1; linarith
  have dH := (hHs c hc0 x hx0).2
  have dG := (hGs c hc0 x hx2).2
  have dP : DifferentiableAt ℝ (fun y => (-(M / 4)) * harmPeriodic c y +
      gaussPeriodic (greenRem q M) c y) x := (dH.const_mul _).add dG
  have hD : DifferentiableAt ℝ (periodicStream q c) x := dP.congr_of_eventuallyEq hev
  refine ⟨hD, ?_⟩
  have hfd : fderiv ℝ (periodicStream q c) x =
      (-(M / 4)) • fderiv ℝ (harmPeriodic c) x + fderiv ℝ (gaussPeriodic (greenRem q M) c) x := by
    rw [hev.fderiv_eq]
    exact ((dH.hasFDerivAt.const_mul (-(M / 4))).add dG.hasFDerivAt).fderiv
  rw [hEq x hx2, hfd]
  have bH := hH c hc x hx
  have bP := hP c hc x hx
  have hexpP : Real.exp (-(x.2 ^ 2 / 16)) ≤ Real.exp (-(2 * a * |x.2| / c)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    have hsq : x.2 ^ 2 = |x.2| * |x.2| := by rw [← sq_abs]; ring
    have h1 : |x.2| / c ≤ |x.2| * c := by
      rw [div_le_iff₀ hc0]
      nlinarith [mul_nonneg (abs_nonneg x.2) (mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ c + 1))]
    rw [ha, hsq]
    have : 2 * (1 / 32) * |x.2| / c = |x.2| / c / 16 := by ring
    rw [this]
    nlinarith [abs_nonneg x.2, mul_le_mul_of_nonneg_left hx (abs_nonneg x.2)]
  have hexpH : Real.exp (-(2 * Real.pi * (|x.2| / c))) ≤ Real.exp (-(2 * a * |x.2| / c)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    have hpi := Real.pi_gt_three
    have hq : 0 ≤ |x.2| / c := by positivity
    rw [show 2 * a * |x.2| / c = 2 * a * (|x.2| / c) by ring]
    rw [ha]
    nlinarith
  have hnorm : ‖(-(M / 4)) * harmPeriodic c x‖ + ‖(-(M / 4)) • fderiv ℝ (harmPeriodic c) x‖ =
      ‖M / 4‖ * (‖harmPeriodic c x‖ + ‖fderiv ℝ (harmPeriodic c) x‖) := by
    rw [norm_mul, norm_smul, norm_neg]; ring
  have hsum : ‖(-(M / 4)) * harmPeriodic c x + gaussPeriodic (greenRem q M) c x‖ +
      ‖(-(M / 4)) • fderiv ℝ (harmPeriodic c) x +
        fderiv ℝ (gaussPeriodic (greenRem q M) c) x‖ ≤
      B * Real.exp (-(2 * a * |x.2| / c)) := by
    calc _ ≤ (‖(-(M / 4)) * harmPeriodic c x‖ + ‖(-(M / 4)) • fderiv ℝ (harmPeriodic c) x‖) +
          (‖gaussPeriodic (greenRem q M) c x‖ + ‖fderiv ℝ (gaussPeriodic (greenRem q M) c) x‖) := by
          have := norm_add_le ((-(M / 4)) * harmPeriodic c x) (gaussPeriodic (greenRem q M) c x)
          have := norm_add_le ((-(M / 4)) • fderiv ℝ (harmPeriodic c) x)
            (fderiv ℝ (gaussPeriodic (greenRem q M) c) x)
          linarith
      _ ≤ ‖M / 4‖ * (|Ch| * Real.exp (-(2 * a * |x.2| / c))) +
          |Cp| * Real.exp (-(2 * a * |x.2| / c)) := by
          rw [hnorm]
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact bH.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
              (mul_le_mul_of_nonneg_left hexpH (abs_nonneg _)))
          · exact bP.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
              (mul_le_mul_of_nonneg_left hexpP (abs_nonneg _)))
      _ = B * Real.exp (-(2 * a * |x.2| / c)) := by rw [hB]; ring
  calc (1 + |x.2|) ^ m * _ ≤ (1 + |x.2|) ^ m * (B * Real.exp (-(2 * a * |x.2| / c))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B * ((1 + |x.2|) ^ m * Real.exp (-(2 * a * |x.2| / c))) := by ring
    _ ≤ B * ((2 ^ m * (m.factorial / a ^ m)) * c ^ m * Real.exp (-(a * |x.2| / c))) :=
        mul_le_mul_of_nonneg_left (weight_absorb m ha0 hc hx) hB0
    _ = 2 ^ m * (m.factorial / a ^ m) * B * c ^ m * Real.exp (-(a * |x.2| / c)) := by ring

end UnforcedLeray.Short.IIIa
