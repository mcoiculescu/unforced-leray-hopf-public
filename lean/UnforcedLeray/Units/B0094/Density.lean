import UnforcedLeray.Units.B0094.Profiles
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# B0094 helper: completeness of the Gaussian-polynomial profiles in `X_G`

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1515). The unit's notes
name "completeness of that basis (equivalently of Hermite functions)" as the missing analytic
input. This file proves it: if `h ∈ X_G` is orthogonal to every `r^{2+2k} e^{-r²/4}`, then
`h = 0` (`eq_zero_of_inner_prof_X_pow`).

Proof. Orthogonality says `∫₀^∞ r^{3+2k} h(r) dr = 0` for all `k`. Expanding
`e^{-r²/16} = ∑ (-r²/16)ʲ/j!` and exchanging sum and integral (the weight `e^{r²/4}` of `X_G`
dominates `e^{r²/16}`), induction gives `∫₀^∞ r^{3+2k} e^{-n r²/16} h(r) dr = 0` for all `n, k`.
Hence `∫₀^∞ r³ P(e^{-r²/16}) h(r) dr = 0` for every real polynomial `P`; by Weierstrass on
`[0, 1]`, `∫₀^∞ r³ χ(r) h(r) dr = 0` for every continuous `χ` with compact support in
`(0, ∞)`, and the fundamental lemma of the calculus of variations gives `h = 0` a.e.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Polynomial Filter Topology
open scoped ComplexConjugate Real InnerProductSpace Nat ContDiff

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010

/-- The elementary inequality behind the weighted Cauchy–Schwarz estimate. -/
theorem moment_bound {x c r : ℝ} (k : ℕ) (hr : 0 < r) :
    x * (r ^ (3 + 2 * k) * Real.exp (c * r ^ 2)) ≤
      x ^ 2 * (4 * π * Real.exp (r ^ 2 / 4) * r) / (8 * π) +
        r ^ (4 * k + 5) * Real.exp (-(1 / 4 - 2 * c) * r ^ 2) / 2 := by
  set a := x * Real.exp (r ^ 2 / 8) with ha
  set bb := r ^ (3 + 2 * k) * Real.exp ((c - 1 / 8) * r ^ 2) with hbb
  set Y := r ^ (4 * k + 5) * Real.exp (-(1 / 4 - 2 * c) * r ^ 2) with hY
  have h1 : x * (r ^ (3 + 2 * k) * Real.exp (c * r ^ 2)) = a * bb := by
    rw [ha, hbb, show c * r ^ 2 = r ^ 2 / 8 + (c - 1 / 8) * r ^ 2 by ring, Real.exp_add]
    ring
  have h2 : x ^ 2 * (4 * π * Real.exp (r ^ 2 / 4) * r) / (8 * π) = a ^ 2 * r / 2 := by
    rw [ha, show r ^ 2 / 4 = r ^ 2 / 8 + r ^ 2 / 8 by ring, Real.exp_add]
    field_simp
    ring
  have h3 : Y * r = bb ^ 2 := by
    rw [hY, hbb, mul_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  rw [h1, h2]
  have key : (a * bb) * r ≤ (a ^ 2 * r / 2 + Y / 2) * r := by
    nlinarith [sq_nonneg (a * r - bb)]
  exact le_of_mul_le_mul_right key hr

/-- Integrals against `xGMeasure` as weighted integrals on `(0, ∞)`. -/
theorem integral_xGMeasure (F : ℝ → ℂ) :
    ∫ r, F r ∂xGMeasure = ∫ r in Ioi 0, ((xGDensity r : ℝ) : ℂ) * F r := by
  rw [xGMeasure, integral_withDensity_eq_integral_smul measurable_xGDensity]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]

variable (h : XG)

theorem integrableOn_sq_weight :
    IntegrableOn (fun r => ‖h r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
  (memLp_iff_integrableOn (Lp.stronglyMeasurable h).aestronglyMeasurable).1 (Lp.memLp h)

/-- Weighted moments of `h ∈ X_G` against `r^{3+2k} e^{c r²}`, `c < 1/8`, are integrable. -/
theorem integrableOn_weighted {c : ℝ} (hc : c < 1 / 8) (k : ℕ) :
    IntegrableOn (fun r => ((r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) : ℝ) : ℂ) * h r) (Ioi 0) := by
  have hb : 0 < 1 / 4 - 2 * c := by linarith
  have hg : IntegrableOn (fun r => ‖h r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) / (8 * π) +
      r ^ (4 * k + 5) * Real.exp (-(1 / 4 - 2 * c) * r ^ 2) / 2) (Ioi 0) :=
    ((integrableOn_sq_weight h).div_const _).add
      ((integrableOn_pow_mul_exp (4 * k + 5) hb).div_const 2)
  refine Integrable.mono' hg ?_ ?_
  · exact ((by fun_prop : Continuous fun r : ℝ =>
      ((r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) : ℝ) : ℂ)).aestronglyMeasurable).mul
      (Lp.stronglyMeasurable h).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), weight_eq, mul_comm]
    exact moment_bound k hr'

theorem integrableOn_norm_weighted {c : ℝ} (hc : c < 1 / 8) (k : ℕ) :
    IntegrableOn (fun r => r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) * ‖h r‖) (Ioi 0) := by
  refine IntegrableOn.congr_fun (integrableOn_weighted h hc k).norm (fun r hr => ?_)
    measurableSet_Ioi
  have hr' : (0 : ℝ) < r := hr
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity :
    (0 : ℝ) ≤ r ^ (3 + 2 * k) * Real.exp (c * r ^ 2))]

/-- The inner product with a monomial profile is a moment of `h`. -/
theorem inner_prof_X_pow_eq (k : ℕ) :
    ⟪prof (X ^ k), h⟫_ℂ = ∫ r in Ioi 0, ((4 * π * r ^ (3 + 2 * k) : ℝ) : ℂ) * h r := by
  rw [← pairing_eq_inner, pairing]
  have h1 : ∫ r, h r * conj ((prof (X ^ k) : ℝ → ℂ) r) ∂xGMeasure =
      ∫ r, h r * conj (profFun (X ^ k) r) ∂xGMeasure := by
    apply integral_congr_ae
    filter_upwards [coeFn_prof (X ^ k)] with r hr
    rw [hr]
  rw [h1, integral_xGMeasure]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr' : (0 : ℝ) < r := hr
  simp only [coe_xGDensity hr', profFun_X_pow, Complex.conj_ofReal, weight_eq, monoReal]
  push_cast
  have := exp_quarter_mul r
  have e : Complex.exp (-((r : ℂ) ^ 2 / 4)) * Complex.exp ((r : ℂ) ^ 2 / 4) = 1 := by
    rw [← Complex.exp_add]
    simp
  linear_combination (h r * 4 * π * (r : ℂ) ^ (3 + 2 * k)) * e

/-- Step 1: vanishing moments. -/
theorem moments_zero (horth : ∀ k, ⟪prof (X ^ k), h⟫_ℂ = 0) (k : ℕ) :
    ∫ r in Ioi 0, ((r ^ (3 + 2 * k) * Real.exp ((0 : ℝ) * r ^ 2) : ℝ) : ℂ) * h r = 0 := by
  have h1 := horth k
  rw [inner_prof_X_pow_eq] at h1
  have h2 : ∫ r in Ioi 0, ((4 * π * r ^ (3 + 2 * k) : ℝ) : ℂ) * h r =
      (4 * π : ℂ) * ∫ r in Ioi 0, ((r ^ (3 + 2 * k) * Real.exp ((0 : ℝ) * r ^ 2) : ℝ) : ℂ) * h r := by
    rw [← integral_const_mul]
    congr 1
    funext r
    simp only [zero_mul, Real.exp_zero, mul_one]
    push_cast
    ring
  rw [h2] at h1
  have hπ : (4 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) this
  exact (mul_eq_zero.1 h1).resolve_left hπ

/-- The real exponential series. -/
theorem hasSum_exp_real (x : ℝ) : HasSum (fun j : ℕ => x ^ j / j !) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- Step 2: vanishing Gaussian-weighted moments, by induction on `n`. -/
theorem gaussian_moments_zero (horth : ∀ k, ⟪prof (X ^ k), h⟫_ℂ = 0) (n : ℕ) :
    ∀ k : ℕ, ∫ r in Ioi 0,
      ((r ^ (3 + 2 * k) * Real.exp (-(n : ℝ) / 16 * r ^ 2) : ℝ) : ℂ) * h r = 0 := by
  induction n with
  | zero =>
    intro k
    simpa using moments_zero h horth k
  | succ n ih =>
    intro k
    set c : ℝ := -(n : ℝ) / 16 with hc
    have hc8 : c < 1 / 8 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hc]; linarith
    have hc8' : c + 1 / 16 < 1 / 8 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hc]; linarith
    set a : ℕ → ℝ := fun j => (-(1 / 16 : ℝ)) ^ j / j ! with ha
    set F : ℕ → ℝ → ℂ := fun j r =>
      (a j : ℂ) * (((r ^ (3 + 2 * (k + j)) * Real.exp (c * r ^ 2) : ℝ) : ℂ) * h r) with hF
    have hFint : ∀ j, Integrable (F j) (volume.restrict (Ioi 0)) :=
      fun j => (integrableOn_weighted h hc8 (k + j)).const_mul _
    have hFzero : ∀ j, ∫ r in Ioi 0, F j r = 0 := by
      intro j
      simp only [hF]
      rw [integral_const_mul, ih (k + j), mul_zero]
    have hnormF : ∀ j, ∀ r ∈ Ioi (0 : ℝ), ‖F j r‖ =
        r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) * ‖h r‖ * ((r ^ 2 / 16) ^ j / j !) := by
      intro j r hr
      have hr' : (0 : ℝ) < r := hr
      simp only [hF, ha, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity :
        (0 : ℝ) ≤ r ^ (3 + 2 * (k + j)) * Real.exp (c * r ^ 2)), norm_div, norm_pow, norm_neg,
        Real.norm_natCast]
      rw [norm_one, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
      ring
    have hsum : Summable fun j => ∫ r in Ioi 0, ‖F j r‖ := by
      refine summable_of_sum_range_le (c := ∫ r in Ioi 0,
          r ^ (3 + 2 * k) * Real.exp ((c + 1 / 16) * r ^ 2) * ‖h r‖)
        (fun j => integral_nonneg fun r => norm_nonneg _) (fun N => ?_)
      rw [← integral_finsetSum _ (fun j _ => (hFint j).norm)]
      refine setIntegral_mono_on (integrable_finsetSum _ fun j _ => (hFint j).norm)
        ?_ measurableSet_Ioi (fun r hr => ?_)
      · exact integrableOn_norm_weighted h hc8' k
      · have hr' : (0 : ℝ) < r := hr
        rw [Finset.sum_congr rfl fun j _ => hnormF j r hr, ← Finset.mul_sum]
        calc r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) * ‖h r‖ *
              ∑ j ∈ Finset.range N, (r ^ 2 / 16) ^ j / j !
            ≤ r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) * ‖h r‖ * Real.exp (r ^ 2 / 16) :=
              mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) N)
                (by positivity)
          _ = r ^ (3 + 2 * k) * Real.exp ((c + 1 / 16) * r ^ 2) * ‖h r‖ := by
              rw [show (c + 1 / 16) * r ^ 2 = c * r ^ 2 + r ^ 2 / 16 by ring, Real.exp_add]
              ring
    have hpt : ∀ r, ∑' j, F j r =
        ((r ^ (3 + 2 * k) * Real.exp (-((n + 1 : ℕ) : ℝ) / 16 * r ^ 2) : ℝ) : ℂ) * h r := by
      intro r
      have hs := hasSum_exp_real (-(r ^ 2 / 16))
      have hs' := ((Complex.hasSum_ofReal).2 hs).mul_left
        (((r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) : ℝ) : ℂ) * h r)
      have e1 : ∀ j, ((r ^ (3 + 2 * k) * Real.exp (c * r ^ 2) : ℝ) : ℂ) * h r *
          (((-(r ^ 2 / 16)) ^ j / j ! : ℝ) : ℂ) = F j r := by
        intro j
        simp only [hF, ha]
        push_cast
        ring
      simp only [e1] at hs'
      rw [hs'.tsum_eq, mul_right_comm, ← Complex.ofReal_mul]
      congr 2
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      rw [hc]
      push_cast
      ring
    have hint := integral_tsum_of_summable_integral_norm hFint hsum
    simp only [hFzero, tsum_zero] at hint
    rw [← funext hpt]
    exact hint.symm

/-- Step 3: vanishing moments against polynomials in `e^{-r²/16}`. -/
theorem poly_moments_zero (horth : ∀ k, ⟪prof (X ^ k), h⟫_ℂ = 0) (P : ℝ[X]) :
    ∫ r in Ioi 0, ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ) * h r = 0 := by
  have hpt : ∀ r : ℝ, ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ) * h r =
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℂ) *
        (((r ^ (3 + 2 * 0) * Real.exp (-(i : ℝ) / 16 * r ^ 2) : ℝ) : ℂ) * h r) := by
    intro r
    rw [eval_eq_sum_range, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, show (i : ℝ) * (-(1 / 16) * r ^ 2) = -(i : ℝ) / 16 * r ^ 2 by ring]
    push_cast
    ring
  rw [show (fun r : ℝ => ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ) * h r) =
    fun r => ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℂ) *
        (((r ^ (3 + 2 * 0) * Real.exp (-(i : ℝ) / 16 * r ^ 2) : ℝ) : ℂ) * h r) from funext hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, gaussian_moments_zero h horth i 0, mul_zero]
  · intro i _
    have : -(i : ℝ) / 16 < 1 / 8 := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    exact (integrableOn_weighted h this 0).const_mul _

/-- Step 4: vanishing moments against continuous functions with compact support in `(0, ∞)`
(Weierstrass approximation in the variable `u = e^{-r²/16} ∈ (0, 1]`). -/
theorem test_moments_zero (horth : ∀ k, ⟪prof (X ^ k), h⟫_ℂ = 0) (χ : ℝ → ℝ)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχU : tsupport χ ⊆ Ioi 0) :
    ∫ r in Ioi 0, ((r ^ 3 * χ r : ℝ) : ℂ) * h r = 0 := by
  -- `χ` vanishes at `0` and beyond some `R > 0`
  have hχ0 : χ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h0 => (lt_irrefl (0 : ℝ)) (Set.mem_Ioi.1 (hχU h0))
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hχs.isCompact.isBounded
  set R := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hχR : ∀ r, R < r → χ r = 0 := by
    intro r hr
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR₀ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have : r ≤ R₀ := (le_abs_self r).trans this
    linarith [le_max_left R₀ 1]
  -- the function `ψ(u) = χ(√(-16 log u))`
  set ψ : ℝ → ℝ := fun u => χ (Real.sqrt (-16 * Real.log u)) with hψ
  set δ := Real.exp (-(R ^ 2 / 16)) with hδ
  have hδpos : 0 < δ := Real.exp_pos _
  have hψ0 : ∀ u, |u| < δ → ψ u = 0 := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hψ, hu0, hχ0]
    · apply hχR
      have hlog : Real.log u < -(R ^ 2 / 16) := by
        rw [← Real.log_abs]
        calc Real.log |u| < Real.log δ := Real.log_lt_log (abs_pos.2 hu0) hu
          _ = -(R ^ 2 / 16) := Real.log_exp _
      rw [Real.lt_sqrt hRpos.le]
      linarith
  have hψcont : ContinuousOn ψ (Icc 0 1) := by
    intro u _
    apply ContinuousAt.continuousWithinAt
    by_cases hu : u = 0
    · subst hu
      have : ψ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδpos
        filter_upwards [hball] with v hv
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
        exact hψ0 v hv
      rw [continuousAt_congr this]
      exact continuousAt_const
    · exact hχc.continuousAt.comp (Real.continuous_sqrt.continuousAt.comp
        ((continuousAt_const.mul (Real.continuousAt_log hu))))
  have hψr : ∀ r : ℝ, 0 < r → ψ (Real.exp (-(1 / 16) * r ^ 2)) = χ r := by
    intro r hr
    simp only [hψ, Real.log_exp]
    rw [show -16 * (-(1 / 16) * r ^ 2) = r ^ 2 by ring, Real.sqrt_sq hr.le]
  have hu01 : ∀ r : ℝ, Real.exp (-(1 / 16) * r ^ 2) ∈ Icc (0 : ℝ) 1 := by
    intro r
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg r]
  -- the bound
  set I := ∫ r in Ioi 0, ((r ^ 3 * χ r : ℝ) : ℂ) * h r with hI
  set K := ∫ r in Ioi 0, r ^ (3 + 2 * 0) * Real.exp ((0 : ℝ) * r ^ 2) * ‖h r‖ with hK
  have hKint := integrableOn_norm_weighted h (c := 0) (by norm_num) 0
  obtain ⟨C, hC⟩ := hχc.bounded_above_of_compact_support hχs
  have hIint : IntegrableOn (fun r => ((r ^ 3 * χ r : ℝ) : ℂ) * h r) (Ioi 0) := by
    refine Integrable.mono' (hKint.const_mul C) ?_ ?_
    · exact ((by fun_prop : Continuous fun r : ℝ => ((r ^ 3 * χ r : ℝ) : ℂ)).aestronglyMeasurable).mul
        (Lp.stronglyMeasurable h).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr' : (0 : ℝ) < r := hr
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos hr', zero_mul, Real.exp_zero, mul_one, mul_zero, add_zero]
      have := hC r
      rw [Real.norm_eq_abs] at this
      have h3 : 0 ≤ r ^ 3 := by positivity
      have h4 : 0 ≤ ‖h r‖ := norm_nonneg _
      calc r ^ 3 * |χ r| * ‖h r‖ ≤ r ^ 3 * C * ‖h r‖ := by gcongr
        _ = C * (r ^ 3 * ‖h r‖) := by ring
  have hbound : ∀ ε > 0, ‖I‖ ≤ ε * K := by
    intro ε hε
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 ψ hψcont ε hε
    have hPint : IntegrableOn
        (fun r => ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ) * h r) (Ioi 0) := by
      refine Integrable.mono' (hKint.const_mul (C + ε)) ?_ ?_
      · exact ((by fun_prop : Continuous fun r : ℝ =>
          ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ)).aestronglyMeasurable).mul
          (Lp.stronglyMeasurable h).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
        have hr' : (0 : ℝ) < r := hr
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_pos hr', zero_mul, Real.exp_zero, mul_one, mul_zero, add_zero]
        have hPb : |P.eval (Real.exp (-(1 / 16) * r ^ 2))| ≤ C + ε := by
          have h1 := hP _ (hu01 r)
          have h2 := hC r
          rw [Real.norm_eq_abs, ← hψr r hr'] at h2
          have := abs_sub_abs_le_abs_sub (P.eval (Real.exp (-(1 / 16) * r ^ 2)))
            (ψ (Real.exp (-(1 / 16) * r ^ 2)))
          linarith
        have h3 : 0 ≤ r ^ 3 := by positivity
        have h4 : 0 ≤ ‖h r‖ := norm_nonneg _
        calc r ^ 3 * |P.eval (Real.exp (-(1 / 16) * r ^ 2))| * ‖h r‖
            ≤ r ^ 3 * (C + ε) * ‖h r‖ := by gcongr
          _ = (C + ε) * (r ^ 3 * ‖h r‖) := by ring
    have hzero := poly_moments_zero h horth P
    have hdiff : I = ∫ r in Ioi 0, (((r ^ 3 * χ r : ℝ) : ℂ) * h r -
        ((r ^ 3 * P.eval (Real.exp (-(1 / 16) * r ^ 2)) : ℝ) : ℂ) * h r) := by
      rw [integral_sub hIint hPint, hzero, sub_zero]
    rw [hdiff, hK, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hKint.const_mul ε) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      ← mul_sub, abs_mul, abs_of_pos (pow_pos hr' 3)]
    have h1 := hP _ (hu01 r)
    rw [hψr r hr', abs_sub_comm] at h1
    simp only [zero_mul, Real.exp_zero, mul_one, mul_zero, add_zero]
    have h3 : 0 ≤ r ^ 3 := by positivity
    have h4 : 0 ≤ ‖h r‖ := norm_nonneg _
    calc r ^ 3 * |χ r - P.eval (Real.exp (-(1 / 16) * r ^ 2))| * ‖h r‖
        ≤ r ^ 3 * ε * ‖h r‖ := by gcongr
      _ = ε * (r ^ 3 * ‖h r‖) := by ring
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  by_contra hne
  have hpos : 0 < ‖I‖ := norm_pos_iff.2 hne
  have := hbound (‖I‖ / (2 * (K + 1))) (by positivity)
  have h2 : ‖I‖ / (2 * (K + 1)) * K < ‖I‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Completeness**: a vector of `X_G` orthogonal to all profiles `r^{2+2k} e^{-r²/4}`
vanishes. -/
theorem eq_zero_of_inner_prof_X_pow (horth : ∀ k, ⟪prof (X ^ k), h⟫_ℂ = 0) : h = 0 := by
  set f : ℝ → ℂ := fun r => ((r ^ 3 : ℝ) : ℂ) * h r with hf
  have hfint : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_weighted h (c := 0) (by norm_num) 0).congr_fun (fun r _ => ?_)
      measurableSet_Ioi
    simp [hf]
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioi
    hfint.locallyIntegrableOn (fun g hg hgs hgU => by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hgU hx')), zero_smul])]
      have := test_moments_zero h horth g hg.continuous hgs hgU
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
      simp only [hf, Complex.real_smul]
      push_cast
      ring)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have h2 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), h r = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have := hr hr0
    simp only [hf, mul_eq_zero, Complex.ofReal_eq_zero, pow_eq_zero_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true] at this
    rcases this with h0 | h0
    · exact absurd h0 (ne_of_gt hr0)
    · exact h0
  have h3 : ∀ᵐ r ∂xGMeasure, h r = 0 := (withDensity_absolutelyContinuous _ _).ae_le h2
  filter_upwards [h3] with r hr
  rw [hr]
  rfl

end UnforcedLeray.B0094
