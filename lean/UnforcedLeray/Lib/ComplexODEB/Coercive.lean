import UnforcedLeray.Analysis.Rayleigh.Evans.Nontrivial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# B0034 helper: no Evans zero at large spectral speed, for every real angular index

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Blueprint unit B0034 (`paper/main.tex`, lines 1012–1021) needs a mode at angular
index two; the continuation argument behind it (Lin's argument, cited at tex lines
1012–1014) moves the real wavenumber `β` through `(1, α_{max,N})`. Isolation of
Evans zeros and compactness of the zero set both need that the Evans function
`D(β,·) = evansFunction β a b` has no zero of large modulus, uniformly in `β`
bounded away from zero.

This is proved from the Dirichlet energy: for a solution of `F'' = V F` with
`F(a) = F(b) = 0`, integration by parts gives `∫ conj F · V F = -∫ |F'|²`, so
`Re V > 0` on `[a,b]` forces `F = 0` there. For the actual Gaussian coefficient
`V = β² + A/(Ω-c)`, `|A/(Ω-c)| ≤ max|A| / (‖c‖-1)` because `0 < Ω < 1`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans

/-- Dirichlet coercivity: a classical solution of `F'' = V F` on `[a,b]` with
`F(a) = F(b) = 0` and `Re V > 0` on `[a,b]` vanishes on `[a,b]`. -/
theorem eq_zero_of_dirichlet_of_re_pos {F G V : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hV : Continuous V) (hF : ∀ t, HasDerivAt F (G t) t)
    (hG : ∀ t, HasDerivAt G (V t * F t) t) (ha : F a = 0) (hb : F b = 0)
    (hpos : ∀ t ∈ Icc a b, 0 < (V t).re) : ∀ t ∈ Icc a b, F t = 0 := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun t => (hG t).continuousAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun t => star (F t)) (u' := fun t => star (G t)) (v := G)
    (v' := fun t => V t * F t)
    (fun t _ => (hF t).star) (fun t _ => hG t)
    ((continuous_star.comp hGc).intervalIntegrable _ _)
    ((hV.mul hFc).intervalIntegrable _ _)
  simp only [ha, hb, star_zero, zero_mul, sub_zero, zero_sub] at hibp
  set w : ℝ → ℂ := fun t => star (F t) * (V t * F t) + star (G t) * G t with hw_def
  have hwc : Continuous w :=
    ((continuous_star.comp hFc).mul (hV.mul hFc)).add ((continuous_star.comp hGc).mul hGc)
  have hw0 : ∫ t in a..b, w t = 0 := by
    show ∫ t in a..b, (star (F t) * (V t * F t) + star (G t) * G t) = 0
    have i1 : Continuous (fun t => star (F t) * (V t * F t)) :=
      (continuous_star.comp hFc).mul (hV.mul hFc)
    have i2 : Continuous (fun t => star (G t) * G t) :=
      (continuous_star.comp hGc).mul hGc
    rw [intervalIntegral.integral_add (i1.intervalIntegrable a b) (i2.intervalIntegrable a b), hibp]
    ring
  set g : ℝ → ℝ := fun t => (V t).re * ‖F t‖ ^ 2 + ‖G t‖ ^ 2 with hg_def
  have hgc : Continuous g :=
    ((Complex.continuous_re.comp hV).mul (hFc.norm.pow 2)).add (hGc.norm.pow 2)
  have hpt : ∀ t, (w t).re = g t := by
    intro t
    have h1 : star (F t) * F t = ((‖F t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    have h2 : star (G t) * G t = ((‖G t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    have h3 : star (F t) * (V t * F t) = V t * ((‖F t‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h1]; ring
    simp only [hw_def, hg_def, h3, h2, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hg0 : ∫ t in a..b, g t = 0 := by
    have := intervalIntegral.intervalIntegral_re (μ := volume) (hwc.intervalIntegrable a b)
    simp only [RCLike.re_to_complex, hpt] at this
    rw [this, hw0, Complex.zero_re]
  intro t₀ ht₀
  by_contra hne
  have hta : t₀ ≠ a := by rintro rfl; exact hne ha
  have htb : t₀ ≠ b := by rintro rfl; exact hne hb
  have ht₀' : t₀ ∈ Ioo a b := ⟨lt_of_le_of_ne ht₀.1 (Ne.symm hta), lt_of_le_of_ne ht₀.2 htb⟩
  have hab' : a < b := ht₀'.1.trans ht₀'.2
  have hgnn : ∀ t ∈ Icc a b, 0 ≤ g t := fun t ht =>
    add_nonneg (mul_nonneg (hpos t ht).le (by positivity)) (by positivity)
  have hgpos : 0 < g t₀ := by
    have : 0 < ‖F t₀‖ ^ 2 := by positivity
    exact add_pos_of_pos_of_nonneg (mul_pos (hpos t₀ ht₀) this) (by positivity)
  have hae : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)] g := by
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hab'.le] at ht
    exact hgnn t (Ioc_subset_Icc_self ht)
  have hint : 0 < ∫ t in a..b, g t := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hae (hgc.intervalIntegrable a b)]
    refine ⟨hab', ?_⟩
    have hopen : IsOpen ({t | 0 < g t} ∩ Ioo a b) :=
      (isOpen_lt continuous_const hgc).inter isOpen_Ioo
    have hpos' := hopen.measure_pos volume ⟨t₀, hgpos, ht₀'⟩
    refine lt_of_lt_of_le hpos' (measure_mono ?_)
    rintro t ⟨ht1, ht2⟩
    exact ⟨ne_of_gt ht1, Ioo_subset_Ioc_self ht2⟩
  linarith

/-- `‖Ω(t) - c‖ ≥ ‖c‖ - 1`, since the Gaussian angular speed lies in `(0,1)`. -/
theorem sub_one_le_norm_neutralOmega_sub (t : ℝ) (c : ℂ) :
    ‖c‖ - 1 ≤ ‖(Sturm.neutralOmega t : ℂ) - c‖ := by
  have h1 : ‖(Sturm.neutralOmega t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (neutralOmega_pos t)]
    exact (neutralOmega_lt_one t).le
  have h2 := norm_sub_norm_le c (Sturm.neutralOmega t : ℂ)
  rw [norm_sub_rev] at h2
  linarith

/-- The actual coefficient `A = -W(Ω-a_*)` is bounded on every compact log-interval. -/
theorem exists_bound_rayleighCoefficient (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, |gaussianRayleighCoefficient t| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (gaussianRayleighCoefficient_smooth.continuous.continuousOn (s := Icc a b))
  exact ⟨max M 0, le_max_right _ _, fun t ht =>
    (by simpa only [Real.norm_eq_abs] using hM t ht : |gaussianRayleighCoefficient t| ≤ M).trans
      (le_max_left _ _)⟩

/-- The real part of `V = β² + A/(Ω-c)` is positive once `‖c‖ > 1 + M/β²`. -/
theorem re_rayleighPotential_pos {β M t : ℝ} {c : ℂ} (hβ : β ≠ 0)
    (hA : |gaussianRayleighCoefficient t| ≤ M) (hM : 0 ≤ M) (hc : 1 + M / β ^ 2 < ‖c‖) :
    0 < (rayleighPotential β t c).re := by
  have hβ2 : 0 < β ^ 2 := by positivity
  have hd : 0 < ‖c‖ - 1 := by have := div_nonneg hM hβ2.le; linarith
  have hden := sub_one_le_norm_neutralOmega_sub t c
  set q : ℂ := (gaussianRayleighCoefficient t : ℂ) / ((Sturm.neutralOmega t : ℂ) - c) with hq_def
  have hq : ‖q‖ ≤ M / (‖c‖ - 1) := by
    rw [hq_def, norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div₀ hM hA hd hden
  have hMlt : M / (‖c‖ - 1) < β ^ 2 := by
    rw [div_lt_iff₀ hd]
    have h' : M / β ^ 2 < ‖c‖ - 1 := by linarith
    rw [div_lt_iff₀ hβ2] at h'
    linarith
  have hre : -‖q‖ ≤ q.re := by
    have := Complex.abs_re_le_norm q
    linarith [neg_abs_le q.re]
  have hV : (rayleighPotential β t c).re = β ^ 2 + q.re := by
    simp only [rayleighPotential, Complex.add_re, hq_def]
    norm_cast
  rw [hV]
  linarith

/-- No Evans zero of large modulus, uniformly for `|β| ≥ β₀ > 0`. -/
theorem evansFunction_ne_zero_of_norm_gt {a b : ℝ} (hab : a < b) {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    ∃ R : ℝ, ∀ β : ℝ, β₀ ≤ |β| → ∀ c : ℂ, 0 < c.im → R < ‖c‖ →
      evansFunction β a b c ≠ 0 := by
  obtain ⟨M, hM, hA⟩ := exists_bound_rayleighCoefficient a b
  refine ⟨1 + M / β₀ ^ 2, fun β hβ c hc hcR he => ?_⟩
  have hβne : β ≠ 0 := by
    rintro rfl
    simp only [abs_zero] at hβ
    linarith
  have hβsq : β₀ ^ 2 ≤ β ^ 2 := by
    rw [← sq_abs β]
    exact pow_le_pow_left₀ hβ₀.le hβ 2
  have hcR' : 1 + M / β ^ 2 < ‖c‖ := lt_of_le_of_lt
    (by have := div_le_div_of_nonneg_left hM (by positivity) hβsq; linarith) hcR
  have hz := eq_zero_of_dirichlet_of_re_pos hab.le (continuous_rayleighPotential β hc)
    (hasDerivAt_normalizedF β a hc) (hasDerivAt_normalizedDerivative β a hc)
    (normalizedF_initial β a hc) he
    (fun t ht => re_rayleighPotential_pos hβne (hA t ht) hM hcR')
  obtain ⟨t, ht, hne⟩ := normalizedF_nonzero_on_interval β hab hc
  exact hne (hz t ht)

/-- For `β ≠ 0`, the Evans function `D(β,·)` is not identically zero on the upper
half-plane. -/
theorem exists_evansFunction_ne_zero {a b : ℝ} (hab : a < b) {β : ℝ} (hβ : β ≠ 0) :
    ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c ≠ 0 := by
  obtain ⟨R, hR⟩ := evansFunction_ne_zero_of_norm_gt hab (abs_pos.mpr hβ)
  set y : ℝ := max R 0 + 1
  have hy : 0 < y := by positivity
  refine ⟨(y : ℂ) * Complex.I, by simpa using hy, hR β le_rfl _ (by simpa using hy) ?_⟩
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have := le_max_left R 0
  linarith

end UnforcedLeray.ComplexODEB
