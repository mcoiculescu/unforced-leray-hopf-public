import UnforcedLeray.Analysis.Rayleigh.ClassicalMode
import UnforcedLeray.Analysis.Rayleigh.Evans.Coefficients
import UnforcedLeray.Analysis.Rayleigh.DecayH1

/-!
# Smoothness, decay and normalization of classical whole-line Gaussian modes

Wave 2 block 2H PLAN1b (INF18 O8). `paper/main.tex` lines 1124--1146 (§`sec:st18-1294`:
for nonreal `c` the limiting equation is `F'' - 4F = BF`, `B = A/(Ω - c)`, eq.
`st18-t00043`), restricted to what the whole-line mode of O8 records: global smoothness in
logarithmic radius, decay of `F` and `F'` at both ends, and the unit-mass normalization.

*Provenance.* Copy, with namespace `UnforcedLeray.ComplexODEB` and explicit mode hypotheses
in place of the dot-notation namespace `UnforcedLeray.Rayleigh.GaussianWholeLineMode`, of the

WholeLineNormalization}.lean`; the drafts are unchanged.

The mode is the compiled `Rayleigh.GaussianWholeLineMode c F`: `Im c > 0`, `F ∈ C²`,
`F, F', F'' ∈ L²`, `F ≢ 0` and `(Ω - c)(F'' - 4F) - AF = 0` at every `t`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh Sturm

/-! ### Smoothness (tex eq. `st18-t00043`) -/

section Smooth
variable {c : ℂ} {F : ℝ → ℂ}

/-- Tex eq. `st18-t00043`: for `Im c > 0` the undivided equation divides to
`F'' = (4 + A/(Ω - c)) F`, which is the compiled `rayleighPotential 2`. -/
theorem wholeLineMode_second_deriv_eq_potential (h : GaussianWholeLineMode c F) :
    deriv (deriv F) = fun t => Evans.rayleighPotential 2 t c * F t := by
  funext t
  have hd := gaussianSpeed_denominator_ne_zero h.upper_half_plane t
  have he := h.equation t
  unfold Evans.rayleighPotential
  norm_num only [Complex.ofReal_ofNat, show (2 : ℂ) ^ 2 = 4 by norm_num]
  apply mul_left_cancel₀ hd
  calc
    ((neutralOmega t : ℂ) - c) * deriv (deriv F) t =
        4 * ((neutralOmega t : ℂ) - c) * F t +
          (gaussianRayleighCoefficient t : ℂ) * F t := by linear_combination he
    _ = _ := by field_simp

/-- Simultaneous bootstrap of `F` and `F'` to every finite order. -/
theorem wholeLineMode_contDiff_pair_nat (h : GaussianWholeLineMode c F) (n : ℕ) :
    ContDiff ℝ n F ∧ ContDiff ℝ n (deriv F) := by
  have h1 : ContDiff ℝ 1 F := h.regularity.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv F) := contDiff_deriv_of_two h.regularity
  induction n with
  | zero => exact ⟨contDiff_zero.mpr h1.continuous, contDiff_zero.mpr hd.continuous⟩
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one]
      constructor
      · apply contDiff_succ_iff_deriv.mpr
        refine ⟨h1.differentiable one_ne_zero, ?_, ih.2⟩
        intro hn
        simp at hn
      · apply contDiff_succ_iff_deriv.mpr
        refine ⟨hd.differentiable one_ne_zero, ?_, ?_⟩
        · intro hn
          simp at hn
        · rw [wholeLineMode_second_deriv_eq_potential h]
          exact (contDiff_infty.mp
            (Evans.rayleighPotential_smooth 2 h.upper_half_plane) n).mul ih.1

/-- Every classical unstable Gaussian whole-line mode is smooth in logarithmic radius
(tex lines 1124--1146). -/
theorem wholeLineMode_smooth (h : GaussianWholeLineMode c F) : ContDiff ℝ ∞ F :=
  contDiff_infty.mpr fun n => (wholeLineMode_contDiff_pair_nat h n).1

end Smooth

/-! ### Decay at both ends -/

section Decay
variable {c : ℂ} {F : ℝ → ℂ}

/-- The mode tends to zero at both ends (from `F, F' ∈ L²`, compiled `DecayH1`). -/
theorem wholeLineMode_decay (h : GaussianWholeLineMode c F) :
    Tendsto F atTop (𝓝 0) ∧ Tendsto F atBot (𝓝 0) :=
  tendsto_zero_of_contDiff_one_memLp (h.regularity.of_le (by norm_num)) h.memLp h.deriv_memLp

/-- Its first derivative tends to zero at both ends (from `F', F'' ∈ L²`). -/
theorem wholeLineMode_derivative_decay (h : GaussianWholeLineMode c F) :
    Tendsto (deriv F) atTop (𝓝 0) ∧ Tendsto (deriv F) atBot (𝓝 0) :=
  tendsto_deriv_zero_of_contDiff_two_memLp h.regularity h.deriv_memLp h.second_memLp

end Decay

/-! ### Unit-mass normalization -/

/-- L² membership gives integrability of the squared norm. -/
theorem integrable_sq_norm_of_memLp_two {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume : Measure ℝ)) :
    Integrable (fun t => ‖F t‖ ^ 2) (volume : Measure ℝ) :=
  hF.integrable_norm_pow (p := 2) (by decide)

/-- A continuous L² field with a nonzero value has strictly positive mass. -/
theorem integral_sq_norm_pos_of_continuous_nonzero {F : ℝ → ℂ}
    (hc : Continuous F) (hm : MemLp F 2 (volume : Measure ℝ))
    (hne : ∃ t, F t ≠ 0) :
    0 < ∫ t : ℝ, ‖F t‖ ^ 2 := by
  have hi := integrable_sq_norm_of_memLp_two hm
  have hnonneg : 0 ≤ ∫ t : ℝ, ‖F t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg ‖F t‖)
  by_contra h
  have hz : (∫ t : ℝ, ‖F t‖ ^ 2) = 0 :=
    le_antisymm (le_of_not_gt h) hnonneg
  have hae : (fun t : ℝ => ‖F t‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖F t‖) hi).1 hz
  have hall : (fun t : ℝ => ‖F t‖ ^ 2) = (fun _ => (0 : ℝ)) :=
    Measure.eq_of_ae_eq hae (hc.norm.pow 2) continuous_const
  obtain ⟨t, ht⟩ := hne
  have hnorm : ‖F t‖ = 0 := eq_zero_of_pow_eq_zero (congrFun hall t)
  exact ht (norm_eq_zero.mp hnorm)

/-- The squared L² mass of a field on the whole line. -/
def wholeLineMass (F : ℝ → ℂ) : ℝ := ∫ t, ‖F t‖ ^ 2

/-- Normalization by the square root of the mass. -/
def normalizeWholeLine (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((Real.sqrt (wholeLineMass F))⁻¹ : ℝ) * F t

theorem wholeLineMass_const_mul (F : ℝ → ℂ) (a : ℂ) :
    wholeLineMass (fun t => a * F t) = ‖a‖ ^ 2 * wholeLineMass F := by
  unfold wholeLineMass
  simp_rw [norm_mul, mul_pow]
  exact integral_const_mul _ _

section Normalize
variable {c : ℂ} {F : ℝ → ℂ}

theorem wholeLineMode_mass_pos (h : GaussianWholeLineMode c F) : 0 < wholeLineMass F :=
  integral_sq_norm_pos_of_continuous_nonzero h.regularity.continuous h.memLp h.nonzero

/-- A nonzero multiple of a mode is a mode. -/
theorem wholeLineMode_const_mul (h : GaussianWholeLineMode c F) (a : ℂ) (ha : a ≠ 0) :
    GaussianWholeLineMode c (fun t => a * F t) := by
  refine ⟨h.upper_half_plane, contDiff_const.mul h.regularity, h.memLp.const_mul a,
    ?_, ?_, ?_, ?_⟩
  · simpa only [deriv_const_mul_field'] using h.deriv_memLp.const_mul a
  · simpa only [deriv_const_mul_field'] using h.second_memLp.const_mul a
  · obtain ⟨t, ht⟩ := h.nonzero
    exact ⟨t, mul_ne_zero ha ht⟩
  · intro t
    simp only [deriv_const_mul_field']
    calc
      ((neutralOmega t : ℂ) - c) * (a * deriv (deriv F) t - 4 * (a * F t)) -
          (gaussianRayleighCoefficient t : ℂ) * (a * F t) =
        a * (((neutralOmega t : ℂ) - c) * (deriv (deriv F) t - 4 * F t) -
          (gaussianRayleighCoefficient t : ℂ) * F t) := by ring
      _ = 0 := by rw [h.equation t, mul_zero]

theorem wholeLineMode_normalization_scalar_ne_zero (h : GaussianWholeLineMode c F) :
    (((Real.sqrt (wholeLineMass F))⁻¹ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (wholeLineMode_mass_pos h)))

theorem wholeLineMode_normalize (h : GaussianWholeLineMode c F) :
    GaussianWholeLineMode c (normalizeWholeLine F) :=
  wholeLineMode_const_mul h _ (wholeLineMode_normalization_scalar_ne_zero h)

theorem wholeLineMode_normalized_mass (h : GaussianWholeLineMode c F) :
    wholeLineMass (normalizeWholeLine F) = 1 := by
  have hp := wholeLineMode_mass_pos h
  change wholeLineMass (fun t => (((Real.sqrt (wholeLineMass F))⁻¹ : ℝ) : ℂ) * F t) = 1
  rw [wholeLineMass_const_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (le_of_lt hp),
    inv_mul_cancel₀ (ne_of_gt hp)]

/-- A nonzero mode has a unit-mass multiple. -/
theorem wholeLineMode_exists_normalized (h : GaussianWholeLineMode c F) :
    ∃ G : ℝ → ℂ, GaussianWholeLineMode c G ∧ (∫ t, ‖G t‖ ^ 2) = 1 :=
  ⟨normalizeWholeLine F, wholeLineMode_normalize h, wholeLineMode_normalized_mass h⟩

end Normalize

end UnforcedLeray.ComplexODEB
