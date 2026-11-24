import UnforcedLeray.Infra.AnalyticFredholm.Global
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Convex

/-!
# Spectrum of a compact perturbation outside the spectral radius

Corollary of the analytic Fredholm theorem (`analyticFredholm`).  Let `A : X →L[ℂ] X` on a
complex Banach space have spectral radius `< q`, and let `K` be approximable by finite-rank
operators.  On `U = {z | q < ‖z‖}` (preconnected, `isPreconnected_setOf_lt_norm`)

`z - (A + K) = (z - A) (1 - (z - A)⁻¹ K)`,

`F z = (z - A)⁻¹ K` is analytic and approximable, and `‖F z‖ → 0` as `‖z‖ → ∞`, so `1 - F z₀` is
invertible for some `z₀ ∈ U`.  Hence the spectrum of `A + K` in `U` is discrete and closed in
`U`, and it meets `{z | r ≤ ‖z‖}` in a finite set for every `r > q`
(`finite_spectrum_add_inter`, `finite_spectrum_add_inter_of_spectralRadius_lt`,
`eventually_not_mem_spectrum_add`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Bornology
open scoped NNReal ENNReal

namespace UnforcedLeray.Infra.AnalyticFredholm

/-- The exterior `{z | c < ‖z‖}` of a closed disc of positive radius is preconnected (it is the
image of a half-plane under `Complex.exp`). -/
theorem isPreconnected_setOf_lt_norm {c : ℝ} (hc : 0 < c) :
    IsPreconnected {z : ℂ | c < ‖z‖} := by
  have heq : {z : ℂ | c < ‖z‖} = Complex.exp '' {w : ℂ | Real.log c < w.re} := by
    ext z
    constructor
    · intro hz
      have hz' : c < ‖z‖ := hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hz'
        linarith
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log c < (Complex.log z).re
      rw [Complex.log_re]
      exact Real.log_lt_log hc hz'
    · rintro ⟨w, hw, rfl⟩
      have hw' : Real.log c < w.re := hw
      change c < ‖Complex.exp w‖
      rw [Complex.norm_exp]
      calc c = Real.exp (Real.log c) := (Real.exp_log hc).symm
        _ < Real.exp w.re := Real.exp_lt_exp.mpr hw'
  rw [heq]
  exact (convex_halfSpace_re_gt (Real.log c)).isPreconnected.image _
    Complex.continuous_exp.continuousOn

/-- The resolvent `z ↦ (z - a)⁻¹` of an element of a complex Banach algebra is analytic on the
resolvent set. -/
theorem analyticAt_resolvent {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜] [CompleteSpace 𝒜]
    {a : 𝒜} {z : ℂ} (hz : z ∈ resolventSet ℂ a) : AnalyticAt ℂ (resolvent a) z := by
  have hu : IsUnit (algebraMap ℂ 𝒜 z - a) := spectrum.mem_resolventSet_iff.mp hz
  have h1 : AnalyticAt ℂ (fun w : ℂ => algebraMap ℂ 𝒜 w - a) z := by
    have he : (fun w : ℂ => algebraMap ℂ 𝒜 w - a) =
        fun w => (ContinuousLinearMap.id ℂ ℂ).smulRight (1 : 𝒜) w - a := by
      funext w
      simp [Algebra.algebraMap_eq_smul_one]
    rw [he]
    exact (ContinuousLinearMap.analyticAt _ _).sub analyticAt_const
  exact (analyticAt_inverse (𝕜 := ℂ) hu.unit).comp_of_eq h1 hu.unit_spec.symm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The factorization `z - (A + K) = (z - A) (1 - (z - A)⁻¹ K)` on the resolvent set of `A`:
invertibility of `1 - (z - A)⁻¹ K` implies `z ∉ σ(A + K)`. -/
theorem not_mem_spectrum_add_of_isUnit {A K : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ A)
    (hu : IsUnit (1 - resolvent A z * K)) : z ∉ spectrum ℂ (A + K) := by
  have hzA : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) := spectrum.mem_resolventSet_iff.mp hz
  rw [spectrum.mem_iff, not_not]
  have hfact : algebraMap ℂ (X →L[ℂ] X) z - (A + K) =
      (algebraMap ℂ (X →L[ℂ] X) z - A) * (1 - resolvent A z * K) := by
    rw [mul_sub, mul_one, ← mul_assoc, resolvent, Ring.mul_inverse_cancel _ hzA, one_mul]
    abel
  rw [hfact]
  exact hzA.mul hu

section Corollary

variable {A K : X →L[ℂ] X} {q : ℝ≥0}

/-- Data for the corollary: on `{z | q < ‖z‖}`, with `spectralRadius ℂ A < q`, the family
`F z = (z - A)⁻¹ K` satisfies the hypotheses of `analyticFredholm`. -/
theorem fredholm_data_resolvent_mul (hA : spectralRadius ℂ A < q) (hK : IsApproximable K) :
    IsPreconnected {z : ℂ | (q : ℝ) < ‖z‖} ∧
    (∀ z ∈ {z : ℂ | (q : ℝ) < ‖z‖}, z ∈ resolventSet ℂ A) ∧
    AnalyticOnNhd ℂ (fun z => resolvent A z * K) {z : ℂ | (q : ℝ) < ‖z‖} ∧
    (∀ z ∈ {z : ℂ | (q : ℝ) < ‖z‖}, IsApproximable (resolvent A z * K)) ∧
    ∃ z₀ ∈ {z : ℂ | (q : ℝ) < ‖z‖}, IsUnit (1 - resolvent A z₀ * K) := by
  have hq : (0 : ℝ) < q := by
    have h0 : (0 : ℝ≥0∞) < q := lt_of_le_of_lt zero_le hA
    exact_mod_cast h0
  have hres : ∀ z ∈ {z : ℂ | (q : ℝ) < ‖z‖}, z ∈ resolventSet ℂ A := by
    intro z hz
    apply spectrum.mem_resolventSet_of_spectralRadius_lt
    refine hA.trans ?_
    have hz' : (q : ℝ) < ‖z‖ := hz
    have : q < ‖z‖₊ := by
      rw [← NNReal.coe_lt_coe, coe_nnnorm]
      exact hz'
    exact_mod_cast this
  refine ⟨isPreconnected_setOf_lt_norm hq, hres, ?_, ?_, ?_⟩
  · intro z hz
    exact (analyticAt_resolvent (hres z hz)).mul analyticAt_const
  · intro z _
    exact hK.comp_left (resolvent A z)
  · have h1 : ∀ᶠ z in cobounded ℂ, (q : ℝ) < ‖z‖ :=
      tendsto_norm_cobounded_atTop.eventually_gt_atTop _
    have h2 : Tendsto (fun z => ‖resolvent A z‖ * ‖K‖) (cobounded ℂ) (𝓝 0) := by
      have := ((spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) A).norm).mul_const ‖K‖
      simpa using this
    obtain ⟨z₀, hz₀U, hz₀⟩ := (h1.and (h2.eventually (gt_mem_nhds one_pos))).exists
    refine ⟨z₀, hz₀U, ?_⟩
    have hnorm : ‖resolvent A z₀ * K‖ < 1 := (norm_mul_le _ _).trans_lt hz₀
    have := (Units.oneSub _ hnorm).isUnit
    rwa [Units.val_oneSub] at this

/-- Outside the circle of radius `q > spectralRadius A`, the spectrum of `A + K` (`K`
approximable) has no accumulation point: every `w` with `q < ‖w‖` has a punctured
neighbourhood disjoint from `spectrum ℂ (A + K)`. -/
theorem eventually_not_mem_spectrum_add (hA : spectralRadius ℂ A < q) (hK : IsApproximable K)
    {w : ℂ} (hw : (q : ℝ) < ‖w‖) : ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum ℂ (A + K) := by
  obtain ⟨hUc, hres, hF, happrox, z₀, hz₀, hinv⟩ := fredholm_data_resolvent_mul hA hK
  have hopen : IsOpen {z : ℂ | (q : ℝ) < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hev := analyticFredholm hUc hF happrox hz₀ hinv w hw
  have hU : ∀ᶠ z in 𝓝[≠] w, z ∈ {z : ℂ | (q : ℝ) < ‖z‖} :=
    nhdsWithin_le_nhds (hopen.mem_nhds hw)
  filter_upwards [hev, hU] with z hz hzU
  exact not_mem_spectrum_add_of_isUnit (hres z hzU) hz

/-- **Finiteness of the outer spectrum.** If `spectralRadius ℂ A < r` and `K` is approximable by
finite-rank operators, then `spectrum ℂ (A + K) ∩ {z | r ≤ ‖z‖}` is finite. -/
theorem finite_spectrum_add_inter_of_spectralRadius_lt (hK : IsApproximable K) {r : ℝ≥0}
    (hr : spectralRadius ℂ A < r) :
    (spectrum ℂ (A + K) ∩ {z : ℂ | (r : ℝ) ≤ ‖z‖}).Finite := by
  obtain ⟨q, hAq, hqr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hqr' : (q : ℝ) < r := by exact_mod_cast hqr
  obtain ⟨hUc, hres, hF, happrox, z₀, hz₀, hinv⟩ := fredholm_data_resolvent_mul hAq hK
  have hC : IsCompact (spectrum ℂ (A + K) ∩ {z : ℂ | (r : ℝ) ≤ ‖z‖}) :=
    (spectrum.isCompact (A + K)).inter_right (isClosed_le continuous_const continuous_norm)
  have hCU : spectrum ℂ (A + K) ∩ {z : ℂ | (r : ℝ) ≤ ‖z‖} ⊆ {z : ℂ | (q : ℝ) < ‖z‖} :=
    fun z hz => lt_of_lt_of_le hqr' hz.2
  refine (analyticFredholm_finite_inter_compact hUc hF happrox hz₀ hinv hC hCU).subset ?_
  intro z hz
  refine ⟨⟨hCU hz, fun hu => ?_⟩, hz⟩
  exact not_mem_spectrum_add_of_isUnit (hres z (hCU hz)) hu hz.1

/-- **Finiteness of the outer spectrum**, in the form of the specification: if
`spectralRadius ℂ A < q`, `K` is approximable by finite-rank operators and `q < r`, then
`spectrum ℂ (A + K) ∩ {z | r ≤ ‖z‖}` is finite. -/
theorem finite_spectrum_add_inter (hA : spectralRadius ℂ A < q) (hK : IsApproximable K)
    {r : ℝ} (hr : (q : ℝ) < r) :
    (spectrum ℂ (A + K) ∩ {z : ℂ | r ≤ ‖z‖}).Finite := by
  have hr0 : 0 ≤ r := le_trans q.2 hr.le
  have hqr : q < r.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r hr0]
    exact hr
  have h := finite_spectrum_add_inter_of_spectralRadius_lt (A := A) hK (r := r.toNNReal)
    (hA.trans (by exact_mod_cast hqr))
  rwa [Real.coe_toNNReal r hr0] at h

end Corollary

end UnforcedLeray.Infra.AnalyticFredholm
