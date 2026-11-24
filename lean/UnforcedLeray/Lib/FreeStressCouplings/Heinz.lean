import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# A Heinz-type C*-inequality (INF10 F2, core step)


§5 Level F, target **F2** (Wave 1, block 1J, bypass B9); blueprint unit **B0474**
(tex 7790-7812, `eq:free-stress-28`).

The manuscript obtains `‖C₀^{1/2} 𝓡_μ D₀^{1/2}‖ ≤ C_μ` from the endpoint bounds `C₀ 𝓡_μ` and
`𝓡_μ D₀` by the three-lines lemma applied to `z ↦ ⟨C₀^z 𝓡_μ D₀^{1-z} φ, ψ⟩` after spectral
cutoffs (tex 7790-7808).  Only the midpoint `z = 1/2` is used downstream (tex 7872, 8220).  At
the midpoint the three-lines bound is the following C*-algebra inequality, proved here with the
C*-identity and `spectralRadius (a * b) = spectralRadius (b * a)` instead of complex analysis:

`‖p r q‖² ≤ ‖p⋆ p r‖ · ‖r q q⋆‖`.

With `p = C₀^{1/2}` and `q = D₀^{1/2}` cut off spectrally (bounded and selfadjoint) this is
`‖C₀^{1/2} R D₀^{1/2}‖ ≤ (‖C₀ R‖ ‖R D₀‖)^{1/2}`, the three-lines bound at `θ = 1/2` with the
constant `M₀^{1/2} M₁^{1/2}` (the product of the endpoint bounds, as the blueprint note on
B0474 asks).  No commutation between `p` and `q` is used (tex 7807-7808).

Main results:
* `spectralRadius_mul_comm`: `r(ab) = r(ba)` in any complex Banach algebra;
* `norm_mul_mul_sq_le`: `‖p r q‖² ≤ ‖p⋆ p r‖ ‖r q q⋆‖` in a C*-algebra;
* `norm_mul_mul_le_sqrt`: the selfadjoint form `‖p r q‖ ≤ √(‖p p r‖ ‖r q q‖)`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal

namespace UnforcedLeray.FreeStress

section SpectralRadius

variable {𝕜 B : Type*} [NormedField 𝕜] [Ring B] [Algebra 𝕜 B]

/-- The spectral radius only sees the nonzero spectrum. -/
theorem spectralRadius_eq_iSup_diff_zero (a : B) :
    spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a \ {0}, (‖k‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    by_cases h0 : k = 0
    · simp [h0]
    · exact le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 a \ {0}) => (‖k‖₊ : ℝ≥0∞)) k ⟨hk, h0⟩
  · exact iSup₂_le fun k hk =>
      le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 a) => (‖k‖₊ : ℝ≥0∞)) k hk.1

/-- `spectralRadius (a * b) = spectralRadius (b * a)` (Jacobson's lemma). -/
theorem spectralRadius_mul_comm (a b : B) :
    spectralRadius 𝕜 (a * b) = spectralRadius 𝕜 (b * a) := by
  rw [spectralRadius_eq_iSup_diff_zero, spectralRadius_eq_iSup_diff_zero,
    spectrum.nonzero_mul_comm]

end SpectralRadius

variable {A : Type*} [CStarAlgebra A]

/-- **Heinz-type inequality.** In a C*-algebra, `‖p r q‖² ≤ ‖p⋆ p r‖ · ‖r q q⋆‖`.

This is the midpoint case of the three-lines interpolation of tex 7790-7808 (B0474,
`eq:free-stress-28`). -/
theorem norm_mul_mul_sq_le (p r q : A) :
    ‖p * r * q‖ ^ 2 ≤ ‖star p * p * r‖ * ‖r * (q * star q)‖ := by
  nontriviality A
  set x := p * r * q with hx
  set X := star r * star p * p * r * q with hX
  have hs : star x * x = star q * X := by
    simp only [hx, hX, star_mul, mul_assoc]
  have hsa : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have key : (‖star x * x‖₊ : ℝ≥0∞) ≤ ‖X * star q‖₊ := by
    rw [← hsa.spectralRadius_eq_nnnorm, hs, spectralRadius_mul_comm]
    exact spectrum.spectralRadius_le_nnnorm _
  have key' : ‖star x * x‖ ≤ ‖X * star q‖ := by
    have := ENNReal.coe_le_coe.mp key
    exact_mod_cast this
  have hfac : X * star q = star (star p * p * r) * (r * (q * star q)) := by
    simp only [hX, star_mul, star_star, mul_assoc]
  rw [sq, ← CStarRing.norm_star_mul_self]
  calc ‖star x * x‖ ≤ ‖X * star q‖ := key'
    _ = ‖star (star p * p * r) * (r * (q * star q))‖ := by rw [hfac]
    _ ≤ ‖star (star p * p * r)‖ * ‖r * (q * star q)‖ := norm_mul_le _ _
    _ = ‖star p * p * r‖ * ‖r * (q * star q)‖ := by rw [norm_star]

/-- **Heinz-type inequality, selfadjoint form.** For selfadjoint `p, q`,
`‖p r q‖ ≤ √(‖p p r‖ ‖r q q‖)` (B0474, tex 7790-7808, midpoint of the three-lines lemma). -/
theorem norm_mul_mul_le_sqrt {p q : A} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) (r : A) :
    ‖p * r * q‖ ≤ Real.sqrt (‖p * p * r‖ * ‖r * (q * q)‖) := by
  have h := norm_mul_mul_sq_le p r q
  rw [hp.star_eq, hq.star_eq] at h
  exact Real.le_sqrt_of_sq_le h

/-- Midpoint interpolation with endpoint constants: if `‖p p r‖ ≤ M₁` and `‖r q q‖ ≤ M₀` for
selfadjoint `p, q`, then `‖p r q‖ ≤ √(M₀ M₁)`. -/
theorem norm_mul_mul_le_of_endpoints {p q : A} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (r : A) {M₀ M₁ : ℝ} (h₁ : ‖p * p * r‖ ≤ M₁) (h₀ : ‖r * (q * q)‖ ≤ M₀) :
    ‖p * r * q‖ ≤ Real.sqrt (M₀ * M₁) := by
  refine (norm_mul_mul_le_sqrt hp hq r).trans (Real.sqrt_le_sqrt ?_)
  rw [mul_comm M₀]
  exact mul_le_mul h₁ h₀ (norm_nonneg _) ((norm_nonneg _).trans h₁)

end UnforcedLeray.FreeStress
