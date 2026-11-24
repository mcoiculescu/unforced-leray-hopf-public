import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/8` helper: the complex pairing split into real pieces

For real fields `x₁, x₂, y₁, y₂` the bilinear complex pairing (`dotL`, no conjugation) of
`x₁ + i x₂` with `y₁ + i y₂` is `⟪x₁,y₁⟫ - ⟪x₂,y₂⟫ + i(⟪x₁,y₂⟫ + ⟪x₂,y₁⟫)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.ComplexAdjointOpAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0418 UnforcedLeray.RieszLp

theorem dotL_ofReV_ofImV (x₁ x₂ y₁ y₂ : Space) :
    dotL (ofReV x₁ + ofImV x₂) (ofReV y₁ + ofImV y₂) =
      ((inner ℝ x₁ y₁ - inner ℝ x₂ y₂ : ℝ) : ℂ) +
        Complex.I * ((inner ℝ x₁ y₂ + inner ℝ x₂ y₁ : ℝ) : ℂ) := by
  rw [dotL_apply]
  simp only [Fin.sum_univ_three, PiLp.add_apply, ofReV_apply, ofImV_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Integrability of the real inner product of two `L^{p}` / `L^{q}` fields
(Hölder with conjugate exponents). -/
theorem integrable_inner_of_memLp {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {f g : SpatialField} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) volume := by
  refine Integrable.mono' (hf.norm.integrable_mul hg.norm)
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  simpa using norm_inner_le_norm (𝕜 := ℝ) (f y) (g y)

/-- The integral of the complex pairing of two complexified pairs, split into real pieces. -/
theorem integral_dotL_split (x₁ x₂ y₁ y₂ : SpatialField)
    (h11 : Integrable (fun y => inner ℝ (x₁ y) (y₁ y)) volume)
    (h22 : Integrable (fun y => inner ℝ (x₂ y) (y₂ y)) volume)
    (h12 : Integrable (fun y => inner ℝ (x₁ y) (y₂ y)) volume)
    (h21 : Integrable (fun y => inner ℝ (x₂ y) (y₁ y)) volume) :
    ∫ y, dotL (ofReV (x₁ y) + ofImV (x₂ y)) (ofReV (y₁ y) + ofImV (y₂ y)) =
      ((∫ y, inner ℝ (x₁ y) (y₁ y) : ℝ) : ℂ) - ((∫ y, inner ℝ (x₂ y) (y₂ y) : ℝ) : ℂ) +
        Complex.I * (((∫ y, inner ℝ (x₁ y) (y₂ y) : ℝ) : ℂ) +
          ((∫ y, inner ℝ (x₂ y) (y₁ y) : ℝ) : ℂ)) := by
  simp only [dotL_ofReV_ofImV]
  have hA : Integrable (fun y : Space => ((inner ℝ (x₁ y) (y₁ y) - inner ℝ (x₂ y) (y₂ y) : ℝ) : ℂ))
      volume := (h11.sub h22).ofReal
  have hB : Integrable (fun y : Space =>
      Complex.I * ((inner ℝ (x₁ y) (y₂ y) + inner ℝ (x₂ y) (y₁ y) : ℝ) : ℂ)) volume :=
    ((h12.add h21).ofReal).const_mul _
  have e1 : ∫ y : Space, ((inner ℝ (x₁ y) (y₁ y) - inner ℝ (x₂ y) (y₂ y) : ℝ) : ℂ) ∂volume =
      ((∫ y, inner ℝ (x₁ y) (y₁ y) : ℝ) : ℂ) - ((∫ y, inner ℝ (x₂ y) (y₂ y) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_sub h11 h22, Complex.ofReal_sub]
  have e2 : ∫ y : Space, ((inner ℝ (x₁ y) (y₂ y) + inner ℝ (x₂ y) (y₁ y) : ℝ) : ℂ) ∂volume =
      ((∫ y, inner ℝ (x₁ y) (y₂ y) : ℝ) : ℂ) + ((∫ y, inner ℝ (x₂ y) (y₁ y) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_add h12 h21, Complex.ofReal_add]
  rw [integral_add hA hB, e1, integral_const_mul, e2]

end UnforcedLeray.Short.PartIIa.ComplexAdjointOpAux
