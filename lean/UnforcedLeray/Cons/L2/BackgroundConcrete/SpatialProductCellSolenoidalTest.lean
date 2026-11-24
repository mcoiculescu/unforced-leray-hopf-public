import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellTest

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint

/-- A real distributionally solenoidal field annihilates the derivative pairing of a complex
smooth compactly supported scalar test. The proof splits the test into its real and imaginary
parts, which are the real tests accepted by `IsSolenoidal`. -/
theorem integral_complexTest_gradient_pair_solenoidal {V : SpatialField}
    (hV : IsSolenoidal V) {φ : Space → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun y : Space => ∑ j : Fin 3,
      (V y j : ℂ) * fderiv ℝ φ y (coordinateVector j)) volume ∧
    ∫ y : Space, ∑ j : Fin 3,
      (V y j : ℂ) * fderiv ℝ φ y (coordinateVector j) = 0 := by
  let φre : Space → ℝ := fun y => (φ y).re
  let φim : Space → ℝ := fun y => (φ y).im
  have hre : IsSpatialTest φre :=
    ⟨Complex.reCLM.contDiff.comp hφ, hφc.comp_left Complex.zero_re⟩
  have him : IsSpatialTest φim :=
    ⟨Complex.imCLM.contDiff.comp hφ, hφc.comp_left Complex.zero_im⟩
  have hDre (j : Fin 3) (y : Space) :
      spatialTestDerivative j φre y = (fderiv ℝ φ y (coordinateVector j)).re := by
    have h := (Complex.reCLM.hasFDerivAt.comp y
      (hφ.differentiable (by simp) y).hasFDerivAt)
    have hD : fderiv ℝ φre y = Complex.reCLM.comp (fderiv ℝ φ y) := h.fderiv
    simp [spatialTestDerivative, φre, hD]
  have hDim (j : Fin 3) (y : Space) :
      spatialTestDerivative j φim y = (fderiv ℝ φ y (coordinateVector j)).im := by
    have h := (Complex.imCLM.hasFDerivAt.comp y
      (hφ.differentiable (by simp) y).hasFDerivAt)
    have hD : fderiv ℝ φim y = Complex.imCLM.comp (fderiv ℝ φ y) := h.fderiv
    simp [spatialTestDerivative, φim, hD]
  let g : Space → ℂ := fun y => ∑ j : Fin 3,
    (V y j : ℂ) * fderiv ℝ φ y (coordinateVector j)
  let gRe : Space → ℝ := fun y =>
    ∑ j : Fin 3, V y j * spatialTestDerivative j φre y
  let gIm : Space → ℝ := fun y =>
    ∑ j : Fin 3, V y j * spatialTestDerivative j φim y
  have hRe : Integrable gRe volume := hV.integrable φre hre
  have hIm : Integrable gIm volume := hV.integrable φim him
  have hgRe : ∀ y, (g y).re = gRe y := by
    intro y
    simp [g, gRe, Complex.re_sum, Complex.mul_re, hDre]
  have hgIm : ∀ y, (g y).im = gIm y := by
    intro y
    simp [g, gIm, Complex.im_sum, Complex.mul_im, hDim]
  have hg : Integrable g volume := by
    refine (Integrable.re_im_iff (f := g) (μ := volume)).mp ⟨?_, ?_⟩
    · exact hRe.congr (ae_of_all _ fun y => (hgRe y).symm)
    · exact hIm.congr (ae_of_all _ fun y => (hgIm y).symm)
  have hgreq : (fun y => (g y).re) = gRe := funext hgRe
  have hgimEq : (fun y => (g y).im) = gIm := funext hgIm
  have hzeroRe : ((∫ y, g y).re) = 0 := by
    calc
      (∫ y, g y).re = ∫ y, (g y).re := (integral_re hg).symm
      _ = ∫ y, gRe y := by rw [hgreq]
      _ = 0 := hV.identity φre hre
  have hzeroIm : ((∫ y, g y).im) = 0 := by
    calc
      (∫ y, g y).im = ∫ y, (g y).im := (integral_im hg).symm
      _ = ∫ y, gIm y := by rw [hgimEq]
      _ = 0 := hV.identity φim him
  refine ⟨?_, ?_⟩
  · simpa [g] using hg
  · apply Complex.ext
    · exact hzeroRe
    · exact hzeroIm

#print axioms integral_complexTest_gradient_pair_solenoidal

end UnforcedLeray.Cons.C03.Concrete
