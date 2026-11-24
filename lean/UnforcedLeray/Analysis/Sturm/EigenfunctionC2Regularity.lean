import UnforcedLeray.Analysis.Sturm.EigenfunctionRegularity
import UnforcedLeray.Analysis.Sturm.OneDRegularitySecond
import UnforcedLeray.Analysis.Sturm.NeutralPotentialRegularity

/-!
# Actual classical Gaussian Sturm eigenfunctions

For the constructed Birman–Schwinger fixed vector, its source equals the
Gaussian potential times its continuous Green representative almost
everywhere. This is a genuinely continuous L² source. The actual Green
kernel's second derivative formula therefore upgrades this constructed
representative to C² and proves the Gaussian differential equation pointwise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- The continuous source obtained from the actual Gaussian potential and
actual Green representative. -/
def gaussianSturmContinuousSource (m : ℝ) (f : ComplexL2) : ℝ → ℂ :=
  fun x => (Wlog x : ℂ) * freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ) x

theorem gaussianSturmContinuousSource_continuous {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    Continuous (gaussianSturmContinuousSource m f) :=
  (Complex.continuous_ofReal.comp continuous_Wlog).mul
    (freeResolventC1Representative hm (complexPotentialSqrtOperator f)).continuous

theorem coeFn_potential_freeResolvent {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    complexPotentialOperator (freeResolventOperator hm (complexPotentialSqrtOperator f)) =ᵐ[volume]
      gaussianSturmContinuousSource m f := by
  filter_upwards [coeFn_complexPotentialOperator
    (freeResolventOperator hm (complexPotentialSqrtOperator f)),
    coeFn_freeResolventOperator hm (complexPotentialSqrtOperator f)] with x hp hu
  simpa only [gaussianSturmContinuousSource, hu] using hp

theorem gaussianSturmContinuousSource_memLp {m : ℝ} (hm : 0 < m) (f : ComplexL2) :
    MemLp (gaussianSturmContinuousSource m f) 2 volume :=
  (Lp.memLp (complexPotentialOperator
    (freeResolventOperator hm (complexPotentialSqrtOperator f)))).ae_eq
      (coeFn_potential_freeResolvent hm f)

/-- The actual fixed-vector equation identifies the source with this continuous function. -/
theorem sqrtPotential_fixedVector_source_ae {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (heigen : birmanSchwingerOperator hm f = f) :
    (complexPotentialSqrtOperator f : ℝ → ℂ) =ᵐ[volume] gaussianSturmContinuousSource m f := by
  have hSu : complexPotentialSqrtOperator
      (freeResolventOperator hm (complexPotentialSqrtOperator f)) = f := heigen
  have hPu : complexPotentialOperator
      (freeResolventOperator hm (complexPotentialSqrtOperator f)) = complexPotentialSqrtOperator f := by
    have hs := congrArg (fun A : ComplexL2 →L[ℂ] ComplexL2 =>
      A (freeResolventOperator hm (complexPotentialSqrtOperator f)))
      complexPotentialSqrtOperator_comp_self
    change complexPotentialSqrtOperator
      (complexPotentialSqrtOperator (freeResolventOperator hm (complexPotentialSqrtOperator f))) =
        complexPotentialOperator (freeResolventOperator hm (complexPotentialSqrtOperator f)) at hs
    rw [hSu] at hs
    exact hs.symm
  rw [← hPu]
  exact coeFn_potential_freeResolvent hm f

theorem freeResolvent_fixedVector_source_eq {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (heigen : birmanSchwingerOperator hm f = f) :
    freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ) =
      freeResolvent m (gaussianSturmContinuousSource m f) :=
  freeResolvent_congr_ae m (sqrtPotential_fixedVector_source_ae hm f heigen)

/-- C² regularity for the actual Green representative of every fixed vector. -/
theorem contDiff_two_gaussianSturm_fixedVector {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (heigen : birmanSchwingerOperator hm f = f) :
    ContDiff ℝ 2 (freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ)) := by
  rw [freeResolvent_fixedVector_source_eq hm f heigen]
  exact contDiff_two_freeResolvent_of_memLp_continuous hm
    (gaussianSturmContinuousSource_memLp hm f) (gaussianSturmContinuousSource_continuous hm f)

/-- The second classical derivative is the actual Gaussian differential expression. -/
theorem deriv_deriv_gaussianSturm_fixedVector {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (heigen : birmanSchwingerOperator hm f = f) :
    deriv (deriv (freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ))) =
      fun x => ((m : ℂ) ^ 2 - (Wlog x : ℂ)) *
        freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ) x := by
  have hsource := gaussianSturmContinuousSource_memLp hm f
  have hcontinuous := gaussianSturmContinuousSource_continuous hm f
  rw [freeResolvent_fixedVector_source_eq hm f heigen,
    deriv_freeResolvent_of_memLp hm hsource,
    deriv_freeResolventDeriv_of_memLp_continuous hm hsource hcontinuous]
  funext x
  simp only [gaussianSturmContinuousSource]
  rw [freeResolvent_fixedVector_source_eq hm f heigen]
  ring

theorem gaussianSturmC1Representative_contDiff_two {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    ContDiff ℝ 2 (gaussianSturmC1Representative hm f hf heigen).value :=
  contDiff_two_gaussianSturm_fixedVector hm f heigen

/-- The constructed nonzero representative solves the claimed Sturm equation at every point. -/
theorem gaussianSturmC1Representative_equation {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) (x : ℝ) :
    -deriv (deriv (gaussianSturmC1Representative hm f hf heigen).value) x +
      (4 - (Wlog x : ℂ)) * (gaussianSturmC1Representative hm f hf heigen).value x =
        ((4 - m ^ 2 : ℝ) : ℂ) * (gaussianSturmC1Representative hm f hf heigen).value x := by
  simp only [gaussianSturmC1Representative_value]
  rw [deriv_deriv_gaussianSturm_fixedVector hm f heigen]
  push_cast
  ring

/-- Classical solutions packaged with the actual global Lebesgue L² hypotheses. -/
structure ClassicalGaussianSturmEigenfunction (eigenvalue : ℝ) where
  value : ℝ → ℂ
  contDiff : ContDiff ℝ 2 value
  memLp : MemLp value 2 volume
  deriv_memLp : MemLp (deriv value) 2 volume
  nonzero : ∃ x, value x ≠ 0
  equation : ∀ x, -deriv (deriv value) x + (4 - (Wlog x : ℂ)) * value x =
    (eigenvalue : ℂ) * value x

/-- The concrete fixed-vector construction produces a genuine global C² Sturm eigenfunction. -/
def classicalGaussianSturmEigenfunctionOfBirmanSchwinger {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    ClassicalGaussianSturmEigenfunction (4 - m ^ 2) where
  value := (gaussianSturmC1Representative hm f hf heigen).value
  contDiff := gaussianSturmC1Representative_contDiff_two hm f hf heigen
  memLp := (gaussianSturmC1Representative hm f hf heigen).memLp
  deriv_memLp := (gaussianSturmC1Representative hm f hf heigen).deriv_memLp
  nonzero := gaussianSturmC1Representative_nonzero hm f hf heigen
  equation := gaussianSturmC1Representative_equation hm f hf heigen

end UnforcedLeray.Sturm
