import UnforcedLeray.Analysis.Sturm.OneDRegularity
import UnforcedLeray.Analysis.Sturm.BirmanSchwingerEigenfunction

/-!
# Classical representatives of the constructed Gaussian Sturm eigenfunctions

A `C1L2Representative u du` records an actual continuously differentiable
function representing `u`, whose classical derivative represents `du`.
The concrete Green convolution supplies this structure for the resolvent and
for the eigenfunctions constructed from its Birman–Schwinger fixed vectors.
No regularity assertion is made here for arbitrary weak eigenfunctions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace UnforcedLeray.Sturm

/-- A genuine C¹ representative with its actual L² derivative class. -/
structure C1L2Representative (u du : ComplexL2) where
  value : ℝ → ℂ
  contDiff : ContDiff ℝ 1 value
  value_ae : (u : ℝ → ℂ) =ᵐ[volume] value
  derivative_ae : (du : ℝ → ℂ) =ᵐ[volume] deriv value

namespace C1L2Representative
variable {u du : ComplexL2} (v : C1L2Representative u du)

theorem continuous : Continuous v.value := v.contDiff.continuous

theorem continuous_derivative : Continuous (deriv v.value) := v.contDiff.continuous_deriv_one

theorem memLp : MemLp v.value 2 volume := (Lp.memLp u).ae_eq v.value_ae

theorem deriv_memLp : MemLp (deriv v.value) 2 volume := (Lp.memLp du).ae_eq v.derivative_ae

theorem toLp_value : v.memLp.toLp v.value = u := by
  apply Lp.ext
  exact v.memLp.coeFn_toLp.trans v.value_ae.symm

theorem toLp_derivative : v.deriv_memLp.toLp (deriv v.value) = du := by
  apply Lp.ext
  exact v.deriv_memLp.coeFn_toLp.trans v.derivative_ae.symm

theorem integrable_norm_sq : Integrable (fun x => ‖v.value x‖ ^ 2) :=
  NonUniqueEuler.Sob.EnergyAux.integrable_norm_sq v.memLp

theorem integrable_derivative_norm_sq : Integrable (fun x => ‖deriv v.value x‖ ^ 2) :=
  NonUniqueEuler.Sob.EnergyAux.integrable_norm_sq v.deriv_memLp

/-- The concrete representative has exactly the norm of the given L² class. -/
theorem integral_norm_sq : (∫ x, ‖v.value x‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    (∫ x, ‖v.value x‖ ^ 2) = ∫ x, ‖u x‖ ^ 2 := by
      apply integral_congr_ae
      exact v.value_ae.symm.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
    _ = ‖u‖ ^ 2 := by
      simpa only [NonUniqueEuler.Sob.l2, Lp.norm_def] using
        (NonUniqueEuler.Sob.EnergyAux.l2_sq_eq_integral (Lp.memLp u)).symm

/-- The classical derivative has exactly the norm of the derivative L² class. -/
theorem integral_derivative_norm_sq : (∫ x, ‖deriv v.value x‖ ^ 2) = ‖du‖ ^ 2 := by
  calc
    (∫ x, ‖deriv v.value x‖ ^ 2) = ∫ x, ‖du x‖ ^ 2 := by
      apply integral_congr_ae
      exact v.derivative_ae.symm.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
    _ = ‖du‖ ^ 2 := by
      simpa only [NonUniqueEuler.Sob.l2, Lp.norm_def] using
        (NonUniqueEuler.Sob.EnergyAux.l2_sq_eq_integral (Lp.memLp du)).symm

theorem exists_value_ne_zero (hu : u ≠ 0) : ∃ x, v.value x ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [v.value_ae] with x hx
  simpa only [h x, Pi.zero_apply] using hx

theorem integral_norm_sq_pos (hu : u ≠ 0) : 0 < ∫ x, ‖v.value x‖ ^ 2 := by
  rw [v.integral_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hu)

theorem re_contDiff : ContDiff ℝ 1 (fun x => (v.value x).re) :=
  Complex.reCLM.contDiff.comp v.contDiff

theorem im_contDiff : ContDiff ℝ 1 (fun x => (v.value x).im) :=
  Complex.imCLM.contDiff.comp v.contDiff

theorem re_memLp : MemLp (fun x => (v.value x).re) 2 volume := v.memLp.re

theorem im_memLp : MemLp (fun x => (v.value x).im) 2 volume := v.memLp.im

end C1L2Representative

/-- The actual exponential-kernel convolution is the C¹ representative of the
bounded resolvent and its verified weak-derivative operator. -/
def freeResolventC1Representative {L : ℝ} (hL : 0 < L) (f : ComplexL2) :
    C1L2Representative (freeResolventOperator hL f) (freeResolventDerivativeOperator hL f) where
  value := freeResolvent L (f : ℝ → ℂ)
  contDiff := contDiff_one_freeResolvent_of_memLp hL (Lp.memLp f)
  value_ae := coeFn_freeResolventOperator hL f
  derivative_ae := by
    rw [deriv_freeResolvent_of_memLp hL (Lp.memLp f)]
    exact coeFn_freeResolventDerivativeOperator hL f

@[simp]
theorem freeResolventC1Representative_value {L : ℝ} (hL : 0 < L) (f : ComplexL2) :
    (freeResolventC1Representative hL f).value = freeResolvent L (f : ℝ → ℂ) := rfl

/-- Classical regularity for the eigenfunction actually produced by the
Birman–Schwinger construction. -/
def gaussianSturmC1Representative {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    C1L2Representative
      (gaussianSturmEigenfunctionOfBirmanSchwinger hm f hf heigen).value
      (gaussianSturmEigenfunctionOfBirmanSchwinger hm f hf heigen).first :=
  freeResolventC1Representative hm (complexPotentialSqrtOperator f)

@[simp]
theorem gaussianSturmC1Representative_value {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    (gaussianSturmC1Representative hm f hf heigen).value =
      freeResolvent m (complexPotentialSqrtOperator f : ℝ → ℂ) := rfl

/-- In particular the constructed classical representative is genuinely nonzero. -/
theorem gaussianSturmC1Representative_nonzero {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    ∃ x, (gaussianSturmC1Representative hm f hf heigen).value x ≠ 0 :=
  (gaussianSturmC1Representative hm f hf heigen).exists_value_ne_zero
    (gaussianSturmEigenfunctionOfBirmanSchwinger hm f hf heigen).nonzero

end UnforcedLeray.Sturm
