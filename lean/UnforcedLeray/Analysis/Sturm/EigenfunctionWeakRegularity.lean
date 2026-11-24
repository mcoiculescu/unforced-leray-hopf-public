import UnforcedLeray.Analysis.Sturm.OneDRegularityH2
import UnforcedLeray.Analysis.Sturm.EigenfunctionC2Regularity
import UnforcedLeray.Analysis.Sturm.NeutralKernelComplex
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Classical regularity and neutral-mode exclusion for genuine weak eigenfunctions

The proved weak free uniqueness theorem recovers any actual weak H² Gaussian
eigenfunction by the mass-two Green operator. Its source is the continuous
function `(λ+Wlog)v`, so the verified classical Green equation gives a C²
representative and the Sturm equation pointwise. This upgrades every genuine
weak eigenfunction and transfers the proved neutral-mode exclusion to it.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace UnforcedLeray.Sturm
open GaussianPotential

namespace GaussianSturmEigenfunction
variable {eigenvalue : ℝ} (u : GaussianSturmEigenfunction eigenvalue)

/-- The mass-two free source of the actual weak H² eigenfunction. -/
def freeSource : ComplexL2 := ((2 : ℝ) : ℂ) ^ 2 • u.value - u.second

theorem freeSource_eq : u.freeSource = (eigenvalue : ℂ) • u.value +
    complexPotentialOperator u.value := by
  unfold freeSource
  norm_num only [Complex.ofReal_ofNat, show (2 : ℂ) ^ 2 = 4 by norm_num]
  calc
    (4 : ℂ) • u.value - u.second =
        (-u.second + (4 : ℂ) • u.value - complexPotentialOperator u.value) +
          complexPotentialOperator u.value := by abel
    _ = _ := by rw [u.equation]

def continuousSource : ℝ → ℂ :=
  fun x => ((eigenvalue : ℂ) + (Wlog x : ℂ)) * u.c1Representative.value x

theorem continuous_continuousSource : Continuous u.continuousSource :=
  (continuous_const.add (Complex.continuous_ofReal.comp continuous_Wlog)).mul
    u.c1Representative.continuous

/-- The weak differential equation identifies the source with a continuous representative. -/
theorem freeSource_ae_continuousSource :
    (u.freeSource : ℝ → ℂ) =ᵐ[volume] u.continuousSource := by
  rw [u.freeSource_eq]
  filter_upwards [Lp.coeFn_add ((eigenvalue : ℂ) • u.value) (complexPotentialOperator u.value),
    Lp.coeFn_smul (eigenvalue : ℂ) u.value, coeFn_complexPotentialOperator u.value,
    u.c1Representative.value_ae] with x ha hs hp hu
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hs
  rw [ha, hs, hp, hu]
  simp only [continuousSource]
  ring

theorem memLp_continuousSource : MemLp u.continuousSource 2 volume :=
  (Lp.memLp u.freeSource).ae_eq u.freeSource_ae_continuousSource

/-- Weak free uniqueness recovers the given L² class, with no spectral assumption. -/
theorem freeResolvent_freeSource_eq :
    freeResolventOperator (by norm_num : (0 : ℝ) < 2) u.freeSource = u.value :=
  weakH2_eq_freeResolvent (by norm_num) u.value u.second u.weakSecondOrder

/-- Continuity makes the almost-everywhere representative identity an everywhere identity. -/
theorem c1Representative_eq_freeResolvent :
    u.c1Representative.value = freeResolvent 2 (u.freeSource : ℝ → ℂ) := by
  have ha := coeFn_freeResolventOperator (by norm_num : (0 : ℝ) < 2) u.freeSource
  rw [u.freeResolvent_freeSource_eq] at ha
  exact Measure.eq_of_ae_eq (u.c1Representative.value_ae.symm.trans ha)
    u.c1Representative.continuous
    (contDiff_one_freeResolvent_of_memLp (by norm_num) (Lp.memLp u.freeSource)).continuous

theorem c1Representative_eq_freeResolvent_continuousSource :
    u.c1Representative.value = freeResolvent 2 u.continuousSource :=
  u.c1Representative_eq_freeResolvent.trans
    (freeResolvent_congr_ae 2 u.freeSource_ae_continuousSource)

/-- Every actual weak H² Gaussian eigenfunction has a C² representative. -/
theorem c1Representative_contDiff_two : ContDiff ℝ 2 u.c1Representative.value := by
  rw [u.c1Representative_eq_freeResolvent_continuousSource]
  exact contDiff_two_freeResolvent_of_memLp_continuous (by norm_num)
    u.memLp_continuousSource u.continuous_continuousSource

theorem c1Representative_second_deriv : deriv (deriv u.c1Representative.value) =
    fun x => (4 : ℂ) * u.c1Representative.value x - u.continuousSource x := by
  rw [u.c1Representative_eq_freeResolvent_continuousSource,
    deriv_freeResolvent_of_memLp (by norm_num : (0 : ℝ) < 2) u.memLp_continuousSource,
    deriv_freeResolventDeriv_of_memLp_continuous (by norm_num : (0 : ℝ) < 2)
      u.memLp_continuousSource u.continuous_continuousSource]
  norm_num

/-- The actual Gaussian Sturm equation holds at every point for the classical representative. -/
theorem c1Representative_equation (x : ℝ) :
    -deriv (deriv u.c1Representative.value) x +
      (4 - (Wlog x : ℂ)) * u.c1Representative.value x =
        (eigenvalue : ℂ) * u.c1Representative.value x := by
  rw [u.c1Representative_second_deriv]
  simp only [continuousSource]
  ring

/-- An arbitrary genuine weak Gaussian eigenfunction gives a classical one. -/
def classicalRepresentative : ClassicalGaussianSturmEigenfunction eigenvalue where
  value := u.c1Representative.value
  contDiff := u.c1Representative_contDiff_two
  memLp := u.c1Representative.memLp
  deriv_memLp := u.c1Representative.deriv_memLp
  nonzero := u.c1Representative.exists_value_ne_zero u.nonzero
  equation := u.c1Representative_equation

theorem classicalRepresentative_value_ae :
    (u.value : ℝ → ℂ) =ᵐ[volume] u.classicalRepresentative.value :=
  u.c1Representative.value_ae

theorem classicalRepresentative_derivative_ae :
    (u.first : ℝ → ℂ) =ᵐ[volume] deriv u.classicalRepresentative.value :=
  u.c1Representative.derivative_ae

/-- The second weak derivative also agrees with the actual classical one. -/
theorem classicalRepresentative_second_derivative_ae :
    (u.second : ℝ → ℂ) =ᵐ[volume] deriv (deriv u.classicalRepresentative.value) := by
  filter_upwards [u.equation_ae, u.c1Representative.value_ae] with x hw hu
  rw [hu] at hw
  have hc := u.c1Representative_equation x
  change u.second x = deriv (deriv u.c1Representative.value) x
  linear_combination hc - hw

theorem classicalRepresentative_second_memLp :
    MemLp (deriv (deriv u.classicalRepresentative.value)) 2 volume :=
  (Lp.memLp u.second).ae_eq u.classicalRepresentative_second_derivative_ae

end GaussianSturmEigenfunction

/-- The actual weak H² Gaussian Sturm operator has no nonzero neutral eigenfunction. -/
theorem not_nonempty_gaussianSturmEigenfunction_zero :
    ¬ Nonempty (GaussianSturmEigenfunction 0) := by
  rintro ⟨u⟩
  have hz : u.c1Representative.value = 0 := by
    apply gaussian_complex_neutral_mode_two_eq_zero u.c1Representative_contDiff_two
      u.c1Representative.memLp u.c1Representative.deriv_memLp
    intro x
    simpa only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_ofNat,
      Complex.ofReal_zero, zero_mul] using u.c1Representative_equation x
  obtain ⟨x, hx⟩ := u.c1Representative.exists_value_ne_zero u.nonzero
  exact hx (congrFun hz x)

theorem GaussianSturmEigenfunction.eigenvalue_ne_zero {eigenvalue : ℝ}
    (u : GaussianSturmEigenfunction eigenvalue) : eigenvalue ≠ 0 := by
  intro h
  subst eigenvalue
  exact not_nonempty_gaussianSturmEigenfunction_zero ⟨u⟩

end UnforcedLeray.Sturm
