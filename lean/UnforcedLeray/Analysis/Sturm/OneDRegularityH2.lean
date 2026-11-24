import UnforcedLeray.Analysis.Sturm.OneDRegularityWeakUniqueness
import UnforcedLeray.Analysis.Sturm.OneDRegularityWeakGraph
import UnforcedLeray.Analysis.Sturm.EigenfunctionRegularity

/-!
# Classical C¹ representatives of arbitrary one-dimensional H² data

Actual weak free uniqueness identifies every L² function with L² weak second
derivative as a Green integral. Its checked classical representative then
identifies the given first weak derivative by distributional uniqueness.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

/-- Every genuine weak H² function is recovered by the actual Green operator. -/
theorem weakH2_eq_freeResolvent {L : ℝ} (hL : 0 < L) (u ddu : ComplexL2)
    (hu : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ)) :
    freeResolventOperator hL ((L : ℂ) ^ 2 • u - ddu) = u := by
  let f : ComplexL2 := (L : ℂ) ^ 2 • u - ddu
  have hd := hasWeakDerivOn_L2_sub hu (freeResolventOperator_weak_two hL f)
  have heq : ddu - freeResolventSecondOperator hL f =
      (L : ℂ) ^ 2 • (u - freeResolventOperator hL f) := by
    change ddu - ((L : ℂ) ^ 2 • freeResolventOperator hL f -
      ((L : ℂ) ^ 2 • u - ddu)) = _
    rw [smul_sub]
    abel
  rw [heq] at hd
  have hz := eq_zero_of_weakFree hL (u - freeResolventOperator hL f) hd
  exact (sub_eq_zero.mp hz).symm

/-- The actual derivative Green operator recovers the given weak derivative. -/
theorem weakH2_derivative_eq_freeResolventDerivative {L : ℝ} (hL : 0 < L)
    (u du ddu : ComplexL2)
    (h1 : HasWeakDerivOn univ (derivList 1) (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ (derivList 1) (du : ℝ → ℂ) (ddu : ℝ → ℂ)) :
    freeResolventDerivativeOperator hL ((L : ℂ) ^ 2 • u - ddu) = du := by
  have hu2 : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ) := h1.trans h2
  have heq := weakH2_eq_freeResolvent hL u ddu hu2
  have hr := freeResolventOperator_weak_one hL ((L : ℂ) ^ 2 • u - ddu)
  rw [heq] at hr
  exact weakDerivative_L2_unique hr h1

/-- Genuine one-dimensional H²-to-C¹ representation, without an assumed
Sobolev embedding or an assumed pointwise trace. -/
def weakH2C1Representative (u du ddu : ComplexL2)
    (h1 : HasWeakDerivOn univ (derivList 1) (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ (derivList 1) (du : ℝ → ℂ) (ddu : ℝ → ℂ)) :
    C1L2Representative u du := by
  have hu2 : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ) := h1.trans h2
  have heq := weakH2_eq_freeResolvent (by norm_num : 0 < (2 : ℝ)) u ddu hu2
  have hd := weakH2_derivative_eq_freeResolventDerivative
    (by norm_num : 0 < (2 : ℝ)) u du ddu h1 h2
  have hrep := freeResolventC1Representative (by norm_num : 0 < (2 : ℝ))
    (((2 : ℝ) : ℂ) ^ 2 • u - ddu)
  rw [heq, hd] at hrep
  exact hrep

/-- Every actual weak Gaussian Sturm eigenfunction has a classical C¹ representative. -/
def GaussianSturmEigenfunction.c1Representative {eigenvalue : ℝ}
    (u : GaussianSturmEigenfunction eigenvalue) : C1L2Representative u.value u.first :=
  weakH2C1Representative u.value u.first u.second u.weakFirst u.weakSecond

end UnforcedLeray.Sturm
