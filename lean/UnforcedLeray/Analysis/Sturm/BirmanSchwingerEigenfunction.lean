import UnforcedLeray.Analysis.Sturm.BirmanSchwingerOperator
import UnforcedLeray.Analysis.Sturm.FreeResolventWeak

/-!
# Actual Gaussian Sturm eigenfunctions from the Birman–Schwinger operator

A fixed vector of the concrete compact-operator candidate produces a genuine
L² function with two weak L² derivatives satisfying the Gaussian Sturm
equation. This is the exact differential-operator reduction; no finite matrix
or presumed differential eigenfunction appears in the construction.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

/-- An actual H² weak eigenfunction of `-d²/dt² + 4 - Wlog`. All functions
are ordinary Lebesgue L² classes and the derivatives use smooth compact tests. -/
structure GaussianSturmEigenfunction (eigenvalue : ℝ) where
  value : ComplexL2
  first : ComplexL2
  second : ComplexL2
  nonzero : value ≠ 0
  weakFirst : HasWeakDerivOn univ (derivList 1) (value : ℝ → ℂ) (first : ℝ → ℂ)
  weakSecond : HasWeakDerivOn univ (derivList 1) (first : ℝ → ℂ) (second : ℝ → ℂ)
  equation : -second + (4 : ℂ) • value - complexPotentialOperator value = (eigenvalue : ℂ) • value

namespace GaussianSturmEigenfunction

/-- The fields give the usual second distributional derivative directly. -/
theorem weakSecondOrder {eigenvalue : ℝ} (u : GaussianSturmEigenfunction eigenvalue) :
    HasWeakDerivOn univ (derivList 2) (u.value : ℝ → ℂ) (u.second : ℝ → ℂ) :=
  u.weakFirst.trans u.weakSecond

/-- The operator equation is the concrete Gaussian differential equation a.e. -/
theorem equation_ae {eigenvalue : ℝ} (u : GaussianSturmEigenfunction eigenvalue) :
    ∀ᵐ x, -u.second x + (4 - (GaussianPotential.Wlog x : ℂ)) * u.value x =
      (eigenvalue : ℂ) * u.value x := by
  filter_upwards [Lp.coeFn_neg u.second,
    Lp.coeFn_smul (4 : ℂ) u.value,
    Lp.coeFn_add (-u.second) ((4 : ℂ) • u.value),
    Lp.coeFn_sub (-u.second + (4 : ℂ) • u.value) (complexPotentialOperator u.value),
    Lp.coeFn_smul (eigenvalue : ℂ) u.value,
    coeFn_complexPotentialOperator u.value] with x hn hfour ha hs he hp
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at *
  have hx := congrArg (fun F : ComplexL2 => F x) u.equation
  rw [hs, ha, hn, hfour, hp, he] at hx
  simpa only [sub_mul, add_sub_assoc] using hx

end GaussianSturmEigenfunction

/-- The positive free resolvent transports the actual fixed vector to a
nonzero Gaussian Sturm eigenfunction with spectral value `4-m²`. -/
def gaussianSturmEigenfunctionOfBirmanSchwinger {m : ℝ} (hm : 0 < m)
    (f : ComplexL2) (hf : f ≠ 0) (heigen : birmanSchwingerOperator hm f = f) :
    GaussianSturmEigenfunction (4 - m ^ 2) := by
  let u := freeResolventOperator hm (complexPotentialSqrtOperator f)
  have hSu : complexPotentialSqrtOperator u = f := by
    exact heigen
  have hPu : complexPotentialOperator u = complexPotentialSqrtOperator f := by
    have hsq := congrArg (fun A : ComplexL2 →L[ℂ] ComplexL2 => A u)
      complexPotentialSqrtOperator_comp_self
    change complexPotentialSqrtOperator (complexPotentialSqrtOperator u) =
      complexPotentialOperator u at hsq
    rw [hSu] at hsq
    exact hsq.symm
  have hnonzero : u ≠ 0 := by
    intro hz
    apply hf
    rw [hz, map_zero] at hSu
    exact hSu.symm
  refine
    { value := u
      first := freeResolventDerivativeOperator hm (complexPotentialSqrtOperator f)
      second := freeResolventSecondOperator hm (complexPotentialSqrtOperator f)
      nonzero := hnonzero
      weakFirst := freeResolventOperator_weak_one hm (complexPotentialSqrtOperator f)
      weakSecond := freeResolventDerivativeOperator_weak_one hm (complexPotentialSqrtOperator f)
      equation := ?_ }
  have hsecond : freeResolventSecondOperator hm (complexPotentialSqrtOperator f) =
      (m : ℂ) ^ 2 • u - complexPotentialOperator u := by
    change (m : ℂ) ^ 2 • u - complexPotentialSqrtOperator f = _
    rw [hPu]
  rw [hsecond]
  push_cast
  simp only [sub_smul, neg_sub]
  abel

/-- Exact fixed-vector transport produces a negative differential eigenvalue
when the free mass lies strictly above two. -/
theorem exists_negative_gaussianSturmEigenfunction_of_fixedVector {m : ℝ}
    (hm : 2 < m) (f : ComplexL2) (hf : f ≠ 0)
    (heigen : birmanSchwingerOperator (show 0 < m by linarith) f = f) :
    ∃ eigenvalue : ℝ, eigenvalue < 0 ∧ Nonempty (GaussianSturmEigenfunction eigenvalue) := by
  refine ⟨4 - m ^ 2, by nlinarith, ?_⟩
  exact ⟨gaussianSturmEigenfunctionOfBirmanSchwinger (by linarith) f hf heigen⟩

end UnforcedLeray.Sturm
