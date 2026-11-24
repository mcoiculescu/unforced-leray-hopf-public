import UnforcedLeray.Analysis.Sturm.OneDRegularityH2

/-!
# Classical representatives of the actual annular H² limit

The compactness theorem identifies first and second distributional derivatives
of the same function. Testing the first derivative identity against a derivative
of a compact smooth test function proves that the first derivative has the given
second derivative. The established one-dimensional H² regularity theorem then
supplies a C¹ representative, and every continuous representative agrees with it
everywhere.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

/-- First and second weak derivatives of one function form the actual successive
weak derivative chain. All identities use the original compact smooth tests. -/
theorem hasWeakDerivOn_first_of_second {V : Set ℝ} {u g j : ℝ → ℂ}
    (h1 : HasWeakDerivOn V [1] u g)
    (h2 : HasWeakDerivOn V [1, 1] u j) :
    HasWeakDerivOn V [1] g j := by
  intro ψ hψ
  have hfirst : (∫ t, u t * iterDirDeriv [1, 1] ψ t) =
      -(∫ t, g t * iterDirDeriv [1] ψ t) := by
    simpa only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_cons,
      List.length_nil, zero_add, pow_one, neg_one_mul] using
      h1 (iterDirDeriv [1] ψ) (hψ.iterDirDeriv [1])
  have hsecond : (∫ t, u t * iterDirDeriv [1, 1] ψ t) = ∫ t, j t * ψ t := by
    simpa using h2 ψ hψ
  have hresult : (∫ t, g t * iterDirDeriv [1] ψ t) = -(∫ t, j t * ψ t) := by
    calc
      _ = -(-(∫ t, g t * iterDirDeriv [1] ψ t)) := (neg_neg _).symm
      _ = _ := congrArg Neg.neg (hfirst.symm.trans hsecond)
  simpa using hresult

/-- A genuine C¹ representative from the first/second weak derivative data
returned by annular compactness, without an assumed successive derivative. -/
def weakH2RepresentativeOfSecond (u g j : ComplexL2)
    (h1 : HasWeakDerivOn univ [1] (u : ℝ → ℂ) (g : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ) (j : ℝ → ℂ)) :
    C1L2Representative u g :=
  weakH2C1Representative u g j h1 (hasWeakDerivOn_first_of_second h1 h2)

/-- The continuous local-uniform limit is the classical representative itself,
not merely another almost-everywhere equivalent function. -/
theorem continuous_eq_weakH2RepresentativeOfSecond (u g j : ComplexL2)
    (h1 : HasWeakDerivOn univ [1] (u : ℝ → ℂ) (g : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ) (j : ℝ → ℂ))
    {f : ℝ → ℂ} (hf : Continuous f) (hae : f =ᵐ[volume] (u : ℝ → ℂ)) :
    f = (weakH2RepresentativeOfSecond u g j h1 h2).value :=
  Measure.eq_of_ae_eq (hae.trans (weakH2RepresentativeOfSecond u g j h1 h2).value_ae)
    hf (weakH2RepresentativeOfSecond u g j h1 h2).continuous

/-- The actual continuous annular limit is C¹, with its classical derivative
representing exactly the extracted first-derivative L² class. -/
theorem continuous_weakH2_contDiff (u g j : ComplexL2)
    (h1 : HasWeakDerivOn univ [1] (u : ℝ → ℂ) (g : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ) (j : ℝ → ℂ))
    {f : ℝ → ℂ} (hf : Continuous f) (hae : f =ᵐ[volume] (u : ℝ → ℂ)) :
    ContDiff ℝ 1 f ∧ (g : ℝ → ℂ) =ᵐ[volume] deriv f := by
  rw [continuous_eq_weakH2RepresentativeOfSecond u g j h1 h2 hf hae]
  exact ⟨(weakH2RepresentativeOfSecond u g j h1 h2).contDiff,
    (weakH2RepresentativeOfSecond u g j h1 h2).derivative_ae⟩

end UnforcedLeray.Rayleigh
