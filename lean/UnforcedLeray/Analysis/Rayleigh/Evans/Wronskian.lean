import NonUniqueEuler.P.Infra.ODE.Existence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual Wronskian variation for two different coefficients

This is an exact identity for genuine ODE solutions. The zero endpoint
hypothesis in the final lemma is an intermediate neutral-eigenfunction
hypothesis, not an assertion that a Gaussian neutral or unstable zero exists.
-/

noncomputable section
open Set
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

variable {V₁ V₂ f f' g g' : ℝ → ℂ}

/-- Differentiating the actual Wronskian cancels the first-derivative terms. -/
theorem hasDerivAt_wronskian_distinct
    (hf : IsSolOn V₁ univ f f') (hg : IsSolOn V₂ univ g g') (t : ℝ) :
    HasDerivAt (wronskian f f' g g')
      ((V₂ t - V₁ t) * f t * g t) t := by
  obtain ⟨hf₁, hf₂⟩ := isSolOn_univ_iff.mp hf
  obtain ⟨hg₁, hg₂⟩ := isSolOn_univ_iff.mp hg
  have h := ((hf₁ t).mul (hg₂ t)).sub ((hf₂ t).mul (hg₁ t))
  convert h using 1 <;> first | rfl | ring

/-- The integral identity follows from the actual derivative and continuity. -/
theorem integral_wronskian_variation
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂)
    (hf : IsSolOn V₁ univ f f') (hg : IsSolOn V₂ univ g g') (a b : ℝ) :
    (∫ t in a..b, (V₂ t - V₁ t) * f t * g t) =
      wronskian f f' g g' b - wronskian f f' g g' a := by
  have hfc : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hgc : Continuous g := continuousOn_univ.mp hg.continuousOn
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_wronskian_distinct hf hg t
  · exact (((hV₂.sub hV₁).mul hfc).mul hgc).intervalIntegrable a b

/-- With both left values zero and a neutral right value zero, the endpoint
value of the second solution equals the exact integrated perturbation. -/
theorem endpoint_wronskian_variation
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂)
    (hf : IsSolOn V₁ univ f f') (hg : IsSolOn V₂ univ g g')
    {a b : ℝ} (hfa : f a = 0) (hga : g a = 0) (hfb : f b = 0) :
    g b * f' b = -(∫ t in a..b, (V₂ t - V₁ t) * f t * g t) := by
  have h := integral_wronskian_variation hV₁ hV₂ hf hg a b
  simp only [wronskian, hfa, hga, hfb, zero_mul, mul_zero, sub_zero, zero_sub] at h
  rw [h]
  ring

end UnforcedLeray.Rayleigh.Evans
