import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Analysis.Fourier.LpSpace
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Part III-a, task `PartIII-a:T20/3` helper: the `L²` Fourier transform of an `L¹ ∩ L²` function

Helper for `T20_3_NonzeroVelUniform.lean` (`CTE.NonzeroVelUniform`, source
`the November 2 reference manuscript`, lines 3236-3240). Mathlib has the
`L²` Fourier transform `Lp.fourierTransformₗᵢ` (`MeasureTheory.Lp`), but no lemma identifying it
with the integral Fourier transform `𝓕 g` for `g ∈ L¹ ∩ L²`. This file proves that identification
(`fourier_toLp_ae_eq`): both sides define the same tempered distribution, and a.e. equality follows
from equality against all compactly supported smooth real test functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

/-- Self-adjointness of the Fourier transform against a Schwartz function, for `g ∈ L¹(ℝ)`. -/
theorem integral_fourier_mul_schwartz (g : ℝ → ℂ) (hg1 : Integrable g) (φ : 𝓢(ℝ, ℂ)) :
    ∫ ξ, 𝓕 g ξ • φ ξ = ∫ x, g x • 𝓕 φ x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hg1 φ.integrable

/-- **Bridge.** For `g ∈ L¹(ℝ) ∩ L²(ℝ)`, the `L²` Fourier transform of `g` agrees a.e. with the
integral Fourier transform `𝓕 g`. -/
theorem fourier_toLp_ae_eq (g : ℝ → ℂ) (hg1 : Integrable g) (hg2 : MemLp g 2) :
    ((𝓕 (hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕 g := by
  set G : Lp ℂ 2 (volume : Measure ℝ) := hg2.toLp g with hGdef
  have hGg : (G : ℝ → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have key : ∀ φ : 𝓢(ℝ, ℂ), ∫ x, φ x • ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
      ∫ x, φ x • 𝓕 g x := by
    intro φ
    have h1 : ∫ x, φ x • ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
        (Lp.toTemperedDistribution (𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) φ := by
      rw [Lp.toTemperedDistribution_apply]
    rw [h1, ← Lp.fourier_toTemperedDistribution_eq G, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply]
    have h2 : ∫ x, (𝓕 φ) x • (G : ℝ → ℂ) x = ∫ x, (𝓕 φ) x • g x := by
      apply integral_congr_ae
      filter_upwards [hGg] with x hx
      rw [hx]
    rw [h2]
    have h3 := integral_fourier_mul_schwartz g hg1 φ
    calc ∫ x, (𝓕 φ) x • g x = ∫ x, g x • 𝓕 φ x := by
          congr 1; funext x; simp only [smul_eq_mul]; ring
      _ = ∫ ξ, 𝓕 g ξ • φ ξ := h3.symm
      _ = ∫ ξ, φ ξ • 𝓕 g ξ := by
          congr 1; funext ξ; simp only [smul_eq_mul]; ring
  have hH : LocallyIntegrable (fun x => ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
      volume :=
    (Lp.memLp _).locallyIntegrable one_le_two
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg1
  have hFl : LocallyIntegrable (𝓕 g) volume := hFc.locallyIntegrable
  have hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - 𝓕 g x) = 0 := by
    intro ψ hψ hψc
    have hc₁ : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hψc.comp_left rfl
    have hc₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) :=
      Complex.ofRealCLM.contDiff.comp hψ
    have k := key (hc₁.toSchwartzMap hc₂)
    have hφ : ∀ x, (hc₁.toSchwartzMap hc₂) x = (ψ x : ℂ) := fun x => rfl
    have hint1 : Integrable (fun x => ψ x • ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
        volume :=
      LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hH hψ.continuous hψc
    have hint2 : Integrable (fun x => ψ x • 𝓕 g x) volume :=
      LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hFl hψ.continuous hψc
    have hsplit : ∫ x, ψ x • (((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - 𝓕 g x) =
        (∫ x, ψ x • ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) - ∫ x, ψ x • 𝓕 g x := by
      simp only [smul_sub]
      exact integral_sub hint1 hint2
    rw [hsplit]
    refine sub_eq_zero.mpr ?_
    simp only [hφ, smul_eq_mul, Complex.real_smul] at k ⊢
    exact k
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hH.sub hFl) hzero
  filter_upwards [hae] with x hx
  have hx' : ((𝓕 G : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - 𝓕 g x = 0 := hx
  exact sub_eq_zero.mp hx'

end UnforcedLeray.Short.IIIa.CTE.T20_3
