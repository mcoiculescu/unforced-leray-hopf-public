import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.TestModeFourier

/-!
# Part III-a, task `PartIII-a:T20/4/2`: mode `k` of the divergence identity

Proves `CTE.ModeDiv` (statement in `Sub/T20_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3240 (`div K_c ω = 0`).

Proof. For `k = 0` both multipliers vanish. For `k ≠ 0`, move to the Fourier side
(`Lp.inner_fourier_eq`, `L2.inner_def`): `𝓕 (modes (ψ e_j))_k = (𝓕 z) e_j` (`testModeFourier`),
`𝓕 (bsModeCLM c k g) = 𝓕 g • bsSymbol c k` and `𝓕 (etaModeCLM c k g) = 𝓕 g • etaSymbol c k`; the
integrand is `conj(𝓕 z) 𝓕 g (iκ bsSym₀ + 2πξ i bsSym₁) = 0` (`bsSym_div_identity`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ContDiff Real

namespace UnforcedLeray.Short.IIIa

namespace CTE

theorem modeDiv : ModeDiv := by
  intro c hc k ψ hψ g
  by_cases hk : k = 0
  · subst hk
    rw [qModeCLM_zero, B0583.etaModeCLM_zero]
    simp
  · obtain ⟨z, -, hF⟩ := testModeFourier c k hψ
    have hbs := B0581.fourier_bsModeCLM c hk g
    have het := B0583.fourier_etaModeCLM c hk g
    have hκ := B0581.kappa_ne_zero hc.out hk
    rw [B0583.qModeCLM_apply, inner_smul_right, ← Lp.inner_fourier_eq,
      ← Lp.inner_fourier_eq ((B0581.modes c (B0583.testLp c hψ 1) : B0581.ModeSeq B0581.Vel) k),
      L2.inner_def, L2.inner_def, ← integral_const_mul,
      ← integral_add ((L2.integrable_inner (𝕜 := ℂ) _ _).const_mul _)
        (L2.integrable_inner (𝕜 := ℂ) _ _)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hF 0, hF 1, hbs, het] with ξ h0 h1 h2 h3
    have hD : B0581.kappa c k ^ 2 + (2 * π * ξ) ^ 2 ≠ 0 := by positivity
    have hdiv := bsSym_div_identity hD
    simp only [Pi.zero_apply]
    rw [h0, h1, h2, h3, B0583.etaSymbol, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right, EuclideanSpace.inner_single_left, inner_smul_right,
      EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, B0581.bsSymbol]
    linear_combination ((starRingEnd ℂ) (((𝓕 z : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) *
      ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) * hdiv

end CTE

end UnforcedLeray.Short.IIIa
