import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart.TestModeFourier

/-!
# Part III-a, task `PartIII-a:T20/4/3`: mode `k ≠ 0` of the curl identity

Proves `CTE.ModeCurl` (statement in `Sub/T20_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3240 (`curl K_c ω = ω`).

Proof. By `testModeFourier`, `(modes (ψ e_j))_k = z e_j` with `𝓕 (modes (ψ e_j))_k = (𝓕 z) e_j`.
The right side is `⟪z e₀, g e₀⟫ = ⟪z, g⟫ = ∫ conj(𝓕 z) 𝓕 g` (Plancherel). The left side, on the
Fourier side (`fourier_bsModeCLM`, `fourier_etaModeCLM`), is
`∫ conj(𝓕 z) 𝓕 g (iκ bsSym₁ - 2πξ i bsSym₀)`, and `bsSym_curl_identity` gives the factor `1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ContDiff Real

namespace UnforcedLeray.Short.IIIa

namespace CTE

theorem inner_compLpL_embed0 (a b : Lp ℂ 2 (volume : Measure ℝ)) :
    ⟪ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 a,
      ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 b⟫_ℂ = ⟪a, b⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL embed0 a,
    ContinuousLinearMap.coeFn_compLpL embed0 b] with x h1 h2
  rw [h1, h2, embedJ_apply, embedJ_apply, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left]
  simp
  ring

theorem modeCurl : ModeCurl := by
  intro c hc k hk ψ hψ g
  obtain ⟨z, hphys, hF⟩ := testModeFourier c k hψ
  have hbs := B0581.fourier_bsModeCLM c hk g
  have het := B0583.fourier_etaModeCLM c hk g
  have hκ := B0581.kappa_ne_zero hc.out hk
  have hR : ⟪(B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel) k,
      ContinuousLinearMap.compLpL 2 (volume : Measure ℝ) embed0 g⟫_ℂ =
      ∫ ξ, ⟪((𝓕 z : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ,
        ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ⟫_ℂ := by
    rw [hphys 0, inner_compLpL_embed0, ← Lp.inner_fourier_eq, L2.inner_def]
  rw [hR, B0583.qModeCLM_apply, inner_smul_right, ← Lp.inner_fourier_eq,
    ← Lp.inner_fourier_eq ((B0581.modes c (B0583.testLp c hψ 0) : B0581.ModeSeq B0581.Vel) k),
    L2.inner_def, L2.inner_def, ← integral_const_mul,
    ← integral_sub ((L2.integrable_inner (𝕜 := ℂ) _ _).const_mul _)
      (L2.integrable_inner (𝕜 := ℂ) _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hF 0, hF 1, hbs, het] with ξ h0 h1 h2 h3
  have hD : B0581.kappa c k ^ 2 + (2 * π * ξ) ^ 2 ≠ 0 := by positivity
  have hcurl := bsSym_curl_identity hD
  rw [h0, h1, h2, h3, B0583.etaSymbol, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, EuclideanSpace.inner_single_left, inner_smul_right,
    EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, B0581.bsSymbol, RCLike.inner_apply]
  linear_combination ((starRingEnd ℂ) (((𝓕 z : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) *
    ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) * hcurl

end CTE

end UnforcedLeray.Short.IIIa
