import UnforcedLeray.Short.PartIIIa.Sub.T20_3

/-!
# Part III-a, task `PartIII-a:T20/3`: the Plancherel formulas for one mode (`FourierL2Formulas`)

Target: `FourierL2Formulas` (`Sub/T20_3.lean`, the `/7` leaf of `T20/3`), stated here as
`UnforcedLeray.Short.IIIa.CTE.T20_3.fourierL2Formulas`.

Source of record: `the November 2 reference manuscript`, lines 3238-3240
("In Plancherel ..."). For `c > 0`, `k ≠ 0` and `h ∈ L²(ℝ; ℂ)`, with `φ(ξ) = ‖𝓕 h (ξ)‖²`:
`φ` is integrable, `‖h‖² = ∫ φ`, and `‖bsModeCLM c k h‖² = ∫ φ(ξ) / (κ_k² + (2πξ)²)`.

Proof. Helpers live in the namespace `FL2`.
* `FL2.integrable_norm_sq`: for `G ∈ L²(μ; E)`, `x ↦ ‖G x‖²` is integrable
  (`MemLp.integrable_norm_pow`).
* `FL2.norm_sq_eq_integral`: `‖G‖² = ∫ ‖G x‖²` for `E` a complex inner product space
  (`L2.inner_def`, `inner_self_eq_norm_sq_to_K`, `integral_ofReal`).
* `FL2.norm_fourier`: `‖𝓕 h‖ = ‖h‖` (`Lp.fourierTransformₗᵢ` is a linear isometry equivalence).
* `FL2.norm_fourierInv`: the inverse transform on `L²(ℝ; ℂ²)` preserves norms.
* `FL2.bsModeCLM_eq`: for `k ≠ 0`, `bsModeCLM c k h = 𝓕⁻¹ (symMulCLM bsSymbol (𝓕 h))`.

Main theorem. (a) is `FL2.integrable_norm_sq` for `𝓕 h`. (b) is `FL2.norm_fourier` with
`FL2.norm_sq_eq_integral`. (c) reduces to `‖S‖²` for `S = symMulCLM bsSymbol (𝓕 h)`; the helper
gives `‖S‖² = ∫ ‖S x‖²`, `S =ᵐ ξ ↦ 𝓕 h ξ • bsSymbol c k ξ` (`coeFn_symMulCLM`), and
`‖bsSymbol c k ξ‖² = (κ² + (2πξ)²)⁻¹` (`norm_sq_bsSym`, `kappa_ne_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

namespace FL2

/-- For `G ∈ L²(μ; E)`, the function `x ↦ ‖G x‖²` is integrable. -/
theorem integrable_norm_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (G : Lp E 2 μ) :
    Integrable (fun x => ‖(G : α → E) x‖ ^ 2) μ := by
  have hG : MemLp (G : α → E) ((2 : ℕ) : ℝ≥0∞) μ := by
    exact_mod_cast Lp.memLp G
  exact hG.integrable_norm_pow (by norm_num)

/-- For `G ∈ L²(μ; E)` with `E` a complex inner product space: `‖G‖² = ∫ ‖G x‖² dμ`. -/
theorem norm_sq_eq_integral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Lp E 2 μ) :
    ‖G‖ ^ 2 = ∫ x, ‖(G : α → E) x‖ ^ 2 ∂μ := by
  have h1 : ⟪G, G⟫_ℂ = ((‖G‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpt : ∀ x, ⟪(G : α → E) x, (G : α → E) x⟫_ℂ = ((‖(G : α → E) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : ⟪G, G⟫_ℂ = ((∫ x, ‖(G : α → E) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [L2.inner_def]
    exact Eq.trans (integral_congr_ae (Filter.Eventually.of_forall hpt)) integral_ofReal
  exact Complex.ofReal_injective (h1.symm.trans h2)

/-- The inverse `L²` Fourier transform on `L²(ℝ; ℂ²)` is an isometry. -/
theorem norm_fourierInv (X : Lp B0581.Vel 2 (volume : Measure ℝ)) :
    ‖B0581.fourierInvL2 B0581.Vel X‖ = ‖X‖ :=
  (MeasureTheory.Lp.fourierTransformₗᵢ ℝ B0581.Vel).symm.norm_map X

/-- Plancherel: the `L²` Fourier transform on `L²(ℝ; ℂ)` preserves norms. -/
theorem norm_fourier (h : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖(𝓕 h : Lp ℂ 2 (volume : Measure ℝ))‖ = ‖h‖ :=
  (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map h

/-- For `k ≠ 0`, the velocity of the mode `h` is the inverse transform of the Biot–Savart symbol
times `𝓕 h` (`B0581.bsModeCLM`, `B0581.fourierL2_apply`). -/
theorem bsModeCLM_eq (c : ℝ) [hc : Fact (0 < c)] {k : ℤ} (hk : k ≠ 0)
    (h : Lp ℂ 2 (volume : Measure ℝ)) :
    B0581.bsModeCLM c k h = B0581.fourierInvL2 B0581.Vel
      (B0581.symMulCLM (B0581.bsSymbol c k) (B0581.continuous_bsSymbol hc.out hk) (c / (2 * π))
        (B0581.norm_bsSymbol_le' hc.out hk) (𝓕 h)) := by
  simp only [B0581.bsModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, B0581.fourierL2_apply]

end FL2

/-- **Plancherel formulas for one mode** (`FourierL2Formulas`; SP 3238-3240). For `k ≠ 0` and
`h ∈ L²(ℝ; ℂ)`: `φ(ξ) = ‖𝓕 h (ξ)‖²` is integrable, `‖h‖² = ∫ φ`, and
`‖bsModeCLM c k h‖² = ∫ φ(ξ) / (κ_k² + (2πξ)²)`. -/
theorem fourierL2Formulas : FourierL2Formulas := by
  unfold FourierL2Formulas
  intro c hc k hk h
  have hκ : B0581.kappa c k ≠ 0 := B0581.kappa_ne_zero hc.out hk
  refine ⟨FL2.integrable_norm_sq (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)), ?_, ?_⟩
  · calc ‖h‖ ^ 2 = ‖(𝓕 h : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := by rw [FL2.norm_fourier]
      _ = _ := FL2.norm_sq_eq_integral _
  · have hS : ‖B0581.bsModeCLM c k h‖ =
        ‖B0581.symMulCLM (B0581.bsSymbol c k) (B0581.continuous_bsSymbol hc.out hk)
          (c / (2 * π)) (B0581.norm_bsSymbol_le' hc.out hk) (𝓕 h)‖ := by
      rw [FL2.bsModeCLM_eq c hk h, FL2.norm_fourierInv]
    rw [hS]
    refine (FL2.norm_sq_eq_integral _).trans ?_
    refine integral_congr_ae ?_
    filter_upwards [B0581.coeFn_symMulCLM (B0581.bsSymbol c k)
      (B0581.continuous_bsSymbol hc.out hk) (c / (2 * π)) (B0581.norm_bsSymbol_le' hc.out hk)
      (𝓕 h)] with ξ hξ
    have hne : B0581.kappa c k ^ 2 + (2 * π * ξ) ^ 2 ≠ 0 := by positivity
    rw [hξ, norm_smul, mul_pow, B0581.bsSymbol, B0581.norm_sq_bsSym hne, div_eq_mul_inv]

end UnforcedLeray.Short.IIIa.CTE.T20_3
