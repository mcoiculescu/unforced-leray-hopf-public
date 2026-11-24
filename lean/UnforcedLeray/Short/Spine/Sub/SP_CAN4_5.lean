import UnforcedLeray.Short.Spine.Sub.SP_CAN4

/-!
# Spine: `SmoothRepresentativeEquation` cut into its leaf statements (task `Spine:SP-CAN/4/5`)

Target (`Short/Spine/Sub/SP_CAN4.lean`): `SmoothRepresentativeEquation`. For a strong solution `V`
that is `C^∞` into every `X_{G,j}` and a jointly smooth representative `W`, the `X_G` equation
`-V' = L₀ V + θ⁻¹ D V` becomes the pointwise equation
`-∂_θ W(θ, r) = generatorL0 (W θ) r + θ⁻¹ oscillatorD (W θ) r` for all `θ, r > 0`.

Source of record: `the November 2 reference manuscript`, line 1086; the classical
formulas `L₀ = -2iΩ + 2ikR` (`eq:st18-t00006`) and `D = Δ + ½ y·∇ + 2` (`eq:st18-t00011`) in the old
manuscript `paper/main.tex` 1879-1888 (read only).

## The cut

* `PartialDerivAe`: the `X_G`-derivative `V'(θ)` is `xGMeasure`-a.e. the pointwise `∂_θ W(θ, ·)`
  (`L²` convergent difference quotients have an a.e. convergent subsequence, while the quotients
  of `W` converge at every `r`).
* `L0ClassicalAe`: `L₀` acts on a continuous representative by `generatorL0`, a.e., and
  `generatorL0 g` is continuous on `(0, ∞)`.
* `DClassicalAe` (the crux): for `u ∈ 𝒟(D)` with a `C^∞` representative `g` on `(0, ∞)`,
  `D u = oscillatorD g` a.e. (test-function argument with the symmetry of `D`).
* `AeEqOfContinuousOn`: two functions continuous on `(0, ∞)` and a.e. equal for `xGMeasure` agree
  at every `r > 0`.
* `SmoothnessFacts`: elementary smoothness facts about a jointly smooth `W`.

`smoothRepresentativeEquation_of` is the assembly.

Status: nothing of the identification is proved here except the assembly; the crux
`DClassicalAe` is not in the library. No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 1, the `X_G`-derivative is the pointwise `θ`-derivative** (a.e. in `r`). Proof: for
`h → 0` the difference quotients `(V(θ+h) - V θ)/h` converge in `L²(xGMeasure)` to `V'(θ)` and are
a.e. equal to `(W(θ+h, ·) - W(θ, ·))/h` (`Lp.coeFn_sub`, `Lp.coeFn_smul`, `W θ =ᵐ V θ`); along
`h = 1/m` extract an a.e.-convergent subsequence
(`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`); the quotients of `W` converge at every
`r > 0` to `deriv (fun t => W t r) θ` (joint smoothness gives differentiability in `t`). -/
def PartialDerivAe : Prop :=
  ∀ V : ℝ → XG, IsStrongOnPos V →
    ∀ W : ℝ → Profile, (∀ θ : ℝ, 0 < θ → W θ =ᵐ[xGMeasure] (V θ : ℝ → ℂ)) →
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0) →
      ∀ θ : ℝ, 0 < θ →
        (fun r : ℝ => deriv (fun t => W t r) θ) =ᵐ[xGMeasure] (⇑(deriv V θ) : ℝ → ℂ)

/-- **Leaf 2, `L₀` acts by `generatorL0`** (shorter proof line 1086; `eq:st18-t00006`). For a
continuous (on `(0, ∞)`) representative `g` of `f ∈ X_G`: `L₀ f =ᵐ generatorL0 g`, and
`generatorL0 g` is continuous on `(0, ∞)`. Proof: `Cons.G3b.generatorL0_eq_L0Fun`,
`B0012.coeFn_L0` (`L₀ f =ᵐ L0Fun f`), `B0012.L0Fun_congr`; continuity from `B0012.continuousOn_R f`
and `B0012.R_congr` (`R g r = R f r` for `r > 0`) and the smoothness of `Ω`, `k` on `(0, ∞)`
(`vortexOmega_eq`, `strainK_eq`). -/
def L0ClassicalAe : Prop :=
  ∀ (f : XG) (g : Profile), g =ᵐ[xGMeasure] (f : ℝ → ℂ) → ContinuousOn g (Ioi 0) →
    (⇑(B0012.L0 f) : ℝ → ℂ) =ᵐ[xGMeasure] generatorL0 g ∧ ContinuousOn (generatorL0 g) (Ioi 0)

/-- **Leaf 3 (the crux), `D` acts by `oscillatorD`** (`eq:st18-t00011`; as in
`PlanarSpectral.exists_modeVort_Ddomain_action`): if `u ∈ 𝒟(D)` has a representative `g` that is
`C^∞` on `(0, ∞)`, then `oscillatorD g =ᵐ D u` for `xGMeasure`.

Proof (test functions; LARGE, expect a further cut). For `ψ` smooth with compact support in
`(0, ∞)`: (i) `toLp ψ ∈ 𝒟(D)` and `D (toLp ψ) =ᵐ oscillatorD ψ` (polar identity
`B0093.gaussianOperator (angularTwoField ψ) = angularTwoField (oscillatorD ψ)` with
`PlanarSpectral.exists_Ddomain_of_gaussClass_profile_ae`, `ψ` is Gaussian class since it has compact
support away from `0`); (ii) symmetry `⟪D x, y⟫ = ⟪x, D y⟫` on `𝒟(D)` (`B0094.isSelfAdjoint_D`);
(iii) weighted integration by parts `∫ (oscillatorD ψ̄) g w = ∫ ψ̄ (oscillatorD g) w`,
`w = r e^{r²/4}` (no boundary terms, `oscillatorD = w⁻¹ (w f')' - 4 f/r² + 2 f`); (iv) hence
`∫ ψ (oscillatorD g - D u) w = 0` for all such `ψ`, and the fundamental lemma on `(0, ∞)` for the
`L²_loc` function `oscillatorD g - D u` gives the a.e. identity (Mathlib's
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` needs a version for test functions supported in
`Ioi 0`; note `D u` is only in `L²`, not continuous, so the fundamental lemma must be stated for
`MemLp _ 2 xGMeasure`, not for continuous functions). -/
def DClassicalAe : Prop :=
  ∀ (u : XG) (hu : u ∈ B0094.D.domain) (g : Profile), g =ᵐ[xGMeasure] (u : ℝ → ℂ) →
    ContDiffOn ℝ ∞ g (Ioi 0) →
      oscillatorD g =ᵐ[xGMeasure] (⇑(B0094.D ⟨u, hu⟩) : ℝ → ℂ)

/-- **Leaf 4, a.e. equality of continuous functions is equality on `(0, ∞)`.** `xGMeasure` is
`volume.restrict (Ioi 0)` with a positive density (`B0012.restrict_ac`, `B0012.xG_ac`), so
`volume.restrict (Ioi 0)`-a.e. equality of functions continuous on the open set `Ioi 0` is
pointwise equality (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). -/
def AeEqOfContinuousOn : Prop :=
  ∀ f g : ℝ → ℂ, ContinuousOn f (Ioi 0) → ContinuousOn g (Ioi 0) → f =ᵐ[xGMeasure] g →
    ∀ r : ℝ, 0 < r → f r = g r

/-- **Leaf 5, elementary smoothness facts** for a jointly smooth `W` on `(0, ∞)²`: the slices
`W θ` are `C^∞` on `(0, ∞)` (compose with `t ↦ (θ, t)`), the partial derivative
`r ↦ deriv (fun t => W t r) θ` is continuous on `(0, ∞)` (it is the directional derivative
`fderiv _ (θ, r) (1, 0)` of a `C^∞` map), and `oscillatorD g` is continuous on `(0, ∞)` for
`g` `C^∞` there (`deriv`, `deriv (deriv g)` are continuous on the open set). -/
def SmoothnessFacts : Prop :=
  (∀ W : ℝ → Profile, ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0) →
    (∀ θ : ℝ, 0 < θ → ContDiffOn ℝ ∞ (W θ) (Ioi 0)) ∧
    (∀ θ : ℝ, 0 < θ → ContinuousOn (fun r : ℝ => deriv (fun t => W t r) θ) (Ioi 0))) ∧
  (∀ g : Profile, ContDiffOn ℝ ∞ g (Ioi 0) → ContinuousOn (oscillatorD g) (Ioi 0))

/-- **`SmoothRepresentativeEquation` from the five leaf statements.** The `X_G` equation
`-V' = L₀V + θ⁻¹DV` holds in `L²(xGMeasure)`; by the leaves each term is a.e. the corresponding
pointwise expression; both sides are continuous in `r` on `(0, ∞)`, so they agree there. -/
theorem smoothRepresentativeEquation_of (h1 : PartialDerivAe) (h2 : L0ClassicalAe)
    (h3 : DClassicalAe) (h4 : AeEqOfContinuousOn) (h5 : SmoothnessFacts) :
    SmoothRepresentativeEquation := by
  intro V hs hsm W hWV hWsm θ hθ r hr
  obtain ⟨hslice, hdcont⟩ := h5.1 W hWsm
  obtain ⟨hD, hderiv⟩ := hs θ hθ
  have hdv : deriv V θ =
      -(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩) := hderiv.deriv
  have hae1 := h1 V hs W hWV hWsm θ hθ
  obtain ⟨hL0ae, hL0cont⟩ := h2 (V θ) (W θ) (hWV θ hθ) (hslice θ hθ).continuousOn
  have hDae := h3 (V θ) hD (W θ) (hWV θ hθ) (hslice θ hθ)
  have key : (fun s : ℝ => -deriv (fun t => W t s) θ) =ᵐ[xGMeasure]
      (fun s : ℝ => generatorL0 (W θ) s + (θ : ℂ)⁻¹ * oscillatorD (W θ) s) := by
    have e1 := Lp.coeFn_neg (B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩)
    have e2 := Lp.coeFn_add (B0012.L0 (V θ)) (((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩)
    have e3 := Lp.coeFn_smul ((θ : ℂ)⁻¹) (B0094.D ⟨V θ, hD⟩)
    rw [← hdv] at e1
    filter_upwards [hae1, e1, e2, e3, hL0ae, hDae] with s s1 s2 s3 s4 s5 s6
    have t1 : deriv (fun t => W t s) θ = (⇑(deriv V θ) : ℝ → ℂ) s := s1
    have t2 : (⇑(deriv V θ) : ℝ → ℂ) s =
        -((⇑(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s) := s2
    have t3 : (⇑(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s =
        (⇑(B0012.L0 (V θ)) : ℝ → ℂ) s +
          (⇑(((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s := s3
    have t4 : (⇑(((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s =
        (θ : ℂ)⁻¹ * (⇑(B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s := s4.trans (by simp)
    have t5 : (⇑(B0012.L0 (V θ)) : ℝ → ℂ) s = generatorL0 (W θ) s := s5
    have t6 : oscillatorD (W θ) s = (⇑(B0094.D ⟨V θ, hD⟩) : ℝ → ℂ) s := s6
    rw [t1, t2, t3, t4, t5, ← t6]
    ring
  exact h4 _ _ (hdcont θ hθ).neg
    ((hL0cont.add (continuousOn_const.mul (h5.2 (W θ) (hslice θ hθ))))) key r hr

end UnforcedLeray.Short.Spine
