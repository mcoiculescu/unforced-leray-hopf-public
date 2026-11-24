import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2

/-!
# `PartII-a:N01/9/2/3` (decomposition): `WeakProjectionInvisible`

Source `the November 2 reference manuscript`
lines 1669-1676.  With `ζ = s^{1/2}Φ(s)`:
(Z1) `ζ ∈ solenoidalHC 0 c` (integration by parts in `(q,η)` per fixed `s`, `div Φ(s) = 0`);
(Z2) `⟪ζ, f⟫_𝓗 = ∬ (f/s)·Φ` for every `f ∈ 𝓗` (weight `s^{-3/2}`, transport by `cellPtInv`);
(Z3) `G/s = div₀ M` on the recentred chart (periodicity of `M`).
The assembly `weakProjectionInvisible_of` is proved here from `⟪ζ, G - P₀G⟫ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- The meridional field `ζ = s^{1/2}Φ(s)` on the profile cell (`Φ` is `c`-periodic in `q`). -/
def zetaFn (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : Profile → MeridC := fun p =>
  (Real.sqrt p.1 : ℂ) • !₂[((Φ p.1 p.2 0 : ℝ) : ℂ), ((Φ p.1 p.2 1 : ℝ) : ℂ)]

/-- **Z1** (1669-1676): `s^{1/2}Φ` is an element of `𝓗` lying in `solenoidalHC 0 c`.
Sketch: `ζ ∈ L²(measureH)` since `Φ` is bounded with support in `s ∈ [s₁,s₂] ⊂ (0,∞)`, `|η| ≤ R`
and the cell is `q`-bounded.  For `ΨT : ProfileTest c` with `cgrad 0 ΨT ∈ L²`, the pairing
`⟪toLp(cgrad 0 ΨT), ζ⟫ = ∬ (∂_qΨ Φ_r + ∂_ηΨ Φ_z) s^{-1} ds dq dη`, and for fixed `s` the inner
integral vanishes by `div Φ(s) = 0`, periodicity in `q` and compact `η`-support (integration by
parts, Fubini on the cell; no `s`-derivative). -/
def ZetaMemSolenoidal : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ Φ, IsFlatTest c Φ →
    ∃ ζ ∈ solenoidalHC 0 c, (ζ : Profile → MeridC) =ᵐ[measureH c] zetaFn Φ

/-- **Z2** (1669-1676, weights): for `ζ = s^{1/2}Φ` in `𝓗` and every `f ∈ 𝓗`,
`⟪ζ, f⟫_𝓗 = ∬_{(0,∞) × cell} Σᵢ (f_i(cellPtInv x)/s) Φ_i(x) dx`, the integrand being integrable
(Cauchy-Schwarz, `f,ζ ∈ L²(s^{-3/2})`; `s^{-3/2}·s^{1/2} = s^{-1}`; push the measure by `cellPtInv`,
which is the translation `q ↦ q + c` on `q ≤ 0`). -/
def InnerZetaUnwind : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ Φ, IsFlatTest c Φ → ∀ ζ : HSpace c MeridC,
    (ζ : Profile → MeridC) =ᵐ[measureH c] zetaFn Φ → ∀ f : HSpace c MeridC,
      IntegrableOn (fun p : Chart => ∑ i : Fin 2,
          (velF c (f : Profile → MeridC) p i / (p.1 : ℂ)) * (Φ p.1 p.2 i : ℂ))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      inner ℂ ζ f = ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ∑ i : Fin 2,
          (velF c (f : Profile → MeridC) p i / (p.1 : ℂ)) * (Φ p.1 p.2 i : ℂ)

/-- **Z3**: if `G = s div₀ M` `measureH`-a.e. then `velF G / s = div₀ M` a.e. on
`(0,∞) × cell` (recentred chart): transport the a.e. statement by `cellPtInv`, and use
`c`-periodicity of `M` (`IsTensorTest.periodic`) for `div₀ M (cellPtInv x) = div₀ M x`. -/
def DivEpsRecentre : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ G : HSpace c MeridC,
    (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∀ᵐ p : Chart ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)), ∀ i : Fin 2,
        velF c (G : Profile → MeridC) p i / (p.1 : ℂ) = divEps 0 M p i

theorem weakProjectionInvisible_of (h1 : ZetaMemSolenoidal) (h2 : InnerZetaUnwind)
    (h3 : DivEpsRecentre) : WeakProjectionInvisible := by
  intro c ν hc _ μ _ M hM G hG Φ hΦ
  obtain ⟨ζ, hζK, hζ⟩ := h1 c hc Φ hΦ
  have hz : inner ℂ ζ (G - PepsC 0 c G) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hζK
      (Submodule.sub_starProjection_mem_orthogonal G)
  obtain ⟨iG, eG⟩ := h2 c hc Φ hΦ ζ hζ G
  obtain ⟨iP, eP⟩ := h2 c hc Φ hΦ ζ hζ (PepsC 0 c G)
  rw [inner_sub_right, eG, eP, sub_eq_zero] at hz
  have h3' := h3 c hc M hM G hG
  have hae : ∀ᵐ p : Chart ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)),
      (∑ i : Fin 2, (divEps 0 M p i - velF c (PepsC 0 c G : Profile → MeridC) p i / (p.1 : ℂ)) *
              (Φ p.1 p.2 i : ℂ)) =
        (∑ i : Fin 2, (velF c (G : Profile → MeridC) p i / (p.1 : ℂ)) * (Φ p.1 p.2 i : ℂ)) -
        ∑ i : Fin 2, (velF c (PepsC 0 c G : Profile → MeridC) p i / (p.1 : ℂ)) *
          (Φ p.1 p.2 i : ℂ) := by
    filter_upwards [h3'] with p hp
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp i]; ring
  refine ⟨(iG.sub iP).congr (hae.mono fun p hp => hp.symm), ?_⟩
  rw [integral_congr_ae hae, integral_sub iG iP, hz, sub_self]

end UnforcedLeray.Short.PartIIa.N01
