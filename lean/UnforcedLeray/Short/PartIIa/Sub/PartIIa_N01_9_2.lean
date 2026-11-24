import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1

/-!
# `PartII-a:N01/9/2` (decomposition): `BodyColumnWeakC`

Source of record `the November 2 reference manuscript`
lines 1650-1658 (`A₀`), 1669-1674 (`T₀ = (μ - A₀)⁻¹P₀ = R₀(μ)P₀`), 1684-1689 (flat equation
`(∂_s + μ/s - νΔ)b = P₀ div₀ M`).

Route.  (W1) for a smooth force `g`, `b = R₀(μ)g` is classical and solves `(∂_s + μ/s - νΔ)b = g/s`
pointwise, so the tested identity holds by integration by parts.  (W2) the identity passes to every
`g ∈ 𝓗` (density of smooth forces, `B0225.norm_R0_le`, the energy bound of `N01/9/1`, and the
compact `s`-support of the flat test).  (W3) `P₀` is the orthogonal projection onto
`solenoidalHC 0 c` and `s^{1/2}Φ(s)` lies in it, so `⟨(P₀G - G)/s, Φ⟩ = 0`.  `bodyColumnWeakC_of` is
the (proved) assembly; the energy class is supplied by `BodyColumnEnergyC` (`N01/9/1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (IsEnergyFieldAE forcedIntegrand)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- **Leaf W1**: for a smooth force `F` and `g ∈ 𝓗` represented by `F`, every energy-class
representative `b` of `velF (R₀(μ) g)` solves `(∂_s + μ/s - νΔ)b = F/s` weakly against every
divergence-free flat test (`B0225.R0_Ms_ae`: `b(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ}F(σ)dσ` is classical;
integrate by parts in `s` and on the cell). -/
def WeakSmoothForce : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ F : Profile → MeridC, IsSmoothForceFn c F →
      ∀ g : HSpace c MeridC, (g : Profile → MeridC) =ᵐ[measureH c] F →
        ∀ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
          b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) →
          IsEnergyFieldAE c b Gr → ∀ Φ, IsFlatTest c Φ →
            IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0)
                (fun x i => velF c F x i / (x.1 : ℂ)) b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
              ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
                forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => velF c F x i / (x.1 : ℂ)) b Φ p = 0

/-- **Leaf W2**: the tested identity holds for the body column `R₀(μ)g` of every solenoidal `g ∈ 𝓗`
(approximate `g` by smooth forces `g_k` in `𝓗`; `R₀ g_k → R₀ g` in `𝓗` by `norm_R0_le`, the
gradients converge in `𝒯` by the energy inequality (`N01/9/1` leaves `SmoothForceGradBound`,
`EnergyClosure`), and the flat test has compact support in `s ∈ (0,∞)`, so every term of the tested
equation, including `⟨g_k/s, Φ⟩ → ⟨g/s, Φ⟩`, is continuous; use `WeakSmoothForce`). -/
def WeakAllForces : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ g ∈ solenoidalHC 0 c, ∀ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
      b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) →
      IsEnergyFieldAE c b Gr → ∀ Φ, IsFlatTest c Φ →
        IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0)
            (fun x i => velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) b Φ)
          (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
            forcedIntegrand ν μ (fun _ _ _ => 0)
              (fun x i => velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) b Φ p = 0

/-- **Leaf W3, the flat Leray projection is invisible to divergence-free tests** (1669-1676):
`PepsC 0 c` is the orthogonal projection onto `solenoidalHC 0 c`, and `ζ = s^{1/2}Φ(s)` lies in
that subspace (`div Φ(s) = 0`, `Φ` smooth with compact support in `s`, `ζ ∈ 𝓗` since the weight is
bounded on the support), so `⟨G - P₀G, ζ⟩_𝓗 = 0`, i.e. (weight `s^{-3/2}`, `ζ = s^{1/2}Φ`)
`∬ ((P₀G)/s - G/s)·Φ = 0`, with `G/s = div₀ M` a.e. -/
def WeakProjectionInvisible : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∀ Φ, IsFlatTest c Φ →
        IntegrableOn (fun p : Chart => ∑ i : Fin 2,
            (divEps 0 M p i - velF c (PepsC 0 c G : Profile → MeridC) p i / (p.1 : ℂ)) *
              (Φ p.1 p.2 i : ℂ)) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ∑ i : Fin 2,
            (divEps 0 M p i - velF c (PepsC 0 c G : Profile → MeridC) p i / (p.1 : ℂ)) *
              (Φ p.1 p.2 i : ℂ) = 0

theorem bodyColumnWeakC_of (hE : BodyColumnEnergyC) (h2 : WeakAllForces)
    (h3 : WeakProjectionInvisible) : BodyColumnWeakC := by
  intro c ν hc hν μ hμ M hM G hG Φ hΦ
  obtain ⟨b₁, G₁, hb₁, hE₁⟩ := hE c ν hc hν μ hμ M hM G hG
  have hT : T0flat hc ν μ G = UnforcedLeray.B0225.R0 hc ν μ (PepsC 0 c G) := rfl
  rw [hT] at hb₁ ⊢
  obtain ⟨hi2, hz2⟩ := h2 c ν hc hν μ hμ (PepsC 0 c G) (Submodule.starProjection_apply_mem _ _) b₁ G₁ hb₁ hE₁ Φ hΦ
  obtain ⟨hi3, hz3⟩ := h3 c ν hc hν μ hμ M hM G hG Φ hΦ
  have hcongr := n01_forcedIntegrand_congr_ae (c := c) (ν := ν) hc (μ := μ)
    (f := fun x i => velF c (PepsC 0 c G : Profile → MeridC) x i / (x.1 : ℂ)) Φ hb₁
  have hi2' := hi2.congr (n01_forcedIntegrand_congr_ae (c := c) (ν := ν) hc (μ := μ)
    (f := fun x i => velF c (PepsC 0 c G : Profile → MeridC) x i / (x.1 : ℂ)) Φ hb₁)
  have key : ∀ p : Chart,
      forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i)
          (velF c (UnforcedLeray.B0225.R0 hc ν μ (PepsC 0 c G) : Profile → MeridC)) Φ p =
        forcedIntegrand ν μ (fun _ _ _ => 0)
          (fun x i => velF c (PepsC 0 c G : Profile → MeridC) x i / (x.1 : ℂ))
          (velF c (UnforcedLeray.B0225.R0 hc ν μ (PepsC 0 c G) : Profile → MeridC)) Φ p -
        ∑ i : Fin 2, (divEps 0 M p i - velF c (PepsC 0 c G : Profile → MeridC) p i / (p.1 : ℂ)) *
              (Φ p.1 p.2 i : ℂ) := by
    intro p
    simp only [forcedIntegrand, Fin.sum_univ_two]
    ring
  have hz2' : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c (PepsC 0 c G : Profile → MeridC) x i / (x.1 : ℂ))
        (velF c (UnforcedLeray.B0225.R0 hc ν μ (PepsC 0 c G) : Profile → MeridC)) Φ p = 0 := by
    rw [← hz2]
    exact integral_congr_ae hcongr.symm
  refine ⟨(hi2'.sub hi3).congr (Eventually.of_forall fun p => ?_), ?_⟩
  · simp only [Pi.sub_apply]
    exact (key p).symm
  · simp_rw [key]
    rw [integral_sub hi2' hi3, hz2', hz3, sub_zero]

end UnforcedLeray.Short.PartIIa.N01
