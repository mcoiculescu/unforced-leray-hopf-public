import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1

/-!
# `PartII-a:N01/9/1/2` (decomposition): `SmoothForceFields`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383 (`R₀(μ)M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ`),
3426-3430.  For a smooth, compactly `s`-supported, solenoidal force `g = F` a.e., `R₀(μ)g` is the
classical causal heat integral `smoothHeatInt`; this is a field of the energy class.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (vnorm2)

/-- The classical causal heat integral `∫₀^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} (F/σ)(σ) dσ` (3379-3383) for
the force `F = s g'` (`R₀(μ)M_s g'`, `M_s g' = s g' = F`), so the integrand carries `g' = F/s`. -/
def smoothHeatInt (c ν : ℝ) (μ : ℂ) (F : Profile → MeridC) : Profile → MeridC := fun p =>
  ∫ σ in (0 : ℝ)..p.1, ((σ / p.1 : ℝ) : ℂ) ^ μ •
    UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
      (fun z => UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)) p.2

/-- **(L1)** For a smooth compactly `s`-supported force `g = F` a.e., `R₀(μ)g` is the classical
heat integral a.e. (`B0225.R0_Ms_ae` applied to `g/s ∈ H_g`, smooth and supported in
`[s₁,s₂] ⊂ (0,∞)`, so `M_s(g/s) = g`; lines 3379-3383). -/
def SmoothForceRepr : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ g ∈ SmoothForceSet c, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
      (g : Profile → MeridC) =ᵐ[measureH c] F →
        (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) =ᵐ[measureH c] smoothHeatInt c ν μ F

/-- **(L2)** Null sets of the profile measure `measureH` transfer to null sets of the age measure
`ageμ c (-3/2)` through `velF` (the chart `Chart → Fin 2 → ℂ` is the cell chart of the profile
space with the normalised cell measure; both measures are `s^{-3/2}ds ⊗` Lebesgue on the cell). -/
def VelFAeCongr : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u v : Profile → MeridC, u =ᵐ[measureH c] v →
    velF c u =ᵐ[ageμ c (-3 / 2)] velF c v

/-- **(L3)** `zeroEntrance` for `R₀(μ)g`: `R₀(μ)g ∈ 𝓗` (`B0225.norm_R0_le`), i.e. finite
`L²(s^{-3/2})` energy of `velF` near age `0` (lines 1684-1689, 3426-3430). -/
def R0Entrance : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ g : HSpace c MeridC, ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ p, ENNReal.ofReal (vnorm2 (velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤

/-- **(L4)** Classical energy class of the heat integral (lines 1650-1658, 1684-1689): for a smooth
compactly `s`-supported solenoidal force the heat integral is smooth in `s>0`, `(q,η)`; it is
measurable, locally of finite energy (continuity on compacts), has weak cell gradient and zero cell
divergence at every age (`planeHeat` commutes with the cell divergence and periodicity; `F(σ,·)` is
solenoidal for every `σ` by continuity from `g ∈ solenoidalHC 0 c`).  `zeroEntrance` is supplied as
hypothesis. -/
def HeatIntEnergy : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ g ∈ SmoothForceSet c, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
      (g : Profile → MeridC) =ᵐ[measureH c] F →
      (∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (velF c (smoothHeatInt c ν μ F) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤) →
      ∃ Gr : Chart → Fin 2 → Fin 2 → ℂ, IsEnergyFieldAE c (velF c (smoothHeatInt c ν μ F)) Gr

theorem smoothForceFields_of (h1 : SmoothForceRepr) (h2 : VelFAeCongr) (h3 : R0Entrance)
    (h4 : HeatIntEnergy) : SmoothForceFields := by
  intro c ν hc hν μ hμ g hg
  obtain ⟨hs, F, hF, hgF⟩ := hg
  have hrep := h1 c ν hc hν μ hμ g ⟨hs, F, hF, hgF⟩ F hF hgF
  have hcongr := h2 c hc _ _ hrep
  obtain ⟨δ, hδ, hint⟩ := h3 c ν hc hν μ hμ (g : HSpace c MeridC)
  obtain ⟨Gr, hGr⟩ := h4 c ν hc hν μ hμ g ⟨hs, F, hF, hgF⟩ F hF hgF ⟨δ, hδ, by
    have hae : ∀ᵐ p ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)),
        velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) p
          = velF c (smoothHeatInt c ν μ F) p := ae_restrict_of_ae hcongr
    have : ∫⁻ p, ENNReal.ofReal (vnorm2 (velF c (smoothHeatInt c ν μ F) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) =
        ∫⁻ p, ENNReal.ofReal (vnorm2 (velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) :=
      lintegral_congr_ae (hae.mono fun p hp => by simp only [hp])
    rw [this]; exact hint⟩
  exact ⟨velF c (smoothHeatInt c ν μ F), Gr, hcongr.symm, hGr⟩

end UnforcedLeray.Short.PartIIa.N01
