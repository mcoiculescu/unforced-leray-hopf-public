import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4

/-!
# `PartII-a:N01/9/1/3/3/2` (decomposition): `SmoothClassicalEnergyBound`

Source `the November 2 reference manuscript`
lines 1684-1689, 3541-3552.  By `SmoothForceRepr`/`VelFAeCongr` the field `R₀(μ)g` is a.e. the
classical heat integral `smoothHeatInt`; `HeatIntEnergy` makes it an energy field.  What remains
is the classical energy bound for `smoothHeatInt` with its classical gradient (`ClassicalGradBound`)
and that any weak gradient of the energy field is the classical gradient a.e. (`WeakGradIsClassical`).
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
open UnforcedLeray.Short.IIIa (tnorm2 vnorm2)

/-- **(E1)** Classical energy bound (lines 1684-1689, 3541-3552).  For a smooth force `F` with
`g = F` a.e., `u = smoothHeatInt c ν μ F` is a classical solution of
`s ∂_s u + μ u - ν s Δ_{q,η} u = F` for `s > 0` (`∂_s(s^μ u) = νΔ(s^μ u) + s^{μ-1}F`, differentiate
the Duhamel formula), vanishing for `s < s₁`, `c`-periodic.  Pairing with `s^{-3/2} ū` and
integrating over `(0,∞) × cell` (integration by parts in `s`: `Re ∫ s^{-1/2}∂_s|u|²/2 = -¼∫s^{-3/2}|u|²`
up to boundary terms that vanish at `s → 0` (vanishing near `0`) and along a sequence `s → ∞`
(finite weighted energy); in the cell: periodicity in `q`, decay in `η`) gives
`(Re μ+1/4)‖u‖²_𝓗 + ν ∫|∇u|² s^{-1/2} ≤ ‖g‖_𝓗 ‖u‖_𝓗` with `‖u‖_𝓗 ≤ (Re μ+1/4)⁻¹‖g‖_𝓗`
(`B0225.norm_R0_le`, `R0 g =ᵐ u`); the factor `c` between the unnormalised `measureH` and the
normalised `ageμ` is absorbed in `C = C(c,ν,μ)`. -/
def ClassicalGradBound : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ C : ℝ, ∀ g ∈ SmoothForceSet c, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
      (g : Profile → MeridC) =ᵐ[measureH c] F →
      ∫⁻ p, ENNReal.ofReal
          (tnorm2 (gradOf (velF c (smoothHeatInt c ν μ F)) p) ^ 2) ∂(ageμ c (-1 / 2))
        ≤ ENNReal.ofReal (C * ‖g‖ ^ 2)

/-- **(E2)** Any weak gradient of the energy field `velF c (smoothHeatInt c ν μ F)` is the classical
gradient `gradOf` a.e. (`ageμ c (-1/2)`): by Fubini, for a.e. age `s>0` the slice
`y ↦ u(s,y) i` is `C¹`, `c`-periodic, so its classical derivative is a weak derivative
(`PeriodicWeakDeriv`, `HeatIntRegular`) and weak derivatives are a.e. unique
(fundamental lemma on the cylinder; cf. `EnergyGradUnique`).  Source lines 3426-3430. -/
def WeakGradIsClassical : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ Gr : Chart → Fin 2 → Fin 2 → ℂ, IsEnergyFieldAE c (velF c (smoothHeatInt c ν μ F)) Gr →
      Gr =ᵐ[ageμ c (-1 / 2)] gradOf (velF c (smoothHeatInt c ν μ F))

theorem smoothClassicalEnergyBound_of (h1 : SmoothForceRepr) (h2 : VelFAeCongr)
    (h3 : R0Entrance) (h4 : HeatIntEnergy) (h5 : ClassicalGradBound) (h6 : WeakGradIsClassical) :
    SmoothClassicalEnergyBound := by
  intro c ν hc hν μ hμ
  obtain ⟨C, hC⟩ := h5 c ν hc hν μ hμ
  refine ⟨C, fun g hg => ?_⟩
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
  refine ⟨velF c (smoothHeatInt c ν μ F), Gr, hcongr.symm, hGr, ?_⟩
  have hG := h6 c ν hc hν μ F hF Gr hGr
  calc ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2))
      = ∫⁻ p, ENNReal.ofReal (tnorm2 (gradOf (velF c (smoothHeatInt c ν μ F)) p) ^ 2)
          ∂(ageμ c (-1 / 2)) :=
        lintegral_congr_ae (hG.mono fun p hp => by simp only [hp])
    _ ≤ _ := hC g ⟨hs, F, hF, hgF⟩ F hF hgF

end UnforcedLeray.Short.PartIIa.N01
