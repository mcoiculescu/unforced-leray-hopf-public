import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3

/-!
# `PartII-a:N01/9/1/3/3` (decomposition): `SmoothEnergyIneq`

Source `the November 2 reference manuscript`
lines 1684-1689 (pair the flat equation with `s^{-1/2} b̄`), 3541-3552.

Route: (A) the weak gradient of an energy field is a.e. unique, so the bound need only be proved for
one gradient representative; (B) for a smooth force `g` the classical field `b₀ = R₀(μ)g`
(`B0225.R0_Ms_ae`) has a gradient `G₀` for which the energy inequality holds.
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
open UnforcedLeray.Short.IIIa (tnorm2)

/-- **Sub-leaf (A), a.e. uniqueness of the weak gradient** (source 3426-3430, definition of the
energy class).  If two energy fields have a.e. equal velocities (`ageμ c (-3/2)`), their gradients
agree a.e. (`ageμ c (-1/2)`; the measures `ageμ c a` have the same null sets for all `a`).
Route: Fubini gives, for a.e. age `s`, `b(s,·) = b'(s,·)` a.e. on the cell; for a.e. `s` both
`weakGradAE` clauses hold (`HasWeakCellDerivC.congr_ae` transfers the first); then
`∫ (G - G')(s,·) ψ = 0` for all cylinder tests `ψ`, so `G(s,·) = G'(s,·)` a.e. on the cell
(fundamental lemma on the cylinder); Fubini again. -/
def EnergyGradUnique : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (b b' : Chart → Fin 2 → ℂ) (G G' : Chart → Fin 2 → Fin 2 → ℂ),
    IsEnergyFieldAE c b G → IsEnergyFieldAE c b' G' →
      b =ᵐ[ageμ c (-3 / 2)] b' → G =ᵐ[ageμ c (-1 / 2)] G'

/-- **Sub-leaf (B), classical energy inequality** (source 1684-1689, 3541-3552): for a smooth force
`g`, `R₀(μ)g` has an energy-class representative `(b₀, G₀)` (classical: `B0225.R0_Ms_ae`,
`R₀ M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ`, smooth in `(s,q,η)` for `s>0`) whose gradient
satisfies, by pairing the equation with `s^{-1/2} b̄₀` (integration by parts in `s`: compact
`s`-support of `g` and zero entrance; in the cell: η-decay),
`(Re μ+1/4)‖b₀‖²_𝓗 + ν‖G₀‖² ≤ ‖g‖_𝓗‖b₀‖_𝓗`, hence with `‖b₀‖_𝓗 ≤ (Re μ+1/4)⁻¹‖g‖_𝓗`
(`B0225.norm_R0_le`) `ν∫|G₀|² dageμ(-1/2) ≤ K‖g‖²`; `K` depends on `c,ν,μ` only (factor `c` from the
unnormalised `𝓗` measure against the normalised `ageμ`). -/
def SmoothClassicalEnergyBound : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ C : ℝ, ∀ g ∈ SmoothForceSet c,
      ∃ (b₀ : Chart → Fin 2 → ℂ) (G₀ : Chart → Fin 2 → Fin 2 → ℂ),
        b₀ =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) ∧
          IsEnergyFieldAE c b₀ G₀ ∧
          ∫⁻ p, ENNReal.ofReal (tnorm2 (G₀ p) ^ 2) ∂(ageμ c (-1 / 2))
            ≤ ENNReal.ofReal (C * ‖g‖ ^ 2)

theorem smoothEnergyIneq_of (h1 : EnergyGradUnique) (h2 : SmoothClassicalEnergyBound) :
    SmoothEnergyIneq := by
  intro c ν hc hν μ hμ
  obtain ⟨C, hC⟩ := h2 c ν hc hν μ hμ
  refine ⟨C, fun g hg b G hb hE => ?_⟩
  obtain ⟨b₀, G₀, hb₀, hE₀, hle⟩ := hC g hg
  have hG : G =ᵐ[ageμ c (-1 / 2)] G₀ := h1 c hc b b₀ G G₀ hE hE₀ (hb.trans hb₀.symm)
  have : ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2))
      = ∫⁻ p, ENNReal.ofReal (tnorm2 (G₀ p) ^ 2) ∂(ageμ c (-1 / 2)) := by
    apply lintegral_congr_ae
    filter_upwards [hG] with p hp
    rw [hp]
  rw [this]; exact hle

end UnforcedLeray.Short.PartIIa.N01
