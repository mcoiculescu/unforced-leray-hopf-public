import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1

/-!
# `PartII-a:N01/9/1/3` (decomposition): `SmoothForceGradBound`

Source `the November 2 reference manuscript`
lines 1684-1689 (energy inequality `(Re μ+1/4)‖b‖² + ν‖∇b‖² ≤ ‖h‖‖b‖`), 3541-3552.

Route: apply the energy inequality (`SmoothEnergyIneq`) to the difference of the two smooth forces
(`g₁ - g₂ ∈ SmoothForceSet`), with the difference energy field `(b₁ - b₂, G₁ - G₂)`
(`EnergyFieldSub`), which represents `R₀(g₁ - g₂)` a.e. (linearity of `R₀`, `VelFAeTransfer`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (tnorm2)

/-- **Sub-leaf**: the energy class is a vector space (difference of two energy fields).  Source
3426-3430.  `energyLoc` by `|x - y|² ≤ 2|x|² + 2|y|²`; `zeroEntrance` with the smaller `δ`;
`divFreeAE`, `weakGradAE` for a.e. age: the slices of `b_i` and `G_i` are integrable on the cell for
a.e. `s` (from `energyLoc`, a countable union of intervals `[1/n, n]`), so the tested identities
subtract (`HasWeakCellDerivC` is linear in integrable data). -/
def EnergyFieldSub : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (b₁ b₂ : Chart → Fin 2 → ℂ) (G₁ G₂ : Chart → Fin 2 → Fin 2 → ℂ),
    IsEnergyFieldAE c b₁ G₁ → IsEnergyFieldAE c b₂ G₂ →
      IsEnergyFieldAE c (fun p i => b₁ p i - b₂ p i) (fun p i j => G₁ p i j - G₂ p i j)

/-- **Sub-leaf, bridge**: an a.e. equality of profile fields for the `𝓗`-measure `measureH c`
transfers through the recentring chart map to an a.e. equality of the transported fields for
`ageμ c (-3/2)` (the pull-back along `Masked.cellPtInv c` of `measureH c`-null sets is
`ageμ c (-3/2)`-null; see `PartIIIb.NearInst.Masked.CellPtInvH`). -/
def VelFAeTransfer : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f f' : Profile → MeridC, f =ᵐ[measureH c] f' →
    velF c f =ᵐ[ageμ c (-3 / 2)] velF c f'

/-- **Sub-leaf, the energy inequality** (1684-1689: pair the classical equation for `b = R₀(μ)g`,
`g` a smooth force, with `s^{-1/2} b̄`; integrate by parts in `s` (compact `s`-support, zero
entrance) and in the periodic cell (η-decay): `(Re μ+1/4)‖b‖²_𝓗 + ν‖∇b‖²_𝒯 ≤ ‖g‖_𝓗‖b‖_𝓗`,
and `‖b‖_𝓗 ≤ (Re μ+1/4)⁻¹‖g‖_𝓗` by `B0225.norm_R0_le`; the weak gradient of an energy field is
a.e. unique, so the bound holds for every gradient representative `G`).  `C` depends on `c,ν,μ`
only. -/
def SmoothEnergyIneq : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ C : ℝ, ∀ g ∈ SmoothForceSet c,
      ∀ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) →
        IsEnergyFieldAE c b G →
        ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) ≤ ENNReal.ofReal (C * ‖g‖ ^ 2)

/-- Smooth forces form an additive group (difference of smooth periodic compactly supported
fields; `solenoidalHC 0 c` is a submodule). -/
theorem smoothForceSet_sub (c : ℝ) {g₁ g₂ : HSpace c MeridC} (h₁ : g₁ ∈ SmoothForceSet c)
    (h₂ : g₂ ∈ SmoothForceSet c) : g₁ - g₂ ∈ SmoothForceSet c := by
  obtain ⟨hs₁, F₁, ⟨hF₁, hp₁, s₁, s₂, R, hs, hsupp₁⟩, hae₁⟩ := h₁
  obtain ⟨hs₂, F₂, ⟨hF₂, hp₂, t₁, t₂, R', ht, hsupp₂⟩, hae₂⟩ := h₂
  refine ⟨Submodule.sub_mem _ hs₁ hs₂, fun p => F₁ p - F₂ p,
    ⟨hF₁.sub hF₂, fun p => by simp [hp₁, hp₂], min s₁ t₁, max s₂ t₂, max R R',
      lt_min hs ht, fun p hp => ?_⟩, ?_⟩
  · have h1 : F₁ p = 0 := by
      apply hsupp₁
      rcases hp with hp | hp | hp
      · left; exact lt_of_lt_of_le hp (min_le_left _ _)
      · right; left; exact lt_of_le_of_lt (le_max_left _ _) hp
      · right; right; exact lt_of_le_of_lt (le_max_left _ _) hp
    have h2 : F₂ p = 0 := by
      apply hsupp₂
      rcases hp with hp | hp | hp
      · left; exact lt_of_lt_of_le hp (min_le_right _ _)
      · right; left; exact lt_of_le_of_lt (le_max_right _ _) hp
      · right; right; exact lt_of_le_of_lt (le_max_right _ _) hp
    simp [h1, h2]
  · exact (Lp.coeFn_sub g₁ g₂).trans (hae₁.sub hae₂)

theorem smoothForceGradBound_of (h1 : EnergyFieldSub) (h2 : VelFAeTransfer)
    (h3 : SmoothEnergyIneq) : SmoothForceGradBound := by
  intro c ν hc hν μ hμ
  obtain ⟨C, hC⟩ := h3 c ν hc hν μ hμ
  refine ⟨C, fun g₁ hg₁ g₂ hg₂ b₁ b₂ G₁ G₂ hb₁ hE₁ hb₂ hE₂ => ?_⟩
  have hg : g₁ - g₂ ∈ SmoothForceSet c := smoothForceSet_sub c hg₁ hg₂
  have hR : (UnforcedLeray.B0225.R0 hc ν μ (g₁ - g₂) : HSpace c MeridC)
      = UnforcedLeray.B0225.R0 hc ν μ g₁ - UnforcedLeray.B0225.R0 hc ν μ g₂ := by
    rw [map_sub]
  have hcoe : velF c ((UnforcedLeray.B0225.R0 hc ν μ (g₁ - g₂) : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[ageμ c (-3 / 2)] fun x i =>
        velF c (UnforcedLeray.B0225.R0 hc ν μ g₁ : HSpace c MeridC) x i
          - velF c (UnforcedLeray.B0225.R0 hc ν μ g₂ : HSpace c MeridC) x i := by
    have h0 : ((UnforcedLeray.B0225.R0 hc ν μ (g₁ - g₂) : HSpace c MeridC) : Profile → MeridC)
        =ᵐ[measureH c] fun p => (UnforcedLeray.B0225.R0 hc ν μ g₁ : HSpace c MeridC) p
          - (UnforcedLeray.B0225.R0 hc ν μ g₂ : HSpace c MeridC) p := by
      rw [hR]; exact Lp.coeFn_sub _ _
    have h := h2 c hc _ _ h0
    refine h.trans (Filter.Eventually.of_forall fun x => ?_)
    funext i
    simp [velF]
  have hb : (fun p i => b₁ p i - b₂ p i) =ᵐ[ageμ c (-3 / 2)]
      velF c (UnforcedLeray.B0225.R0 hc ν μ (g₁ - g₂) : HSpace c MeridC) := by
    filter_upwards [hb₁, hb₂, hcoe] with x e1 e2 e3
    rw [e3]; funext i
    rw [e1, e2]
  have := hC (g₁ - g₂) hg _ _ hb (h1 c hc b₁ b₂ G₁ G₂ hE₁ hE₂)
  have hn : ‖g₁ - g₂‖ = ‖g₁ - g₂‖ := rfl
  exact this

end UnforcedLeray.Short.PartIIa.N01
