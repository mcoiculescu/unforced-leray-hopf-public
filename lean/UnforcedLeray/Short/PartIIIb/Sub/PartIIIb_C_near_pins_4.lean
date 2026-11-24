import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic

/-!
# `ChartDivPair`, decomposition (task `PartIII-b:C/near/pins/4`)

Source `the November 2 reference manuscript`:
1660-1665 (`div_ε` with the hoop traction), 3893-3897 (`div(√s b)` in the chart), 2683 (lifts
`𝒩_v b = √s b`, `𝒩_T T = sT`), 1640-1641, 2666-2668 (the chart `(τ, y) ↦ (s, q, η)`).

Three leaves:
* `ChartDivPointwise` : the pointwise chart identity (chain rule through `chartOf`, `cylFrame`;
  `∂_ϱ = √s(∂_q - εK)`, `∂_z = √s ∂_η`, `1/ϱ = ε√s`, `K s = 2s`): there is a real chart field `G₀`
  with `merC G₀ = s div_ε M` such that the Cartesian divergence of `strPhys M` is `velPhys G₀` off
  the axis.
* `ChartStressIBP` : integration by parts on the phase cell for a band tensor (compact support away
  from the axis): if `F` is the divergence of `strPhys M` off the axis then
  `⟨Φ, F⟩ = -⟨strPhys M, ∇Φ⟩`.
* `VelPairAE` : the velocity pairing sees only the a.e. class of the chart field (null sets of
  `ageμ c (-3/2)` pull back to null sets of `dτ dy`, as `StressPairAE`).
`chartDivPair_of` assembles `ChartDivPair`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set
open scoped ENNReal

/-- **Pointwise chart divergence identity** (source 1660-1665, 3893-3897, 2683): for a smooth
band tensor `M` there is a real chart field `G₀` with `merC G₀ = s div_ε M` (so `div_ε M` is real)
and `div_y (𝒩_T M)(τ, y) = 𝒩_v G₀ (τ, y)` for every `τ` and every `y` off the axis. -/
def ChartDivPointwise : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ M : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∃ G₀ : Chart → Merid,
      (∀ x : Chart, merC (G₀ x) =
        (x.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun y => tv4 (M y)) x) ∧
      ∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ i : Fin 3,
        ∑ j : Fin 3, dy j (fun x => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ)) (τ, y) =
          velPhys ε⁻¹ c G₀ (τ, y) i

/-- **Integration by parts on the phase cell** (source 1660-1665; `⟨div T, Φ⟩ = -⟨T, ∇Φ⟩`): for a
smooth band tensor `M` (so `y ↦ strPhys M (τ, y)` is smooth with compact support away from the
axis), a field `F` that is the Cartesian divergence of `strPhys M` off the axis pairs with a phase
test as `-⟨strPhys M, ∇Φ⟩`. -/
def ChartStressIBP : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ M : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∀ F : ℝ × Space → CVec3,
      (∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ i : Fin 3,
        ∑ j : Fin 3, dy j (fun x => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ)) (τ, y) = F (τ, y) i) →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
        pairF (2 * ε * c) Φ F = -stressPair (2 * ε * c) (strPhys ε⁻¹ c M) Φ

/-- **The velocity pairing sees only the a.e. class of the chart field** (source 1640-1641,
2666-2668, 2683; same argument as `StressPairAE`, weight `ageμ c (-3/2)`). -/
def VelPairAE : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ (G G' : Chart → Merid), G =ᵐ[ageμ c (-3 / 2)] G' →
    ∀ Φ : ℝ × Space → CVec3,
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c G) = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c G')

theorem merC_injective : Function.Injective merC := by
  intro a b h
  ext i
  have := congrArg (fun v : MeridC => (v i).re) h
  simpa [merC] using this

theorem chartDivPair_of (h1 : ChartDivPointwise) (h2 : ChartStressIBP) (h3 : VelPairAE) :
    ChartDivPair := by
  intro c ε hc hε M hM G hG Φ hΦ
  obtain ⟨G₀, hG₀, hdiv⟩ := h1 c ε hc hε M hM
  have hae : G =ᵐ[ageμ c (-3 / 2)] G₀ := by
    filter_upwards [hG] with x hx
    exact merC_injective (hx.trans (hG₀ x).symm)
  rw [h3 c ε hc hε G G₀ hae Φ]
  exact h2 c ε hc hε M hM (velPhys ε⁻¹ c G₀) hdiv Φ hΦ

end UnforcedLeray.Short.PartIIIb.NearInst
