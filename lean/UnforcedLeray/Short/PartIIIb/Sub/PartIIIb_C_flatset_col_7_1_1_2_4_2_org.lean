import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_of
import UnforcedLeray.Units.B0225

/-!
# Concrete Duhamel / heat-gradient statements behind `SFCEnergyG`
(organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/org`)

Source `the November 2 reference manuscript` 1650-1656 (`T₀ = R₀ P₀`, flat equation),
1684-1689 (energy class, coercive pairing), 3426-3430 (`∇b ∈ L²_loc((0,∞);L²)`); Duhamel formula
`B0225.R0_Ms_ae_causalHeat`: `R₀(μ) M_s f = causalHeat c ν μ f` ae.

For the classical context, `T₀flat f' = R₀ (P₀ f')` for every `f' : HSpace c MeridC` lifting `g`
(`NearInst.IsBodyTransport`).  Writing `P₀ f' = PepsC 0 c f'` and `M_s h = s h`, the representative `b`
is the Duhamel integral of `Gp := s⁻¹ P₀ f'`.  This file only *states* the four facts; the energy
finiteness `SFCEnergyG` follows from them by Minkowski's inequality on the cell.

`P₀ f'` is an `L²` class, so pointwise regularity is stated for a representative `Gs` equal to
`sfcGp hc f'` a.e. (`SFCProjGrad`, organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/org`).
The heat `e^{θΔ}`, `θ > 0`, only sees the a.e. class of its datum, so `SFCDuhamel` and
`SFCDuhamelGrad` are stated with `sfcGp` itself; `SFCDuhamelGradRep` is the form of `SFCDuhamelGrad`
with the datum replaced by any such `Gs` (proved from `SFCDuhamelGrad` in
`Sub/PartIII-b_C_flatset_col_7_1_1_2_4_2_proj2/DuhamelGradRep.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- The flat-projected force divided by the age: `Gp σ,x = σ⁻¹ (P₀ f')(σ,x)`, the datum `g` of
`B0225.R0_Ms_ae_causalHeat` for `R₀(M_s g) = R₀ P₀ f'`. -/
def sfcGp {c : ℝ} (hc : 0 < c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC :=
  fun p => ((p.1 : ℝ) : ℂ)⁻¹ • (UnforcedLeray.Short.PartIIa.PepsC 0 c f' :
    UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p

/-- `f'` lifts `g` to the complex profile space (the lift used by `NearInst.IsBodyTransport`). -/
def SFCLift {c : ℝ} (g : Hsp c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    Prop :=
  (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (g (NearInst.cellPt c p)))

/-- **Duhamel representation** (source 1650-1656, 1684-1689, `B0225.R0_Ms_ae_causalHeat`): in the
classical context the representative `b` is, ae, the causal cylinder heat of `Gp = s⁻¹ P₀ f'`
for a lift `f'` of `g`, componentwise. -/
def SFCDuhamel : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∃ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' ∧
        ∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i : Fin 2,
          b p i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i

/-- **Heat contracts the cell gradient** (source 3426-3430, Gaussian average): for a smooth
bounded `q`-periodic `f` (`P₀` data is not compactly supported in `η`), `‖∇ e^{θΔ} f‖_{L²(cell)} ≤ ‖∇ f‖_{L²(cell)}`, `θ ≥ 0`. -/
def SFCHeatGrad : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 ≤ θ → ∀ f : ℝ × ℝ → ℂ, ContDiff ℝ ∞ f →
    (∀ q η, f (q + c, η) = f (q, η)) → (∃ C : ℝ, ∀ x : ℝ × ℝ, ‖f x‖ ≤ C) →
      ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (UnforcedLeray.B0224.planeHeat θ f) x
          (B0579.dir j) * (if i = 0 then 1 else 0)) ^ 2)
        ≤ ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ f x (B0579.dir j) * (if i = 0 then 1 else 0)) ^ 2)

/-- **Smooth representative of the flat-projected force, with locally bounded gradient** (source
1650-1656, 1676: `P₀` is the planar cylinder Leray projection, acting on each age slice, a Fourier
multiplier of order zero commuting with `∂_q, ∂_η`; 1684-1689: `g` smooth with compact support in
`s ≥ s₀ > 0`; 3426-3430: `∇b ∈ L²_loc((0,∞);L²)`).  `P₀ f'` is an `L²` class, so the statement is
about a representative: for the lift `f'` of an `IsSmoothForce`, there is `Gs` equal
`measureH`-a.e. to the Duhamel datum `sfcGp hc f' = σ⁻¹ P₀ f'`, vanishing for `σ < s₀` (support of
`g`), whose slices `Gs(σ, ·)` are, for a.e. `σ ∈ (0, s₂]`, `C^∞`, `q`-periodic and bounded, with
cell-gradient energy `∫_{[-c/2,c/2) × ℝ} |∇ Gs(σ)|²` bounded uniformly in `σ`. -/
def SFCProjGrad : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      ∃ Gs : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
        Gs =ᵐ[UnforcedLeray.B0220.measureH c] sfcGp hc f' ∧
        (∃ s₀ : ℝ, 0 < s₀ ∧ ∀ p : UnforcedLeray.B0220.Profile, p.1 < s₀ → Gs p = 0) ∧
        ∀ s₂ : ℝ, 0 < s₂ → ∃ C : ℝ,
          ∀ᵐ σ ∂(volume.restrict (Ioc 0 s₂)),
            (∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => (Gs (σ, y)) i) ∧
            (∀ q η, Gs (σ, (q + c, η)) = Gs (σ, (q, η))) ∧
            (∃ C' : ℝ, ∀ y : ℝ × ℝ, ‖Gs (σ, y)‖ ≤ C') ∧
            ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
              ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ
                (fun y : ℝ × ℝ => (Gs (σ, y)) i) x (B0579.dir j)) ^ 2)
              ≤ ENNReal.ofReal C

/-- **Gradient of the Duhamel integral** (source 3426-3430): `∇b(s)` is the Duhamel integral of the
gradients, `cellGrad b (s,x) i j = ∫₀^s (σ/s)^μ ∂_j (e^{ν(s-σ)Δ} Gp(σ))_i (x) dσ`, for `s > 0`
(differentiation under the integral; `Gp` smooth, supported in `σ ≥ s₀ > 0`). -/
def SFCDuhamelGrad : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
        (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i : Fin 2,
          b p i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i) →
        ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, ∀ i j : Fin 2,
          cellGrad b (s, x) i j =
            ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) *
              fderiv ℝ (fun y : ℝ × ℝ =>
                (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
                  (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) y) i) x
                (B0579.dir j)

/-- **Gradient of the Duhamel integral, representative form** (source 3426-3430): as
`SFCDuhamelGrad`, with the datum `sfcGp hc f'` of the heat replaced by any `Gs` equal to it
`measureH`-a.e. (for `σ < s` the heat `e^{ν(s-σ)Δ}` is a Gaussian average, which depends only on the
a.e. class of the slice; e.g. `Gs` the smooth representative of `SFCProjGrad`). -/
def SFCDuhamelGradRep : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
        (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i : Fin 2,
          b p i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i) →
        ∀ Gs : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
          Gs =ᵐ[UnforcedLeray.B0220.measureH c] sfcGp hc f' →
        ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, ∀ i j : Fin 2,
          cellGrad b (s, x) i j =
            ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) *
              fderiv ℝ (fun y : ℝ × ℝ =>
                (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
                  (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) y) i) x
                (B0579.dir j)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
