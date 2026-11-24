import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_9_1
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_1_4

/-!
# Forward uniqueness of the free causal solution (design of `PartIII-b:C/near/delta/9/1/org`)

Source of record `the November 2 reference manuscript`,
3541-3545 ("for uniqueness, a homogeneous difference in the energy class has a sequence
`δ_j ↓ 0` with `δ_j^{-1/2}‖u(δ_j)‖² → 0` ... apply the energy inequality on `[δ_j, B]` ...
This also proves causality"), 3420-3440 (the free equation, `v = 0`, zero entrance `b ∈ 𝓗` near
zero, energy class `∇b ∈ L²_loc`), 3417-3418 (`K ⋐ {0 < Re μ < 1/4}`).

## Why the statement is `FreeForwardUniquenessML`

`FreeForwardUniqueness` (`Sub/PartIII-b_C_near_delta_9_1.lean`) quantifies over an ARBITRARY
source `F`.  It is true (only tests supported in `s < T` matter, and there `F = 0` a.e.), but the
accepted energy identity `IIIa.CoreAll` (`lionsMagenesCyl`, `flatWeakFromDensity`,
`divFreeCutoffDensity`) is stated for `IIIa.FreeSolData`, which needs `F` measurable and
`L²_loc` on all of `(0,∞)` and the weak equation for all tests.  For an arbitrary `F` no such global
datum exists (the truncation `θ(s) b` is not a solution: `θ' b` is not `𝒫₀ div` of an `L²` tensor in
the horizontal-mean mode), so `FreeForwardUniqueness` as stated would need the whole
Lions-Magenes chain localized to the window `(0,T)`.  The consumer only needs the measurable,
locally square integrable source `merBlockC (zsum G)`, `G ∈ Z`, and `μ ∈ Kset ⊂ (0,1/4)` gives
`Re μ > 0`: `FreeForwardUniquenessML` adds these hypotheses, and `zeroEntranceCausal_of_forwardML`
is the consumer (same proof as `zeroEntranceCausal_of_forward`).

## The zero-entrance hypothesis is sufficient

With `Re μ > 0` the energy `E(s) = ∫_cell |b(s)|²` satisfies, for `w ≥ 0` smooth, compactly
supported in `(0,T)`, `2 Re μ ∫ (w/s) E ≤ ∫ w' E` (`CoreIdentity`, `R = 0` on the window).  With
`w = χ_δ η` (`χ_δ` rises on `[δ,2δ]` with `χ_δ' ≤ K/δ`, `η` falls on `[t₁,t₂]`):
`(2 Re μ/t₁) ∫_ε^{t₁} E ≤ (K/δ)∫_δ^{2δ} E ≤ K 2^{3/2} δ^{1/2} ∫_0^{δ₀} s^{-3/2} E → 0`.
The formalized zero entrance (`∫ |b|² d(ageμ c (-3/2))` over `(0,δ₀) × cell` finite) gives
`∫_0^{δ₀} s^{-3/2}E < ∞` (`IIIa.AgeSlice`), which is all that is used: no sequence `δ_j` and no
trace of `b` are needed.

## Proved here

* `fuZeroEntranceSlice_of` (from `IIIa.AgeSlice`);
* `freeForwardUniquenessML_of` (the assembly of the leaves with `CoreAll`, `EnergyLocIntegrable`);
* `zeroEntranceCausal_of_forwardML` (the consumer).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- **Forward energy uniqueness, measurable locally square integrable source** (source
3541-3545, 3420-3440 with `v = 0`): if `b` is a causal zero-entrance energy solution of the free
equation whose source `F` is measurable, `L²_loc` and vanishes a.e. for ages `s < T`, and
`Re μ > 0`, then `b` vanishes a.e. on `(0,T) × cell`. -/
def FreeForwardUniquenessML : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (T : ℝ),
    0 < c → 0 < ν → 0 < μ.re → 0 < T →
    (∀ i j, Measurable fun p => F p i j) → UnforcedLeray.Short.IIIa.L2locTensor c F →
    (∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i j, F p i j = 0) →
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i, b p i = 0

/-! ## The leaves -/

/-- **(1) The source pairing vanishes on the window** (source 3541-3545: on `(0,T)` the difference
solves the homogeneous equation).  If `F = 0` a.e. on `(0,T) × cell`, then
`R(s) = ∫_cell Re⟨F(s), G(s)⟩ = 0` for a.e. `s ∈ (0,T)` (Fubini: `ae_ae_of_ae_prod`). -/
def FUWindowR : Prop :=
  ∀ (c : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (T : ℝ),
    (∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i j, F p i j = 0) →
    ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)), UnforcedLeray.Short.IIIa.energyR c F G s = 0

/-- **(2) The energy identity on the window as an inequality** (source 3541-3545 with the energy
identity of 3520-3524, unweighted): scalar form.  If `E, N ≥ 0`, `E, N, R` are integrable on every
`[s₁,s₂] ⊂ (0,∞)`, `R = 0` a.e. on `(0,T)`, `ν ≥ 0`, and `w ≥ 0` is smooth, compactly supported in
`(0,T)` with `∫ w' E = ∫ w (κ s⁻¹ E + 2νN + 2R)`, then `κ ∫ (w/s) E ≤ ∫ w' E`. -/
def FUCoreWindow : Prop :=
  ∀ (κ ν T : ℝ) (E N R : ℝ → ℝ), 0 ≤ ν → (∀ s, 0 ≤ E s) → (∀ s, 0 ≤ N s) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      IntegrableOn E (Icc s₁ s₂) ∧ IntegrableOn N (Icc s₁ s₂) ∧ IntegrableOn R (Icc s₁ s₂)) →
    (∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)), R s = 0) →
    ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioo 0 T → (∀ s, 0 ≤ w s) →
      (∫ s in Ioi (0 : ℝ), deriv w s * E s) =
          (∫ s in Ioi (0 : ℝ), w s * (κ / s * E s + 2 * ν * N s + 2 * R s)) →
      κ * (∫ s in Ioi (0 : ℝ), w s / s * E s) ≤ ∫ s in Ioi (0 : ℝ), deriv w s * E s

/-- **(3) Zero entrance as a slice integral** (source 3427-3430: `b ∈ 𝓗` near zero): the formalized
zero-entrance clause gives `∫_0^{δ₀} s^{-3/2} E(s) ds < ∞` for some `δ₀ > 0`. -/
def FUZeroEntranceSlice : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), 0 < c →
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∫⁻ s in Ioo 0 δ₀,
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * UnforcedLeray.Short.IIIa.energyE c b s) < ⊤

/-- **(4a) The derivative of the smooth transition** (for the cutoff of source 3541-3545):
`σ = Real.smoothTransition` has `0 ≤ σ' ≤ K` for a fixed `K > 0`, and `σ' = 0` off `[0,1]`
(`σ` is locally constant there: `0` on `(-∞,0]`, `1` on `[1,∞)`). -/
def FUSigmaDeriv : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ deriv Real.smoothTransition x ∧
    deriv Real.smoothTransition x ≤ K ∧ (x < 0 ∨ 1 < x → deriv Real.smoothTransition x = 0)

/-- **(4) Smooth cutoff weights** (the cutoff of source 3541-3545 on `[δ_j, B]`, made smooth): a
fixed `K > 0` such that for `0 < δ`, `2δ < t₁ < t₂` there is a smooth `w ∈ [0,1]` with
`tsupport w ⊆ [δ, t₂]`, `w = 1` on `[2δ, t₁]` and `w' ≤ (K/δ) 1_{[δ,2δ]}` (so `w' ≤ 0` off
`[δ,2δ]`).  Sketch: `w(s) = σ(s/δ - 1) σ((t₂ - s)/(t₂ - t₁))`, `σ = Real.smoothTransition`. -/
def FUWeightFamily : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δ t₁ t₂ : ℝ, 0 < δ → 2 * δ < t₁ → t₁ < t₂ → ∃ w : ℝ → ℝ,
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ tsupport w ⊆ Icc δ t₂ ∧
    (∀ s, 0 ≤ w s ∧ w s ≤ 1) ∧ (∀ s ∈ Icc (2 * δ) t₁, w s = 1) ∧
    ∀ s, deriv w s ≤ K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s

/-- **(5) One weight** (source 3541-3545): for a weight `w` as in `FUWeightFamily` and the
inequality `κ ∫ (w/s) E ≤ ∫ w' E`, `(κ/t₁) ∫_ε^{t₁} E ≤ (K/δ) ∫_δ^{2δ} E` (`2δ ≤ ε < t₁`). -/
def FUOneWeight : Prop :=
  ∀ (κ K δ ε t₁ t₂ : ℝ) (E w : ℝ → ℝ), 0 < κ → 0 < δ → 2 * δ ≤ ε → ε < t₁ → t₁ < t₂ →
    (∀ s, 0 ≤ E s) → (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → IntegrableOn E (Icc s₁ s₂)) →
    ContDiff ℝ ∞ w → tsupport w ⊆ Icc δ t₂ → (∀ s, 0 ≤ w s ∧ w s ≤ 1) →
    (∀ s ∈ Icc (2 * δ) t₁, w s = 1) →
    (∀ s, deriv w s ≤ K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s) →
    κ * (∫ s in Ioi (0 : ℝ), w s / s * E s) ≤ ∫ s in Ioi (0 : ℝ), deriv w s * E s →
    κ / t₁ * ∫ s in Icc ε t₁, E s ≤ K / δ * ∫ s in Icc δ (2 * δ), E s

/-- **(6) The entrance layer is small** (source 3541-3543, the zero-entrance integral against
`s^{-3/2}`): `∫_δ^{2δ} E ≤ (2δ)^{3/2} ∫_0^{δ₀} s^{-3/2} E` for `2δ < δ₀`. -/
def FUZeroEntranceSmall : Prop :=
  ∀ (δ δ₀ : ℝ) (E : ℝ → ℝ), 0 < δ → 2 * δ < δ₀ → (∀ s, 0 ≤ E s) →
    IntegrableOn E (Icc δ (2 * δ)) →
    ∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) < ⊤ →
    ∫ s in Icc δ (2 * δ), E s ≤
      (2 * δ) ^ (3 / 2 : ℝ) * (∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s)).toReal

/-- **(7) The energy vanishes on every compact age interval of the window** (source 3541-3545,
"let `j → ∞`"): from (4)-(6), letting `δ → 0` in
`(κ/t₁)∫_ε^{t₁} E ≤ (K/δ)(2δ)^{3/2} ∫_0^{δ₀} s^{-3/2}E`. -/
def FUIntervalZero : Prop :=
  ∀ (κ T : ℝ) (E : ℝ → ℝ), 0 < κ → 0 < T → (∀ s, 0 ≤ E s) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → IntegrableOn E (Icc s₁ s₂)) →
    (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∫⁻ s in Ioo 0 δ₀, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E s) < ⊤) →
    (∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioo 0 T →
      (∀ s, 0 ≤ w s) →
      κ * (∫ s in Ioi (0 : ℝ), w s / s * E s) ≤ ∫ s in Ioi (0 : ℝ), deriv w s * E s) →
    ∀ ε t₁ : ℝ, 0 < ε → ε < t₁ → t₁ < T → ∫ s in Icc ε t₁, E s = 0

/-- **(8) From compact intervals to the window**: a nonnegative locally integrable `E` with
`∫_ε^{t₁} E = 0` for all `0 < ε < t₁ < T` vanishes a.e. on `(0,T)`. -/
def FUAeOfIntervals : Prop :=
  ∀ (T : ℝ) (E : ℝ → ℝ), 0 < T → (∀ s, 0 ≤ E s) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → IntegrableOn E (Icc s₁ s₂)) →
    (∀ ε t₁ : ℝ, 0 < ε → ε < t₁ → t₁ < T → ∫ s in Icc ε t₁, E s = 0) →
    ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)), E s = 0

/-- **(9) Zero energy gives zero field** (Fubini on `(0,T) × cell`): if `E(s) = ∫_cell |b(s)|² = 0`
for a.e. `s ∈ (0,T)`, then `b = 0` a.e. on `(0,T) × cell` (a.e. slice integrability from
`energyLoc`, e.g. through `IIIa.SliceLoc`; `Measure.ae_prod_iff_ae_ae`). -/
def FUSliceZero : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (T : ℝ), 0 < c →
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    (∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)), UnforcedLeray.Short.IIIa.energyE c b s = 0) →
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i, b p i = 0

/-- **(10) The flat source is measurable** (source 3569-3571: the meridional block of `F₁ + F₂`). -/
def FUSourceMeas : Prop :=
  ∀ (c mZ ρb : ℝ) (F : Zsp c mZ ρb) (i j : Fin 2), Measurable fun p => merBlockC (zsum F) p i j

/-- **(11) The flat source lies in `𝒯`** (source 3564-3568: `‖F₁ + F₂‖_𝒯 ≤ ‖F‖_Z` for `W ≥ 1`,
`ρ_b ≤ 1`). -/
def FUSourceTNorm : Prop :=
  ∀ (c mZ ρb : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 → ∀ F : Zsp c mZ ρb,
    UnforcedLeray.Short.IIIa.tCalNorm c (merBlockC (zsum F)) ≤ ENNReal.ofReal ‖F‖

/-! ## Proved reductions -/

theorem fuZeroEntranceSlice_of (hAS : UnforcedLeray.Short.IIIa.AgeSlice) : FUZeroEntranceSlice := by
  intro c ν μ F b G hc hsol
  obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
  refine ⟨δ, hδ, ?_⟩
  set g : ℝ × (ℝ × ℝ) → ℝ := fun p => UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 with hg
  have hgm : Measurable g := UnforcedLeray.Short.IIIa.measurable_vnorm2_sq hsol.measurable
  have hg0 : ∀ p, 0 ≤ g p := fun p => sq_nonneg _
  have hgl : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c, ENNReal.ofReal (g p) < ⊤ := by
    intro s₁ s₂ h1 h2
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) (hsol.energyLoc s₁ s₂ h1 h2)
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))
  obtain ⟨-, h2⟩ := hAS c (-3 / 2) g hc hgm hg0 hgl
  have hfin' : ∫⁻ p, ENNReal.ofReal (g p)
      ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤ := hfin
  rw [h2 δ] at hfin'
  have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by
    simpa using inv_pos.2 hc
  change ∫⁻ s in Ioo 0 δ,
    ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * UnforcedLeray.Short.IIIa.sliceSq c g s) < ⊤
  rcases ENNReal.mul_lt_top_iff.1 hfin' with h | h | h
  · exact h.2
  · exact absurd h hc'
  · rw [h]; exact ENNReal.zero_lt_top

/-- The energy `E(s) = ∫_cell |b(s)|²` is nonnegative. -/
theorem fu_energyE_nonneg (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) :
    0 ≤ UnforcedLeray.Short.IIIa.energyE c b s :=
  integral_nonneg fun _ => sq_nonneg _

/-- The dissipation `N(s) = ∫_cell |G(s)|²` is nonnegative. -/
theorem fu_energyN_nonneg (c : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    0 ≤ UnforcedLeray.Short.IIIa.energyN c G s :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Forward uniqueness from the leaves** (source 3541-3545).  `hCore` is the accepted energy
identity (`lionsMagenesCyl (flatWeakFromDensity divFreeCutoffDensity)`), `hEL` the accepted local
integrability `energyLocIntegrable`. -/
theorem freeForwardUniquenessML_of (hCore : UnforcedLeray.Short.IIIa.CoreAll)
    (hEL : UnforcedLeray.Short.IIIa.EnergyLocIntegrable) (hR : FUWindowR) (hCW : FUCoreWindow)
    (hZE : FUZeroEntranceSlice) (hIZ : FUIntervalZero) (hAE : FUAeOfIntervals)
    (hSZ : FUSliceZero) : FreeForwardUniquenessML := by
  intro c ν μ F b G T hc hν hμ hT hFm hFl hF0 hsol
  have hdat : UnforcedLeray.Short.IIIa.FreeSolData c ν μ F b G := ⟨hc, hν, hFl, hFm, hsol⟩
  have hcore := hCore c ν μ F b G hdat
  have hRz := hR c F G T hF0
  have hloc := hEL c ν μ F b G hdat
  have hineq : ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioo 0 T →
      (∀ s, 0 ≤ w s) →
      2 * μ.re * (∫ s in Ioi (0 : ℝ), w s / s * UnforcedLeray.Short.IIIa.energyE c b s) ≤
        ∫ s in Ioi (0 : ℝ), deriv w s * UnforcedLeray.Short.IIIa.energyE c b s := by
    intro w hw hcs hts hw0
    have hts' : tsupport w ⊆ Ioi 0 := hts.trans Ioo_subset_Ioi_self
    exact hCW (2 * μ.re) ν T (UnforcedLeray.Short.IIIa.energyE c b)
      (UnforcedLeray.Short.IIIa.energyN c G) (UnforcedLeray.Short.IIIa.energyR c F G) hν.le
      (fu_energyE_nonneg c b) (fu_energyN_nonneg c G)
      (fun s₁ s₂ h1 h2 => ⟨(hloc s₁ s₂ h1 h2).1, (hloc s₁ s₂ h1 h2).2.1, (hloc s₁ s₂ h1 h2).2.2.1⟩)
      hRz w hw hcs hts hw0 (hcore w hw hcs hts')
  have hint := hIZ (2 * μ.re) T (UnforcedLeray.Short.IIIa.energyE c b) (by linarith) hT
    (fu_energyE_nonneg c b) (fun s₁ s₂ h1 h2 => (hloc s₁ s₂ h1 h2).1)
    (hZE c ν μ F b G hc hsol) hineq
  have hae := hAE T (UnforcedLeray.Short.IIIa.energyE c b) hT (fu_energyE_nonneg c b)
    (fun s₁ s₂ h1 h2 => (hloc s₁ s₂ h1 h2).1) hint
  exact hSZ c ν μ F b G T hc hsol hae

/-- `g⁻¹F = F` for the trivial gain `γ = 0`. -/
theorem fu_gainConj_zero (ν : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.gainConj 0 ν F = F := by
  funext q
  simp [UnforcedLeray.Short.IIIa.gainConj, UnforcedLeray.Short.IIIa.gainG]

/-- **The consumer**: causality of the flat free response from the forward uniqueness
(same bookkeeping as `zeroEntranceCausal_of_forward`, plus measurability and `L²_loc` of the source
`merBlockC (zsum G)`; `IIIa.GainLocF` at `γ = 0` turns `‖·‖_𝒯 < ∞` into `L²_loc`). -/
theorem zeroEntranceCausal_of_forwardML (hFU : FreeForwardUniquenessML) (hM : FUSourceMeas)
    (hTN : FUSourceTNorm) (hGF : UnforcedLeray.Short.IIIa.GainLocF) : ZeroEntranceCausal := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ S0 hS0 T hT
  have hcpos : 0 < p.c := p.c_pos
  have hμre : (0 : ℝ) < ((μ : ℝ) : ℂ).re := by
    have := (hKs hμ).1
    simpa using this
  apply ContinuousLinearMap.ext
  intro F
  set A : Set Chart := ageAbove T with hAdef
  have hAm : MeasurableSet A := ageAbove_measurable T
  have hBm : MeasurableSet (ageBelow T) := ageBelow_measurable T
  set G := inRestr p.c mZ ρb A F with hG
  obtain ⟨b, G', hbv, hsol⟩ := hS0 G
  -- absolute continuity of the chart measures w.r.t. Lebesgue
  have hac : ∀ a, ageμ p.c a ≪
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) :=
    fun a => ageMeasureAC p.c a hcpos
  have hz1 : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) ≪ z1Measure p.c mZ :=
    (FlatSettingInst.volCyl_ac_ageμ hcpos (-1 / 2)).trans
      (FlatSettingInst.ageμ_ac_z1Measure p.c mZ)
  have hht : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) ≪ htRhoMeasure p.c ρb :=
    (FlatSettingInst.volCyl_ac_ageμ hcpos (-1 / 2)).trans
      (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne')
  -- the source of the restricted input vanishes for `s < T`
  have h1 : (G.fst : Chart → Ten3) =ᵐ[z1Measure p.c mZ] ind A • (F.fst : Chart → Ten3) :=
    restrLp_ae hAm F.fst
  have h2 : (G.snd : Chart → Ten3) =ᵐ[htRhoMeasure p.c ρb] ind A • (F.snd : Chart → Ten3) :=
    restrLp_ae hAm F.snd
  have hsrc : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c)),
      q.1 < T → ∀ i j, merBlockC (zsum G) q i j = 0 := by
    filter_upwards [hz1.ae_le h1, hht.ae_le h2] with q hq1 hq2 hqT i j
    have hind : ind A q = 0 := by
      have : q ∉ A := by
        simp only [hAdef, ageAbove, Set.mem_ofPred_eq, not_le]; exact hqT
      simp [ind, Set.indicator_of_notMem this]
    have e1 : (G.fst : Chart → Ten3) q = 0 := by
      rw [hq1]; simp [hind]
    have e2 : (G.snd : Chart → Ten3) q = 0 := by
      rw [hq2]; simp [hind]
    have hz : zsum G q = 0 := by simp [zsum, e1, e2]
    have hns : nsSym (0 : Ten3) = 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ]
    simp [merBlockC, hz, hns]
  -- the source is measurable and locally square integrable
  have hmeas : ∀ i j, Measurable fun q => merBlockC (zsum G) q i j := hM p.c mZ ρb G
  have hfinT : UnforcedLeray.Short.IIIa.tCalNorm p.c (merBlockC (zsum G)) < ⊤ :=
    (hTN p.c mZ ρb hcpos hmZ hρ hρ1 G).trans_lt ENNReal.ofReal_lt_top
  have hl2 : UnforcedLeray.Short.IIIa.L2locTensor p.c (merBlockC (zsum G)) := by
    intro s₁ s₂ hs1 hs2
    have hfin0 : UnforcedLeray.Short.IIIa.tCalNorm p.c
        (UnforcedLeray.Short.IIIa.gainConj 0 p.ν (merBlockC (zsum G))) < ⊤ := by
      rw [fu_gainConj_zero]; exact hfinT
    exact (hGF p.c p.ν 0 hcpos le_rfl p.ν_pos _ hmeas hfin0 s₁ s₂ hs1 hs2).1
  have hzero := hFU p.c p.ν ((μ : ℝ) : ℂ) _ b G' T hcpos p.ν_pos hμre hT hmeas hl2 hsrc hsol
  -- transfer to the velocity measure
  have hzero' : ∀ᵐ q ∂(ageμ p.c (-3 / 2)), q.1 < T → ∀ i, b q i = 0 := (hac _).ae_le hzero
  have hout : ((outRestr p.c (ageBelow T) (S0 G) : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2))
      =ᵐ[ageμ p.c (-3 / 2)] ind (ageBelow T) • ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) :=
    restrLp_ae hBm (S0 G)
  apply Lp.ext
  filter_upwards [hout, hbv, hzero', Lp.coeFn_zero (EuclideanSpace ℝ (Fin 2)) 2
    (ageμ p.c (-3 / 2))] with q hq1 hq2 hq3 hq4
  simp only [ContinuousLinearMap.zero_apply]
  rw [hq4]
  change ((outRestr p.c (ageBelow T) (S0 G) : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0
  rw [hq1]
  change ind (ageBelow T) q • ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0
  by_cases hq : q ∈ ageBelow T
  · have hlt : q.1 < T := hq
    have : ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0 := by
      ext i
      have h5 := hq3 hlt i
      have h6 := hq2
      have h7 : (b q i) = (((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q i : ℂ) := by
        rw [h6]; rfl
      rw [h5] at h7
      simpa using h7.symm
    rw [this, smul_zero]
  · simp [ind, Set.indicator_of_notMem hq]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
