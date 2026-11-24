import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting

/-!
# `KcPathEnergy` from five source facts (decomposition of `PartIII-b:C/flatset/col/4`)

Source of record `the November 2 reference manuscript`: 3426-3430 (energy class),
3236-3240 (`K_c = ∇^⊥Δ⁻¹`), 4614-4615 (finite-energy entrance).  The energy field `b = K_cξ` of a
path `ξ` has: joint measurability (leaf 1), divergence-freeness (leaf 2), a weak gradient `G`
together with the slice bound `∫_cell |b|²+|G|² ≤ K ‖ξ s‖²` (leaf 3), and from the slice bound the
local energy (leaf 4) and the zero entrance (leaf 5) by Tonelli.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 HasWeakCellDerivC)

/-- The slice energy bound: `∫_cell (|b(s,·)|² + |G(s,·)|²) ≤ K n(s)²` for all `s > 0`. -/
def KcSliceBound (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (n : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, ∀ s : ℝ, 0 < s →
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) ≤
      ENNReal.ofReal (K * n s ^ 2)

/-- **(1) Joint measurability of `K_cξ`** (source 3426-3430): for `ξ` continuous on `(0,∞)`, zero on
`s ≤ 0`, `(s,x) ↦ kcMer (ξ s) x i` is measurable.  Route: `kcLp` is `realBiotSavartKernelCLM` after
`reX` (`MixedEvolution.realBiotSavartKernelCLM`, `B0583.norm_velocity_le`), continuous in `ξ`, so
`s ↦ kcLp (ξ s)` is continuous on `Ioi 0`; a jointly strongly measurable `F` with
`F(s,·) =ᵐ kcLp (ξ s)` for `s > 0`
(`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn`); then
`kcMer (ξ s) = lebRep c (F(s,·))` for `s > 0` (`lebRep_congr`), `= 0` for `s ≤ 0`
(`kcLp 0 = 0`), and `lebRep_stronglyMeasurable`. -/
def KcJointMeasurable : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m),
    ContinuousOn ξ (Ioi 0) → (∀ s, s ≤ 0 → ξ s = 0) →
      ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) =>
        (NearInst.velC fun q => kcMer (ξ q.1) q.2) p i

/-- **(2) `K_cξ(s)` is divergence free** (source 3236-3240): the div clause of
`BSAux.isBS_re` via `IIIa.CTE.velocityIsBiotSavart_one c m _ (reX ξ.1) (reX_circ ξ)`
(the proof of `isBiotSavart_kc` shows the pattern). -/
def KcDivFree : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m), (∀ s, s ≤ 0 → ξ s = 0) →
    ∀ s : ℝ, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
        ((NearInst.velC fun q => kcMer (ξ q.1) q.2) (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
          (NearInst.velC fun q => kcMer (ξ q.1) q.2) (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0

/-- **(3) Weak gradient with slice bound** (source 3426-3430): a jointly measurable `G`, the weak
cell gradient of `K_cξ(s)` for every `s > 0`, with `∫_cell |K_cξ(s)|²+|G(s)|² ≤ K ‖ξ s‖²`.  Route:
`G` = joint representative of the real parts of `B0583.velGradQ`, `velGradEta` of `reX (ξ s)`
(continuous in `s` by linearity and `norm_velGradQ_le`, `norm_velGradEta_le`;
`G = 0` for `s ≤ 0`); weak derivatives from `MixedEvolution.realBiotSavart_hasWeakDerivs` and
`kcMer_ae`; the slice bound from `B0583.norm_velocity_le` (`‖kcLp ξ‖ ≤ (c/(2π)+2)‖ξ‖`) and the
gradient norm bounds (`cellVol c = c⁻¹ volume|cell`). -/
def KcGradient : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m),
    ContinuousOn ξ (Ioi 0) → (∀ s, s ≤ 0 → ξ s = 0) →
      ∃ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
        (∀ i j, Measurable fun p => G p i j) ∧
        (∀ s, 0 < s → ∀ i j, HasWeakCellDerivC c j
          (fun x => (NearInst.velC fun q => kcMer (ξ q.1) q.2) (s, x) i) (fun x => G (s, x) i j)) ∧
        KcSliceBound c (NearInst.velC fun q => kcMer (ξ q.1) q.2) G (fun s => ‖ξ s‖)

/-- **(4) Local energy from the slice bound** (Tonelli on the compact age band `[s₁,s₂]`, `n`
continuous on `(0,∞)` hence bounded there, cell of finite volume). -/
def EnergyLocOfSlice : Prop :=
  ∀ (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (n : ℝ → ℝ),
    0 < c → (∀ i, Measurable fun p => b p i) → (∀ i j, Measurable fun p => G p i j) →
    ContinuousOn n (Ioi 0) → KcSliceBound c b G n →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤

/-- **(5) Zero entrance from the slice bound** (source 4614-4615): if `|n(s)| ≤ C s^{5/2}` on
`(0,1]`, then `∫ |b|² d(ageμ c (-3/2)) < ⊤` over `(0,1) × ℝ²`: `ageμ c (-3/2)` has density
`c⁻¹ s^{-3/2}` on `(0,∞) × cell` (`lintegral_ageμ`), so the integral is
`≤ c⁻¹K C² ∫₀¹ s^{-3/2} s^5 ds < ∞`. -/
def ZeroEntranceOfSlice : Prop :=
  ∀ (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (n : ℝ → ℝ)
    (C : ℝ), 0 < c → (∀ i, Measurable fun p => b p i) → (∀ i j, Measurable fun p => G p i j) →
    KcSliceBound c b G n → (∀ s ∈ Ioc (0 : ℝ) 1, |n s| ≤ C * s ^ (5 / 2 : ℝ)) →
      ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) < ⊤

/-- `KcPathEnergy` from the five leaves. -/
theorem kcPathEnergy_of (h1 : KcJointMeasurable) (h2 : KcDivFree) (h3 : KcGradient)
    (h4 : EnergyLocOfSlice) (h5 : ZeroEntranceOfSlice) : KcPathEnergy := by
  intro c m _ _ ξ hξ h0 ⟨C, hC⟩
  obtain ⟨G, hG1, hG2, hG3⟩ := h3 c m ξ hξ h0
  have hc : 0 < c := Fact.out
  have hnc : ContinuousOn (fun s => ‖ξ s‖) (Ioi 0) := hξ.norm
  refine ⟨G, ⟨h1 c m ξ hξ h0, hG1, ?_, ⟨1, one_pos, ?_⟩, h2 c m ξ h0, hG2⟩⟩
  · exact h4 c _ G _ hc (h1 c m ξ hξ h0) hG1 hnc hG3
  · exact h5 c _ G _ C hc (h1 c m ξ hξ h0) hG1 hG3
      (fun s hs => by rw [abs_of_nonneg (norm_nonneg _)]; exact hC s hs)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
