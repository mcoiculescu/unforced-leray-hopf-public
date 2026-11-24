import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Column

/-!
# `WeakPairValue` from five source facts (audit of `PartIII-b:C/flatset/col/7/3/6`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
`WeakPairValue` follows by: pointwise identity of the integrand (leaf 2, using the pointwise
formula of `(μ - A₀*)ζ_Φ`, leaf 1), integrability of the two pieces (leaf 5), the cell change of
variables `cellPt` (leaf 3, with `c`-periodicity of the tests, leaf 4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatLap)

/-- Leaf 1 (source 1650-1656): `(μ - A₀*)(s^{1/2}Φ) = s^{1/2}(μΦ - sΦ_s - νsΔΦ)` for `s > 0`
(`s ∂_s(√s Φ) = √s(Φ/2 + sΦ_s)`, the `1/2` cancels `-ζ/2` in `A0adj`). -/
def ResolventTestZetaPhi : Prop :=
  ∀ (c ν μ : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ), IsFlatTest c Φ → ∀ p : Profile, 0 < p.1 →
    resolventTest ν μ (zetaPhi Φ) p =
      WithLp.toLp 2 (fun i : Fin 2 => ((Real.sqrt p.1 *
        (μ * Φ p.1 p.2 i - p.1 * flatDt Φ p.1 p.2 i - ν * p.1 * flatLap Φ p.1 p.2 i) : ℝ) : ℂ))

/-- Leaf 2 (source 1684-1689; weights `s^{-3/2}√s = s^{-1}`, `h = s f`): pointwise form of the
forced integrand (`vel = 0`, `F = 0`), given the pointwise formula of leaf 1. -/
def ForcedIntegrandSplit : Prop :=
  ∀ (c ν μ : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ), IsFlatTest c Φ →
    ∀ (f : Chart → Fin 2 → ℂ) (h vR : Hsp c) (p : Chart), 0 < p.1 →
      (∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      resolventTest ν μ (zetaPhi Φ) p =
        WithLp.toLp 2 (fun i : Fin 2 => ((Real.sqrt p.1 *
          (μ * Φ p.1 p.2 i - p.1 * flatDt Φ p.1 p.2 i - ν * p.1 * flatLap Φ p.1 p.2 i) : ℝ) : ℂ)) →
      forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ p =
        (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (resolventTest ν μ (zetaPhi Φ) p) (NearInst.merC (vR p)) -
          (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (zetaPhi Φ p) (NearInst.merC (h p))

/-- Leaf 3 (source 1684-1689; `cellPt` change of variables `NearInst.Masked.CellPtH`,
`cpcH_eq`, `IIb.ageμ_eq_withDensity`): the `H`-pairing of a `cellPt`-pullback with a
`c`-periodic profile is the chart-cell integral against `s^{-3/2}ds dq dη`. -/
def PairHChart : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Hsp c) (h' : HSpace c MeridC),
    (h' : Profile → MeridC) =ᵐ[measureH c] (fun p => NearInst.merC (g (NearInst.cellPt c p))) →
    ∀ w : Profile → MeridC, (∀ p, w (NearInst.cellPt c p) = w p) →
      IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (w p) (NearInst.merC (g p)))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) →
      pairH c (h' : Profile → MeridC) w =
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (w p) (NearInst.merC (g p))

/-- Leaf 4 (`c`-periodicity in `q`, `cellPt` shifts `q` by `0` or `-c`): the tests are invariant
under `cellPt`. -/
def ZetaPhiCellPtInvariant : Prop :=
  ∀ (c ν μ : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ), IsFlatTest c Φ → ∀ p : Profile,
    zetaPhi Φ (NearInst.cellPt c p) = zetaPhi Φ p ∧
      resolventTest ν μ (zetaPhi Φ) (NearInst.cellPt c p) = resolventTest ν μ (zetaPhi Φ) p

/-- Leaf 5 (`ζ_Φ` and `(μ - A₀*)ζ_Φ` are bounded, supported in `s ∈ [s₁,s₂]`, `|η| ≤ R`;
`g ∈ L²(s^{-3/2})`; Cauchy-Schwarz, cf. `weakPairIntegrable`): integrability of the two pieces. -/
def WeakPairPiecesIntegrable : Prop :=
  ∀ (c ν μ : ℝ), 0 < c → ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ, IsFlatTest c Φ → ∀ g : Hsp c,
    IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
        inner ℂ (resolventTest ν μ (zetaPhi Φ) p) (NearInst.merC (g p)))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
    IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (zetaPhi Φ p) (NearInst.merC (g p)))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c)

theorem weakPairValue_of (h1 : ResolventTestZetaPhi) (h2 : ForcedIntegrandSplit)
    (h3 : PairHChart) (h4 : ZetaPhiCellPtInvariant) (h5 : WeakPairPiecesIntegrable) :
    WeakPairValue := by
  intro c ν μ hc Φ hΦ f h vR h' B hh' hB hhf
  set S : Set Chart := Ioi (0 : ℝ) ×ˢ B0579.cell c with hS
  have hSm : MeasurableSet S := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hac := volCyl_ac_ageμ hc (-3 / 2)
  have hhf' : ∀ᵐ p ∂((volume : Measure Chart).restrict S), ∀ i,
      NearInst.velC h p i = (p.1 : ℂ) * f p i := hac.ae_le hhf
  have hpos : ∀ᵐ p ∂((volume : Measure Chart).restrict S), 0 < p.1 :=
    (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun p hp => hp.1)
  obtain ⟨i1, i2⟩ := h5 c ν μ hc Φ hΦ h
  obtain ⟨j1, j2⟩ := h5 c ν μ hc Φ hΦ vR
  have hcongr : ∫ p in S, forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ p =
      ∫ p in S, ((p.1 ^ (-(3 / 2 : ℝ))) •
          inner ℂ (resolventTest ν μ (zetaPhi Φ) p) (NearInst.merC (vR p)) -
        (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (zetaPhi Φ p) (NearInst.merC (h p))) := by
    refine integral_congr_ae ?_
    filter_upwards [hhf', hpos] with p hp hp0
    exact h2 c ν μ Φ hΦ f h vR p hp0 hp (h1 c ν μ Φ hΦ p hp0)
  rw [hcongr, integral_sub j1 i2]
  have e1 := h3 c hc vR B hB (resolventTest ν μ (zetaPhi Φ))
    (fun p => (h4 c ν μ Φ hΦ p).2) j1
  have e2 := h3 c hc h h' hh' (zetaPhi Φ) (fun p => (h4 c ν μ Φ hΦ p).1) i2
  rw [e1, e2]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
