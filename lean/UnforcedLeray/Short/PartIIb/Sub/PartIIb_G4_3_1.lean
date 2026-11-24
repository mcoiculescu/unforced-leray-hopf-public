import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# `PartII-b:G4/3/1` (`InletIBP`): decomposition

Source `the November 2 reference manuscript` lines 2347-2348, 2370-2374, 2042-2046,
1206-1216, 1292.  `InletIBP` follows from three facts: the inlet `E_εα` is smooth, `P`-periodic and
vanishes near the axis (`InletGood`); `U_raw` is smooth, periodic and solenoidal off the axis
(`RawGood`); and the abstract integration by parts for such a pair (`AbsPhaseIBP`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412

/-- The affine inlet `E_εα` is `C^∞` on `ℝ × ℝ³`, `P`-periodic in the phase, and vanishes in a
neighbourhood `ϱ < δ` of the axis (where the age `s = R²/ϱ²` is `≥ H/2`, SP 2347-2348). -/
def InletGood (p : Params) (α : E2) : Prop :=
  ContDiff ℝ ∞ (inletC p α) ∧ (∀ τ y, inletC p α (τ + p.period, y) = inletC p α (τ, y)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ y, Axi.ϱ y < δ → inletC p α (τ, y) = 0

/-- `U_raw` is `C^∞` jointly off the axis, `P`-periodic in the phase and solenoidal there
(SP 1206-1216, 1292, 2042-2046: `U_raw = N_v b_raw`, the solenoidal ring lift). -/
def RawGood (p : Params) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) {x | x.2 ∉ Axi.axis} ∧
    (∀ τ y, p.raw (τ + p.period) y = p.raw τ y) ∧
    ∀ τ y, y ∉ Axi.axis →
      ∑ j : Fin 3, ((fderiv ℝ (p.raw τ) y (EuclideanSpace.single j 1)) j) = 0

/-- **Abstract integration by parts** against a field `E` that is smooth, periodic and zero near the
axis, with a velocity `V` smooth, periodic and solenoidal off the axis (SP 2370-2382; the proof of
`smoothResidualWeakForm_proof` with `V` only smooth on the support of `E`). -/
def AbsPhaseIBP : Prop :=
  ∀ (P ν : ℝ) (V : ℝ → SpatialField) (E : ℝ × Space → CVec3), 0 < P →
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => V x.1 x.2) {x | x.2 ∉ Axi.axis} →
    (∀ τ y, V (τ + P) y = V τ y) →
    (∀ τ y, y ∉ Axi.axis → ∑ j : Fin 3, ((fderiv ℝ (V τ) y (EuclideanSpace.single j 1)) j) = 0) →
    ContDiff ℝ ∞ E → (∀ τ y, E (τ + P, y) = E (τ, y)) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ τ y, Axi.ϱ y < δ → E (τ, y) = 0) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
        pairF P Φ (fun x => L0 ν E x + advT (fun x => realC (V x.1 x.2)) E x +
          advT E (fun x => realC (V x.1 x.2)) x)

/-- Leaf 1: the inlet is smooth, periodic and zero near the axis. -/
def InletGoodAll : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ α : E2, InletGood p α

/-- Leaf 2: `U_raw` is smooth, periodic and solenoidal off the axis. -/
def RawGoodAll : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      RawGood p

theorem inletIBP_of (h1 : InletGoodAll) (h2 : RawGoodAll) (h3 : AbsPhaseIBP) : InletIBP := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨a, ha, H1⟩ := h1 Sig lam q hSig hq dm dp hdm
  obtain ⟨b, hb, H2⟩ := h2 Sig lam q hSig hq dm dp hdm
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro p d hreg hν hs hm α Φ hΦ
  have hν1 : p.ν ≤ a := le_trans hν (min_le_left _ _)
  have hν2 : p.ν ≤ b := le_trans hν (min_le_right _ _)
  obtain ⟨hc, hper, hδ⟩ := H1 p d hreg hν1 hs hm α
  obtain ⟨hr1, hr2, hr3⟩ := H2 p d hreg hν2 hs hm
  exact h3 p.period p.ν p.raw (inletC p α) p.period_pos hr1 hr2 hr3 hc hper hδ Φ hΦ

end UnforcedLeray.Short.IIb
