import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:T09/4` (`DivVanish`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`div(√s b) = s[(∂_q - εK) b_r + ∂_η b_z]`) and 1912-1916.

Fundamental lemma through the ring chart `chart R (τ, y) = (s, (q, η))`, `R = ε⁻¹`,
`s = R²/ϱ²`, `q = Rτ/2 - (R/2) log s`, `η = R y₃/ϱ`; the phase test is built from a coordinate
test `χ` supported in the window `|q| < c/2`, `s` in a compact subset of `(0, ∞)`
(so away from the axis), periodized in `q` and pulled back by the chart (`T09/4/1`).  The phase
integral is then the weighted chart integral `πR² c⁻¹ ∫ s^{-5/2} χ g` (`phaseAvg_ringChart`,
`T09/4/2`); `g = gDiv` is locally integrable on `s > 0` (`T09/4/3`), so vanishing against all
window tests gives `g = 0` a.e. on the window strip (`T09/4/4`), then on all `q` by
periodicity (`T09/4/5`).  The converse is chart null-set invariance (`T09/4/6`).

Proved here: `divVanish_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- A coordinate test supported in the window `|q| < c/2` (and `s > 0`). -/
def IsWinTest (c : ℝ) (χ : Coord → ℝ) : Prop :=
  IsCoordTest χ ∧ tsupport χ ⊆ {x : Coord | -c / 2 < x.2.1 ∧ x.2.1 < c / 2}

/-- The `c`-periodization in `q` of a window function. -/
def winPer (c : ℝ) (χ : Coord → ℝ) (x : Coord) : ℝ :=
  χ (x.1, (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2))

/-- The weighted window pairing `∫ χ s^{-5/2} g`. -/
def wInt (χ : Coord → ℝ) (g : Coord → ℂ) : ℂ :=
  ∫ x, ((χ x : ℂ) * ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) * g x

/-- **Lemma `T09/4/1`** (SP 1912-1918): a window coordinate test pulls back through the ring
chart to a phase test (smooth and periodic in `τ` by `Axi.chart_add_period`, vanishing near the
axis and at spatial infinity because `s` is in a compact subset of `(0, ∞)`). -/
def ChartWindowTest : Prop :=
  ∀ (c ε : ℝ) (χ : Coord → ℝ), 0 < c → 0 < ε → IsWinTest c χ →
    ∃ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ ∧
      ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
        φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ)

/-- **Lemma `T09/4/2`** (`Axi.phaseAvg_ringChart`, applied to the real and imaginary parts of the
positive and negative parts, after replacing `gDiv` by an everywhere-periodic representative as
in `pairCont_rep`): for a phase test `φ` that is the pullback of a window test, the phase
integral of `φ · sLift gDiv` is `πR²/c · ∫ χ s^{-5/2} gDiv`. -/
def ChartWindowIntegral : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf) (χ : Coord → ℝ) (φ : ℝ × Space → ℂ), 0 < c → 0 < ε → 2 < r →
    DivData c r ε b Qb Eb → IsWinTest c χ →
    (∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
        φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ)) →
    phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) =
      ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) * wInt χ (gDiv ε b Qb Eb)

/-- **Lemma `T09/4/3`** (SP 1912-1918): for data in the graph class (`r > 2`), `gDiv` is locally
integrable on `s > 0` (on compact subsets of `s > 0` the weight `s^{r/2-5/2}` is bounded above
and below, `b, √s Qb, √s Eb ∈ L^r_loc ⊆ L¹_loc`, and `q`-periodicity handles unbounded `q`). -/
def DivLocInt : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    LocallyIntegrableOn (gDiv ε b Qb Eb) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume

/-- **Lemma `T09/4/4`** (fundamental lemma of the calculus of variations; Mathlib
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the open set
`s > 0, |q| < c/2`, with the smooth positive weight `s^{-5/2}` absorbed into the test). -/
def FundWindow : Prop :=
  ∀ (c : ℝ) (g : Coord → ℂ), 0 < c →
    LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume →
    (∀ χ : Coord → ℝ, IsWinTest c χ → wInt χ g = 0) →
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))), g x = 0

/-- **Lemma `T09/4/5`**: from a.e. vanishing of `gDiv` on the window strip to the whole of
`s > 0`, using the ae `q`-periodicity of `b` and of `√s Qb`, `√s Eb` (`DivData`) and
translation invariance of Lebesgue measure; and `gDiv = s · (Qb₀ + ε b₀ + Eb₁)` with `s > 0`. -/
def DivPeriodicExtend : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))),
        gDiv ε b Qb Eb x = 0) →
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
      Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1 = 0

/-- **Lemma `T09/4/6`** (chart null-set invariance, `chartNullPullback` of `T07`, with the
periodic representative of `pairCont_rep`): if `Qb₀ + ε b₀ + Eb₁ = 0` a.e. on `s > 0` then every
phase integral `⟪φ, sLift gDiv⟫` vanishes. -/
def DivVanishRev : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
      Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1 = 0) →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
      phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) = 0

theorem divVanish_of (h1 : ChartWindowTest) (h2 : ChartWindowIntegral) (h3 : DivLocInt)
    (h4 : FundWindow) (h5 : DivPeriodicExtend) (h6 : DivVanishRev) : DivVanish := by
  intro c ε r b Qb Eb hc hε hr hd
  constructor
  · intro hz
    refine h5 c ε r b Qb Eb hc hε hr hd (h4 c _ hc (h3 c ε r b Qb Eb hc hε hr hd) ?_)
    intro χ hχ
    obtain ⟨φ, hφ, hφe⟩ := h1 c ε χ hc hε hχ
    have e := h2 c ε r b Qb Eb χ φ hc hε hr hd hχ hφe
    rw [hz φ hφ] at e
    have hne : ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) ≠ 0 := by
      have : (Real.pi * (ε⁻¹) ^ 2 / c : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    exact (mul_eq_zero.1 e.symm).resolve_left hne
  · intro hae φ hφ
    exact h6 c ε r b Qb Eb hc hε hr hd hae φ hφ

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divVanish_of
