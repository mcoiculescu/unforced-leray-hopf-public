import UnforcedLeray.Short.PartIIb.Sub.T08
import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:T08/1`: the drift identity for nice profiles (conditional)

Source of record: `the November 2 reference manuscript`, lines 1912-1915
(`𝒯(√s b) = √s (S + 1/2) b`, `𝒯 = ∂_τ - y·∇/2`, `S = s∂_s`).

Leaves (`T08/1/1`, `T08/1/2`, `T08/1/3`):
* `DriftWeakS`: for nice `b`, `S b = Sb` weakly gives `Sb = s ∂_s b` a.e. on `s > 0`;
* `DriftSmoothPt`: the identity with the classical `s ∂_s b` (integration by parts in the chart);
* `DriftNvCCongr`: `NvC` pairings only see the profile a.e. on `s > 0` (`ChartNullPullback`).

Proved here: `driftSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `T08/1/1`** (fundamental lemma of the calculus of variations on `s > 0`): if `b` is
nice and `HasWeakVec vS dZero b Sb` (SP 1651, `S = s∂_s`), then `Sb x = s ∂_s b x` for a.e. `x`
with `s > 0`.  Proof: for each component, `∫ (b ∂ᵗ φ) = ∫ Sb φ` for all `IsCoordTest φ`; integrate
by parts classically for smooth `b` and conclude `∫ (Sb - s∂_s b) φ = 0` for all tests, hence
a.e. zero on the open set `s > 0` (du Bois-Reymond; `Tasks/FlatUnique/DualConstancy/DuBoisReymond`
may be reusable). -/
def DriftWeakS : Prop :=
  ∀ (c : ℝ) (b Sb : CProf), NiceProf c b → HasWeakVec vS dZero b Sb →
    ∀ᵐ x : Coord, 0 < x.1 → Sb x = x.1 • fderiv ℝ b x (cdir 0)

/-- **Leaf `T08/1/2`** (SP 1912-1915): classical drift identity.  For nice `b` and a phase test
`Φ`, `⟪𝒯ᵗΦ, N_v b⟫ = ⟪Φ, N_v((s∂_s b) + b/2)⟫`.  Proof: change variables `(τ, y) ↦ (s, q, η)`
(`Axi.chart`, `Lib/Axisymmetric/RingChart.lean`, `phaseAvg_ringChart`), where `driftT = -∂_τ +
(1/2) radialT + (3/2)` becomes `-(S + 1/2)` acting on `√s b` (dilation invariance of
`e_r, e_z`, `chart_similarity`), and integrate by parts with compact support. -/
def DriftSmoothPt : Prop :=
  ∀ (c ε : ℝ) (b : CProf) (Φ : ℝ × Space → CVec3), 0 < c → 0 < ε → NiceProf c b →
    IsPhaseTest (2 * ε * c) Φ →
    pairF (2 * ε * c) (driftT Φ) (NvC ε⁻¹ b) =
      pairF (2 * ε * c) Φ
        (NvC ε⁻¹ (fun x => x.1 • fderiv ℝ b x (cdir 0) + (1 / 2 : ℂ) • b x))

/-- **Leaf `T08/1/3`**: the pairing `⟪Φ, N_v f⟫` is unchanged if `f` is altered on a Lebesgue-null
subset of `s > 0` (not nec. periodic).  Proof: let `E = {s>0, f ≠ g}` (null, take a measurable
null superset), `M = ⋃ₖ qShift^k E` (countable union of null sets, measurable, `q`-periodic),
apply `ChartNullPullback` to `M` and note `NvC R f (τ,y) = NvC R g (τ,y)` when
`chart R τ y ∉ M` and `y` off the axis (as in `phaseLpNorm_NvC_of`, `Sub/T07.lean`). -/
def DriftNvCCongr : Prop :=
  ChartNullPullback → ∀ (c ε : ℝ) (f g : CProf) (Φ : ℝ × Space → CVec3), 0 < c → 0 < ε →
    (∀ᵐ x : Coord, 0 < x.1 → f x = g x) →
    pairF (2 * ε * c) Φ (NvC ε⁻¹ f) = pairF (2 * ε * c) Φ (NvC ε⁻¹ g)

/-- **Target** `DriftSmooth` from its three leaves. -/
theorem driftSmooth_of (h1 : DriftWeakS) (h2 : DriftSmoothPt) (h3 : DriftNvCCongr)
    (hNull : ChartNullPullback) : DriftSmooth := by
  intro c ε b Sb hc hε hb hw Φ hΦ
  rw [h2 c ε b Φ hc hε hb hΦ]
  symm
  refine h3 hNull c ε _ _ Φ hc hε ?_
  filter_upwards [h1 c b Sb hb hw] with x hx hpos
  rw [hx hpos]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.driftSmooth_of
