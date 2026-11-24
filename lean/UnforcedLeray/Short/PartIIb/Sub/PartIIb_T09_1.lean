import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:T09/1` (`DivSmooth`): divergence of the ring lift of a nice profile

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`div(√s b) = s[(∂_q - εK) b_r + ∂_η b_z]`, `∂_q - εK = Q_ε + ε`) and 1912-1916.

Leaves (pattern of `Sub/PartIIb_T08_1.lean`):
* `DivWeakClassical` (`T09/1/1`): for nice `b` a weak first-order derivative is the classical one
  a.e. on `s > 0` (used for `Q_ε` and `∂_η`);
* `DivSmoothPt` (`T09/1/2`): the identity with the classical derivatives (integration by parts in
  the chart);
* `DivNvCCongr` (`T09/1/3`): `phaseInt` of `φ · sLift g` only sees `g` a.e. on `s > 0`.

Proved here: `divSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- The classical first-order operator `v·∇b + d b` on a profile, `v·∇ = Σ_j v_j ∂_j`
(`∂_0, ∂_1, ∂_2 = ∂_s, ∂_q, ∂_η`; `cdir`). -/
def classOp (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b : CProf) : CProf :=
  fun x => (∑ j : Fin 3, (v x j : ℂ) • fderiv ℝ b x (cdir j)) + (d x : ℂ) • b x

/-- **Leaf `T09/1/1`**: for nice `b` and smooth coefficients, `HasWeakVec v d b g` forces
`g = v·∇b + d b` a.e. on `s > 0`.  Proof: for each component and each `IsCoordTest φ`,
`∫ (v·∇b + d b) φ = ∫ b (-div(vφ) + dφ)` by classical integration by parts (`b`, `vφ` smooth,
compact support in `s > 0`), so `∫ (g - classOp b) φ = 0` for all tests; `g` and `classOp b` are
locally integrable on `s > 0`; conclude a.e. (du Bois-Reymond;
`Tasks/FlatUnique/DualConstancy/DuBoisReymond` may be reusable; the T08 analogue is `DriftWeakS`).
Used with `(vQ ε, dQ ε)` and `(vEta, dZero)`, both smooth. -/
def DivWeakClassical : Prop :=
  ∀ (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (c : ℝ) (b g : CProf),
    (∀ j, ContDiff ℝ ∞ (fun x => v x j)) → ContDiff ℝ ∞ d → NiceProf c b →
    HasWeakVec v d b g → ∀ᵐ x : Coord, 0 < x.1 → g x = classOp v d b x

/-- **Leaf `T09/1/2`** (SP 1658-1660, 1912-1916): classical divergence identity for nice `b`,
`⟪∇φ, N_v b⟫ = -⟪φ, s[(Q_ε b)_r + ε b_r + (∂_η b)_z]⟫` with the classical `Q_ε b`, `∂_η b`.
Proof: change variables `(τ, y) ↦ (s, q, η)` (`Axi.chart`, `Lib/Axisymmetric/RingChart.lean`,
`phaseAvg_ringChart`); in the chart `∂_ρ(√s F) = s Q_ε F`, `∂_z(√s F) = s ∂_η F`
(SP 1912-1916); integrate by parts with compact support away from the axis
(`b` vanishes for `s ≥ s₁`, `s ≤ s₀`; pattern `Tasks/DriftNvC/Smooth/SmoothPt`). -/
def DivSmoothPt : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
      pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) =
        -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹
          (gDiv ε b (classOp (vQ ε) (dQ ε) b) (classOp vEta dZero b)) x)

/-- **Leaf `T09/1/3`**: `phaseInt (φ · sLift f)` is unchanged if `f` is altered on a Lebesgue-null
subset of `s > 0` (not nec. periodic).  Proof as `DriftNvCCongr` (`Sub/PartIIb_T08_1.lean`, proved
in `Tasks/DriftNvC/Smooth/Congr.lean`): `ChartNullPullback` applied to the `q`-periodization of
the null set. -/
def DivNvCCongr : Prop :=
  ChartNullPullback → ∀ (c ε : ℝ) (f g : Coord → ℂ) (φ : ℝ × Space → ℂ), 0 < c → 0 < ε →
    IsPhaseTest (2 * ε * c) φ → (∀ᵐ x : Coord, 0 < x.1 → f x = g x) →
    phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ f x) =
      phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ g x)

/-- **Target** `DivSmooth` from its three leaves. -/
theorem divSmooth_of (h1 : DivWeakClassical) (h2 : DivSmoothPt) (h3 : DivNvCCongr)
    (hNull : ChartNullPullback) : DivSmooth := by
  intro c ε b Qb Eb hc hε hb hQ hE φ hφ
  rw [h2 c ε b hc hε hb φ hφ]
  congr 1
  refine h3 hNull c ε _ _ φ hc hε hφ ?_
  have hq := h1 (vQ ε) (dQ ε) c b Qb
    (by intro j; fin_cases j <;> simp [vQ] <;> fun_prop) (by unfold dQ; exact contDiff_const) hb hQ
  have he := h1 vEta dZero c b Eb
    (by intro j; fin_cases j <;> simp [vEta] <;> fun_prop) (by unfold dZero; exact contDiff_const) hb hE
  filter_upwards [hq, he] with x hxq hxe hpos
  simp only [gDiv]
  rw [hxq hpos, hxe hpos]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSmooth_of
