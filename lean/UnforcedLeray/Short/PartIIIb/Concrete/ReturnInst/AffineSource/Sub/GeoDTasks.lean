import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDDefs

/-!
# `PartIII-b:C/asrc/ra/9/1/2` : the leaves of `GeoDChartId` and `GeoGCellL2`

Source of record: `the November 2 reference manuscript` (73 pages), lines 5034-5039
(ring-chart rules), 4979-4980 (`ĥ_A`), 5063-5079 (Gaussian cell norms, derivative budget).

* `RingT0Rule`, `RingLapRule`, `RingDmuRule` : the exact second-order ring-chart rules (5034-5036),
  generic in the profile `b : Chart → Merid` (`C²` on `s > 0`);
* `HLiftIsNv`, `LatSmooth`, `DcSplit` : `ĥ_A = 𝒩_v b` for `b = hbM` (periodic lattice sums, 4979-4980,
  4991), regularity of the lattice sums, and the planar-bracket split of `D_c b`;
* `GeoGPointwise`, `LatCellBound` : `|G| ≤ C(1+s⁻¹)(1+|η|)³ Σ_w (|w h^p| + |w ψ^p|)` over the
  conormal words `w` of length `≤ 4` (the derivative budget, 5076-5079), and the Gaussian cell
  `L²` bound `≤ P_ν M(A) s^{5/2}` of each word applied to `h^p_A`, `ψ^p_A` (5063-5071).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-! ## 1. Generic ring-chart rules (source 5034-5036) -/

/-- `(∂_τ - y·∇/2 - 1/2)(√s b) = s^{3/2} ∂_s b`, i.e. `(∂_τ - y·∇/2 - 1/2) 𝒩_v b = 𝒩_v (s ∂_s b)`
(source 5034-5035; `T0_chain` of `Lib/Axisymmetric/RingChart.lean` and `y·∇ s = -2 s`). -/
def RingT0Rule : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (b : Chart → Merid) (τ : ℝ) (y : Space), y ∉ axis →
    DifferentiableAt ℝ b (chart R τ y) →
      deriv (fun t => Nv R b t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Nv R b τ) y y
          - (1 / 2 : ℝ) • Nv R b τ y
        = Nv R (fun p => p.1 • UnforcedLeray.Axi.dS b p) τ y

/-- The physical Laplacian of a lift (source 5036-5038):
`Δ(√s b) = s^{3/2}{[Δ_{q,η} - 2ε(𝒦+1)∂_q + ε²(𝒦+1)²] b - ε² b_r e_r}`, `ε = R⁻¹`, for `b` of class
`C²` on `s > 0` (`vecLap_liftMer`, `radial_chain`, `axial_chain` applied twice). -/
def RingLapRule : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (b : Chart → Merid), ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ) →
    ∀ (τ : ℝ) (y : Space), y ∉ axis →
      physLap (Nv R b τ) y =
        Nv R (fun p => p.1 • (lapQE b p - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) p
          + (R⁻¹) ^ 2 • K1 (K1 b) p - (R⁻¹) ^ 2 • erProj (b p))) τ y

/-- `D_μ` on a lift in the chart (source 5034-5039):
`coefOf R (D_μ 𝒩_v b) = s (∂_s + μ/s - νΔ_{q,η}) b + ε s · ringRem b`, `ε = R⁻¹`. -/
def RingDmuRule : Prop :=
  ∀ (R ν μ : ℝ), 0 < R → ∀ (b : Chart → Merid), ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ) →
    ∀ q : Chart, 0 < q.1 →
      coefOf R (physDmu ν μ (Nv R b)) q = q.1 • Dc ν μ b q + (R⁻¹ * q.1) • ringRem ν R⁻¹ b q

/-! ## 2. The lift `ĥ_A = 𝒩_v b` and the lattice sums -/

/-- `ĥ_A = 𝒩_v (hbM)` off the axis: `hbM` is `c`-periodic in `q` (reindex `j ↦ j+1` in the lattice
sums), so `perExt` changes nothing, and `hAcoef = hbM` for `s > 0` (source 4979-4980, 4991). -/
def HLiftIsNv (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ (τ : ℝ) (y : Space), y ∉ axis →
      hLift ν ε (cOf ν) χf A τ y = Nv ε⁻¹ (hbM ν ε χf A) τ y

/-- Regularity of the lattice sums (source 4991 "converge by Gaussian decay", 5076-5079): for
`A ∈ 𝒜` (`C⁶`), `h^p_A` and `ψ^p_A` are jointly `C⁴` on `s > 0` (term-wise differentiation of the
Gaussian lattice sums; cf. `GradLatticeSmooth`). -/
def LatSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 4 (hpM ν χf A) (Ioi 0 ×ˢ univ) ∧ ContDiffOn ℝ 4 (psiM ν χf A) (Ioi 0 ×ˢ univ)

/-- The planar bracket of `r_per` as a chart operator, and linearity of `Dc` (source 5022-5023): for
`q.1 > 0`, `Dc ν μ (hbM) q = toMer(∂_s h^p + (μ/s)h^p - νΔ_{q,η}h^p) + ε Dc ν μ Θ q`. -/
def DcSplit (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ q : Chart, 0 < q.1 →
      Dc ν μ (hbM ν ε χf A) q =
        toMer (deriv (fun s' => hpA ν χf A s' q.2) q.1 + (μ / q.1) • hpA ν χf A q.1 q.2
          - ν • lapPl (hpA ν χf A q.1) q.2) + ε • Dc ν μ (thetaM ν χf A) q

/-! ## 3. The cell bound -/

/-- The conormal operators `s∂_s`, `∂_q`, `∂_η` as `0, 1, 2`. -/
def opW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Fin 3) (F : Chart → E) :
    Chart → E :=
  match a with
  | 0 => fun p => p.1 • UnforcedLeray.Axi.dS F p
  | 1 => UnforcedLeray.Axi.dQ F
  | 2 => UnforcedLeray.Axi.dEta F

/-- A word of conormal operators, applied right to left. -/
def wordW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List (Fin 3) → (Chart → E) → Chart → E
  | [], F => F
  | a :: w, F => opW a (wordW w F)

/-- The words of length `≤ 4` (the derivative budget of source 5076-5079). -/
def budgetWords : Finset (List (Fin 3)) :=
  (Finset.range 5).biUnion fun n => (Finset.univ : Finset (Fin n → Fin 3)).image List.ofFn

/-- Pointwise domination of `G` by the conormal words of `h^p_A`, `ψ^p_A` (source 5034-5041): the
expansion of `G` by the product rule, with weights `1, s⁻¹` (from `∂_s = s⁻¹ (s∂_s)`) and `η ≤ 1+|η|`
(from `𝒦`), the coefficients `ν, ε ≤ 1`, `|μ| ≤ 1`. -/
def GeoGPointwise (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ (IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → ν ≤ 1 → |μ| ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ A : ℝ → Mat3, IsAffElem as A →
      ContDiffOn ℝ 4 (hpM ν χf A) (Ioi 0 ×ˢ univ) → ContDiffOn ℝ 4 (psiM ν χf A) (Ioi 0 ×ˢ univ) →
      ∀ q : Chart, 0 < q.1 →
        ‖geoDG ν μ ε χf A q‖ ≤ C * (1 + q.1⁻¹) * (1 + |q.2.2|) ^ 3 *
          ∑ w ∈ budgetWords, (‖wordW w (hpM ν χf A) q‖ + |wordW w (psiM ν χf A) q|))

/-- **Gaussian summation** (source 5063-5071, 5076-5079): each conormal word of length `≤ 4` applied
to `h^p_A` or `ψ^p_A`, weighted by `(1+|η|)³`, has cell `L²` norm `≤ P_ν M(A) s^{5/2}` on
`0 < s ≤ 1.1/ν`, uniformly for small `ν`. -/
def LatCellBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ w ∈ budgetWords,
        (∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * ‖wordW w (hpM ν χf A) (s, x)‖) ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
          ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ)) ^ 2)) ∧
        (∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * |wordW w (psiM ν χf A) (s, x)|) ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
          ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ)) ^ 2))

end UnforcedLeray.Short.PartIIIb.Concrete
