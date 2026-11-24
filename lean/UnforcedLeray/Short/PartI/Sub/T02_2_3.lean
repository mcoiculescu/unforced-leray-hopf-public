import UnforcedLeray.Short.PartI.Sub.T02_2
import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/2/3`: the pressure of a gauge solution is bounded (conditional)

Source of record: `the November 2 reference manuscript`, line 277 ("the bounded
periodic pressure choice") and line 447 ("the decaying pressure gauge is used here").

Target: `PressureBounded` (`Sub/T02_2.lean`): for a classical solution `(v, p)` on `[0,T]` with all
spatial derivatives of `v` bounded, `p(s)` is bounded for every `s ∈ [0,T]`.  `IsClassicalOn` carries
no bound on `p` and `HasBoundedDerivsOn` no bound on `∂_s v`, so boundedness of `p` is itself a
consequence of the equation.

## Mathematics

Write `p̄(s,η)` for the `q`-average and `P_{a,b}(z) = (b-a)⁻¹ ∫_a^b p(σ,z) dσ` for the time average
(`pbAvg`).

* **Mean part.**  `p̄ + \overline{v₂²}` is independent of `η` (`PressureMeanIdentity`) and `|v| ≤ M₀`,
  so `|p̄(s,η)| ≤ |p̄(s,0)| + 2 M₀²` (`PbMeanBounded`).
* **Time-integrated gradient.**  The momentum equation integrated over `[a,b]` gives
  `∫_a^b ∇p dσ = -(v(b) - v(a)) - ∫_a^b ((v·∇)v - νΔv) dσ`, which is bounded by `2 M₀ + T G`
  uniformly in `z` (`PbConvViscBound`, `PbMomentumIntegrated`, `PbTimeGrad`).  Hence the time
  average `P_{a,b}` has bounded gradient, and is `C²` and `c`-periodic with
  `ΔP_{a,b} = -(b-a)⁻¹ ∫_a^b tr((∇v)²) dσ` bounded by `4 B²` (`PbTimeAvgSmooth`, `PressurePoisson`,
  `CylPoisSourceBound`).
* **Oscillating part of a bounded-gradient function with bounded Laplacian** (`PbOscLinear`): a `C²`
  `c`-periodic `q` with bounded partials and `|Δq| ≤ K` satisfies `|q - q̄| ≤ M₁(c,K)`.  (Linear growth
  in `η` kills the exponentially growing `q`-modes `A e^{λη}`, `B e^{-λη}` by a Phragmén-Lindelöf
  maximum principle: `PbGradToGrowth`, `PbMaxPrincipleLinear`; the rest is the decaying case
  `Sub/T02_3_8/Osc.lean`.)  Applied to `P_{a,b}` with `K = 4 B²` it gives
  `|P_{a,b} - \bar P_{a,b}| ≤ M₁` for **all** `0 ≤ a < b ≤ T`, with `M₁` independent of `a, b`.
* **Shrinking the interval.**  `P_{a,b}(z) → p(s,z)` and `\bar P_{a,b} → p̄(s)` as `a, b → s`, so
  `|p(s,z) - p̄(s,z.2)| ≤ M₁` for all `s ∈ [0,T]` (`PbAvgLimit`, from `PbHmeanTimeIntegral`,
  `PbHmeanTimeContinuous`, `PbRealAvgLimit`).

`pressureBounded_of` derives `PressureBounded` from `PressurePoisson`, `CylPoisSourceBound` (both
accepted tasks) and `PbMeanBounded`, `PbOscLinear`, `PbTimeAvgSmooth`, `PbTimeGrad`, `PbAvgLimit`;
`pbAvgLimit_of` derives `PbAvgLimit` from the three real-analysis leaves.  The leaf files live in
`Short/PartI/Tasks/LerayPressureGauge/PressureBounded/`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The time average `(b-a)⁻¹ ∫_a^b p(σ, z) dσ` of a family of functions on the plane. -/
def pbAvg (p : ℝ → Plane → ℝ) (a b : ℝ) (z : Plane) : ℝ :=
  (b - a)⁻¹ * ∫ σ in a..b, p σ z

/-! ### Leaves of `PressureBounded` -/

/-- **Mean part** (source line 447, `p̄ + \overline{v₂²}` is constant in `η`): for each `s ∈ [0,T]`
the `q`-average of `p(s)` is bounded in `η`.  Proof: `pressureMeanIdentity` gives
`hmean c (p s) η = hmean c (p s) 0 + hmean c (v₂²) 0 - hmean c (v₂²) η`, and
`|hmean c (v₂²) η| ≤ M₀²` where `‖v s z‖ ≤ M₀` (`h.bounded 0`, `norm_iteratedFDeriv_zero`,
`norm_setIntegral_le_of_norm_le_const` as in `gg_hmean_tendsto` of `Sub/T02_2.lean`). -/
def PbMeanBounded : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ∃ M : ℝ, ∀ η : ℝ, |hmean c (p s) η| ≤ M

/-- **Oscillating part with bounded gradient** (source lines 276-288 adapted: the decaying case is
`CylPoisOscPartBound`): a `C²` `c`-periodic `q` with bounded first partials and `|Δq| ≤ K` differs
from its `q`-average by at most `M₁(c, K)`.  Decomposition (see `Tasks/LerayPressureGauge/
PressureBounded/OscLinear.lean`): bounded partials and periodicity give `|q(z)| ≤ C (1 + |z.2|)`
(`PbGradToGrowth`), hence the same for every `q`-mode (`(CylPoisQModeEstimates).1` applied to the
slice function `fun z => f (z.1, η)`), the modes `m_n` solve `m_n'' - λ_n² m_n = (Δq)_n` with
`‖(Δq)_n‖ ≤ K`, and `PbMaxPrincipleLinear` gives `‖m_n‖ ≤ 2K/λ_n²`; then exactly as in
`Sub/T02_3_8/Osc.lean` (`cylPoisOscPartBound_of`) with the maximum-principle step replaced. -/
def PbOscLinear : Prop :=
  ∀ (c K : ℝ), 0 < c → ∃ M₁ : ℝ, ∀ q : Plane → ℝ, ContDiff ℝ 2 q → Cyl.IsPeriodic c q →
    (∃ L : ℝ, ∀ z, |Cyl.partialQ q z| ≤ L ∧ |Cyl.partialEta q z| ≤ L) →
    (∀ z, |Train.lapS q z| ≤ K) → ∀ z : Plane, |q z - hmean c q z.2| ≤ M₁

/-- **Linear growth from bounded partials** (leaf of `PbOscLinear`): a `C¹` `c`-periodic function on
the cylinder with bounded partial derivatives grows at most linearly in `η`.  Proof: reduce `q` to
the cell `[-c/2, c/2]` by periodicity (`Cyl.IsPeriodic`, `toIcoMod` or `Function.Periodic.exists_mem_Ico₀`
style), `Q₀ = sup_{|x| ≤ c/2} |q(x,0)|` is finite (`IsCompact.exists_bound_of_continuousOn`), and the
mean value inequality along the vertical line (`Convex.norm_image_sub_le_of_norm_deriv_le` or
`image_le_of_deriv...`, using `Cyl.partialEta` and `Cyl.hasDerivAt_sliceEta`) gives
`|q(x,η) - q(x,0)| ≤ L |η|`, so `|q z| ≤ Q₀ + L |z.2| ≤ (Q₀ + L)(1 + |z.2|)`. -/
def PbGradToGrowth : Prop :=
  ∀ (c : ℝ) (q : Plane → ℝ), 0 < c → ContDiff ℝ 1 q → Cyl.IsPeriodic c q →
    (∃ L : ℝ, ∀ z, |Cyl.partialQ q z| ≤ L ∧ |Cyl.partialEta q z| ≤ L) →
    ∃ C : ℝ, ∀ z : Plane, |q z| ≤ C * (1 + |z.2|)

/-- **Phragmén-Lindelöf maximum principle** (leaf of `PbOscLinear`; the decaying version is
`CylPoisMaxPrinciple`, file `Tasks/ClassicalOdd/CylinderPoissonBound/MaxPrinciple.lean`): if
`h : ℝ → ℂ` is `C²`, `λ > 0`, `‖h'' - λ² h‖ ≤ G` and `h` grows at most linearly, then
`‖h‖ ≤ 2G/λ²`.  Proof (real route, as in the decaying file): apply the real statement to `Re h` and
`Im h` (`|Re (h'' - λ² h)| ≤ G`, `‖h‖ ≤ |Re h| + |Im h|`).  Real statement: if `u : ℝ → ℝ` is `C²`,
`|u'' - λ² u| ≤ G` and `|u η| ≤ C (1 + |η|)`, then `u η ≤ G/λ²` for all `η` (and applying it to `-u`,
`|u| ≤ G/λ²`).  For `ε > 0` the function `w_ε(η) = u(η) - G/λ² - ε cosh(λ η)` tends to `-∞` at `±∞`
(linear against exponential growth), so if `w_ε(η₁) > 0` it attains a global maximum at some `η₀` with
`w_ε(η₀) > 0` and `w_ε''(η₀) ≤ 0` (`cpMP_dd_nonpos` of the decaying file, or
`isLocalMin_of_deriv_deriv_pos` of `Mathlib/Analysis/Calculus/DerivativeTest.lean`), i.e.
`u''(η₀) ≤ ε λ² cosh(λ η₀)`; with `u'' ≥ λ² u - G` this gives `u(η₀) ≤ G/λ² + ε cosh(λ η₀)`,
contradicting `w_ε(η₀) > 0`.  Hence `u η ≤ G/λ² + ε cosh(λ η)` for every `ε > 0`; let `ε → 0`. -/
def PbMaxPrincipleLinear : Prop :=
  ∀ (h : ℝ → ℂ) (lam G : ℝ), ContDiff ℝ 2 h → 0 < lam →
    (∀ η, ‖deriv (deriv h) η - ((lam ^ 2 : ℝ) : ℂ) * h η‖ ≤ G) →
    (∃ C : ℝ, ∀ η, ‖h η‖ ≤ C * (1 + |η|)) → ∀ η, ‖h η‖ ≤ 2 * G / lam ^ 2

/-- **Slice partials of a jointly smooth family are jointly smooth** (leaf of `PbTimeAvgSmooth` and
`PbMomentumIntegrated`): if `(σ, z) ↦ F σ z` is `C^∞` on `[0,T] × ℝ²` with `T > 0`, then so are
`(σ, z) ↦ ∂_q (F σ) z` and `(σ, z) ↦ ∂_η (F σ) z` (the `q`- and `η`-derivatives of the slice).  Proof:
put `H x = F x.1 x.2` and `S = Icc 0 T ×ˢ univ`, which is `UniqueDiffOn` (`uniqueDiffOn_Icc`,
`uniqueDiffOn_univ`, `UniqueDiffOn.prod`; this is where `T > 0` is used).  For `σ ∈ Icc 0 T` the slice
`z ↦ H (σ, z)` is the composite of `H` with `z ↦ (σ, z)` (which maps `univ` into `S`), so
`HasFDerivWithinAt.comp` gives `fderiv ℝ (F σ) z = (fderivWithin ℝ H S (σ, z)).comp
(ContinuousLinearMap.inr ℝ ℝ Plane)`; hence `∂_q (F σ) z = fderivWithin ℝ H S (σ, z) (0, (1, 0))`
(`Cyl.partialQ_eq_fderiv`, `Cyl.partialEta_eq_fderiv` in `Lib/Cylinder/IBP.lean`, with
differentiability of the slice from `gg_slice_contDiff` of `Sub/T02_2.lean`), and
`ContDiffOn.fderivWithin` (`m + 1 ≤ ∞`) makes `fderivWithin ℝ H S` `C^∞` on `S`; compose with the
continuous linear evaluation `L ↦ L (0, (1, 0))` (`ContDiffOn.clm_apply`). -/
def PbSlicePartials : Prop :=
  ∀ (T : ℝ) (F : ℝ → Plane → ℝ), 0 < T →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.partialQ (F x.1) x.2) (Icc 0 T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.partialEta (F x.1) x.2) (Icc 0 T ×ˢ univ)

/-- **Differentiation under a time integral, first order** (leaf of `PbTimeAvgSmooth`): if
`(σ, z) ↦ F σ z` is `C¹` on `[0,T] × ℝ²`, then `z ↦ ∫_a^b F σ z dσ` (`a, b ∈ [0,T]`) is `C¹` and its
partials are the integrals of the partials.  Proof: `hasFDerivAt_integral_of_dominated_of_fderiv_le`
(or the `HasDerivAt` version `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for each partial, as
in `cpH2_hasDerivAt_hmean` of `Tasks/ClassicalOdd/CylinderPoissonBound/HmeanC2.lean`) over the
compact `[a,b]`, with the bound from continuity of `(σ, z) ↦ ∂ F σ z` on the compact set
`[min a b, max a b] × closedBall z 1`; the slice `F σ` is `C¹` on the plane for `σ ∈ [0,T]` (as
`gg_slice_contDiff` of `Sub/T02_2.lean`, for `C¹`), `ContDiff` of the integral from
`contDiff_one_iff_fderiv`/`contDiff_one_iff_deriv`-type criteria or continuity of the parametric
integral (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`). -/
def PbParamDerivC1 : Prop :=
  ∀ (T : ℝ) (F : ℝ → Plane → ℝ) (a b : ℝ), 0 < T → a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
    ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) →
    ContDiff ℝ 1 (fun z => ∫ σ in a..b, F σ z) ∧
    (∀ z, Cyl.partialQ (fun w => ∫ σ in a..b, F σ w) z = ∫ σ in a..b, Cyl.partialQ (F σ) z) ∧
    (∀ z, Cyl.partialEta (fun w => ∫ σ in a..b, F σ w) z = ∫ σ in a..b, Cyl.partialEta (F σ) z)

/-- **Smoothness of a time integral of a jointly smooth family** (source line 447: the time-integrated
pressure): if `(σ, z) ↦ F σ z` is `C^∞` on `[0,T] × ℝ²`, then `z ↦ ∫_a^b F σ z dσ` is `C²`, with first
partials and Laplacian the integrals of those of `F σ`.  Proof: if `T ≤ 0` then `a = b` (or `Icc 0 T`
is empty) and every integral is `0`.  If `T > 0`, apply `PbParamDerivC1` to `F`, to `partialQ ∘ F` and
to `partialEta ∘ F` (these are jointly `C^∞` by `PbSlicePartials`, in particular jointly `C¹`);
`ContDiff ℝ 2` follows from `ContDiff ℝ 1` of the integral `P` and of its two partials, which are the
integrals of `∂_q (F σ)`, `∂_η (F σ)` (`contDiff_succ_iff_fderiv`, with `fderiv ℝ P z` expressed through
`Cyl.partialQ_eq_fderiv`, `Cyl.partialEta_eq_fderiv`: `fderiv ℝ P z = ∂_q P z • proj₁ + ∂_η P z •
proj₂`); and `Train.lapS f = ∂_q(∂_q f) + ∂_η(∂_η f)` together with the partial formulas applied to
`partialQ ∘ F`, `partialEta ∘ F` gives the Laplacian formula. -/
def PbTimeAvgSmooth : Prop :=
  ∀ (T : ℝ) (F : ℝ → Plane → ℝ) (a b : ℝ), a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) →
    ContDiff ℝ 2 (fun z => ∫ σ in a..b, F σ z) ∧
    (∀ z, Cyl.partialQ (fun w => ∫ σ in a..b, F σ w) z = ∫ σ in a..b, Cyl.partialQ (F σ) z) ∧
    (∀ z, Cyl.partialEta (fun w => ∫ σ in a..b, F σ w) z = ∫ σ in a..b, Cyl.partialEta (F σ) z) ∧
    (∀ z, Train.lapS (fun w => ∫ σ in a..b, F σ w) z = ∫ σ in a..b, Train.lapS (F σ) z)

/-- **Convection and viscous terms are bounded** (leaf of `PbTimeGrad`): for a gauge solution there is
`G` with `‖(v·∇)v - νΔv‖ ≤ G` on `[0,T] × ℝ²`.  Proof: `‖v s z‖ ≤ M₀`, `‖D v‖ ≤ M₁`, `‖D² v‖ ≤ M₂`
from `h.bounded 0,1,2` (`norm_iteratedFDeriv_zero`, `gg_component` and `gg_partialQ_le`,
`gg_partialEta_le` of `Sub/T02_2.lean` for the first partials; the second partials via
`fderiv ℝ (fderiv ℝ ·)` as in `iteratedFDeriv_succ_eq_comp_left`/`norm_fderiv_iteratedFDeriv`),
then `Train.advection`, `Train.vecLaplacian`, `Train.lapS` unfold to polynomials in the first and
second partials of the components, bounded by `2 M₀ M₁ + ν · 2 · 2 M₂`-type constants (any
constant suffices; use `EuclideanSpace.norm_eq`, `PiLp.norm_apply_le`-type estimates). -/
def PbConvViscBound : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∃ G : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      ‖Train.advection (v s) z - ν • Train.vecLaplacian (v s) z‖ ≤ G

/-- **The momentum equation integrated in time** (source line 447): for `0 ≤ a ≤ b ≤ T`, `σ ↦ ∇p(σ,z)`
is interval integrable (it is continuous on `[0,T]` by joint smoothness) and
`∫_a^b ∇p(σ,z) dσ = -(v(b,z) - v(a,z)) - ∫_a^b ((v·∇)v - νΔv)(σ,z) dσ`.  Proof: for `σ ∈ (0,T)` the
momentum identity (`h.classical.momentum`, `Train.momentumResidual`) reads
`deriv (fun t => v t z) σ = -(adv - ν vecLap)(σ,z) - gradS (p σ) z`; `σ ↦ v σ z` is continuous on
`[0,T]` and has this derivative on `(a,b) ⊂ (0,T)` (`HasDerivAt` from joint smoothness at interior
points of `Icc 0 T`: `ContDiffOn.contDiffAt` on the open set `Ioo 0 T ×ˢ univ`), the right side is
continuous in `σ` on `[0,T]` (`PbSlicePartials` applied to `p` and to the components of `v`, then to
`∂_q`, `∂_η` of those for the Laplacian; `ContDiffOn.continuousOn`), so
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` gives `∫_a^b deriv = v b z - v a z`; the
interior identity holds a.e. on `[a,b]` (`intervalIntegral.integral_congr_ae` or continuity on the
closed interval and `integral_congr` on `Ioo`) and `intervalIntegral.integral_sub`/`integral_neg`
split the integral. -/
def PbMomentumIntegrated : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → ∀ z : Plane,
      IntervalIntegrable (fun σ => Train.gradS (p σ) z) volume a b ∧
      ∫ σ in a..b, Train.gradS (p σ) z =
        -(v b z - v a z) - ∫ σ in a..b, (Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)

/-- **The time-integrated pressure gradient is bounded** (source line 447; leaf of `PressureBounded`,
decomposed into `PbConvViscBound` and `PbMomentumIntegrated`): there is `L` with
`|∫_a^b ∂_q p(σ,z) dσ|, |∫_a^b ∂_η p(σ,z) dσ| ≤ L` for all `0 ≤ a ≤ b ≤ T` and all `z`.  Proof:
`‖∫_a^b gradS (p σ) z dσ‖ ≤ ‖v b z‖ + ‖v a z‖ + T G ≤ 2 M₀ + T G` by `PbMomentumIntegrated`,
`PbConvViscBound`, `intervalIntegral.norm_integral_le_of_norm_le_const`; the `0`th and `1`st
coordinates of the vector integral are `∫ partialQ`, `∫ partialEta`
(`ContinuousLinearMap.intervalIntegral_comp_comm` with `EuclideanSpace.proj`, `Train.gradS`,
`Train.toVec_zero`/`toVec_one`) and are bounded by its norm (`PiLp.norm_apply_le`). -/
def PbTimeGrad : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∃ L : ℝ, ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b → ∀ z : Plane,
      |∫ σ in a..b, Cyl.partialQ (p σ) z| ≤ L ∧ |∫ σ in a..b, Cyl.partialEta (p σ) z| ≤ L

/-- **The horizontal average commutes with a time integral** (Fubini; leaf of `PbAvgLimit`): for a
family `F` continuous on `[0,T] × ℝ²` and `a, b ∈ [0,T]`,
`hmean c (z ↦ ∫_a^b F σ z dσ) η = ∫_a^b hmean c (F σ) η dσ`.  Proof: unfold `hmean`;
`MeasureTheory.integral_integral_swap` on `Ioc (-c/2) (c/2) × Ι a b` (the function `(q,σ) ↦ F σ (q,η)` is
continuous on the compact rectangle, hence integrable there: `ContinuousOn.integrableOn_compact`,
`Integrable.mono_set` or `ContinuousOn.intervalIntegrable`), then `integral_smul` for the factor
`c⁻¹`. -/
def PbHmeanTimeIntegral : Prop :=
  ∀ (c T : ℝ) (F : ℝ → Plane → ℝ) (a b : ℝ), 0 < c → a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T →
    ContinuousOn (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) →
    ∀ η : ℝ, hmean c (fun w => ∫ σ in a..b, F σ w) η = ∫ σ in a..b, hmean c (F σ) η

/-- **Continuity in time of the horizontal average** (leaf of `PbAvgLimit`): for `F` continuous on
`[0,T] × ℝ²`, `σ ↦ hmean c (F σ) η` is continuous on `[0,T]`.  Proof: `hmean c (F σ) η =
c⁻¹ • ∫_{-c/2}^{c/2} F σ (q,η) dq` is a parametric integral of a function continuous on the compact
set `[0,T] × [-c/2, c/2]` (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
applied to a continuous extension, or `ContinuousOn` version
`ContinuousOn.intervalIntegral`/`continuousOn_primitive`-type lemma, or uniform continuity on the
compact set (`IsCompact.uniformContinuousOn_of_continuous`) and `norm_integral_le_of_norm_le_const`);
`Ioc` versus interval integral by `intervalIntegral.integral_of_le`. -/
def PbHmeanTimeContinuous : Prop :=
  ∀ (c T : ℝ) (F : ℝ → Plane → ℝ), 0 < c →
    ContinuousOn (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) →
    ∀ η : ℝ, ContinuousOn (fun σ => hmean c (F σ) η) (Icc 0 T)

/-- **Averages over shrinking intervals** (leaf of `PbAvgLimit`; pure real analysis): if a continuous
`Φ` on `[0,T]` (`T > 0`) has all interval averages `(b-a)⁻¹ ∫_a^b Φ` bounded by `M` in modulus
(`0 ≤ a < b ≤ T`), then `|Φ s| ≤ M` for every `s ∈ [0,T]`.  Proof: fix `s`; take
`b = min (s + δ) T`, `a = s` when `s < T` (and `a = s - δ`, `b = s` when `s = T`); the averages tend
to `Φ s` as `δ → 0` (continuity of `Φ` at `s` within `Icc 0 T`: `|(b-a)⁻¹ ∫_a^b Φ - Φ s| ≤
sup_{[a,b]} |Φ - Φ s|`, `norm_integral_le_of_norm_le_const`), and `le_of_tendsto`; or via
`intervalIntegral.integral_hasDerivWithinAt_right`/`ContinuousOn.hasDerivWithinAt_integral...` for
the primitive of `Φ`. -/
def PbRealAvgLimit : Prop :=
  ∀ (T M : ℝ) (Φ : ℝ → ℝ), 0 < T → ContinuousOn Φ (Icc 0 T) →
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a < b → |(b - a)⁻¹ * ∫ σ in a..b, Φ σ| ≤ M) →
    ∀ s ∈ Icc (0 : ℝ) T, |Φ s| ≤ M

/-- **From time averages to the pressure itself** (source line 447; the limit step): if the time
averages `pbAvg p a b` of a family `p` continuous on `[0,T] × ℝ²` have oscillation (distance from
their own `q`-average) at most `M` for all `0 ≤ a < b ≤ T`, then so does every slice `p s`,
`s ∈ [0,T]`.  Derived in `pbAvgLimit_of` from `PbHmeanTimeIntegral`, `PbHmeanTimeContinuous`,
`PbRealAvgLimit`. -/
def PbAvgLimit : Prop :=
  ∀ (c T M : ℝ) (p : ℝ → Plane → ℝ), 0 < c → 0 < T →
    ContinuousOn (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ) →
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a < b → ∀ z : Plane,
      |pbAvg p a b z - hmean c (pbAvg p a b) z.2| ≤ M) →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |p s z - hmean c (p s) z.2| ≤ M

/-! ### Elementary helper lemmas -/

theorem pbc_hmean_const_mul {c : ℝ} (k : ℝ) (f : Plane → ℝ) (η : ℝ)
    : hmean c (fun w => k * f w) η = k * hmean c f η := by
  unfold hmean
  rw [integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

theorem pbc_partialQ_const_mul (k : ℝ) (f : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (fun w => k * f w) z = k * Cyl.partialQ f z := by
  show deriv (fun x : ℝ => k * f (x, z.2)) z.1 = k * deriv (fun x : ℝ => f (x, z.2)) z.1
  rw [deriv_const_mul_field']

theorem pbc_partialEta_const_mul (k : ℝ) (f : Plane → ℝ) (z : Plane) :
    Cyl.partialEta (fun w => k * f w) z = k * Cyl.partialEta f z := by
  show deriv (fun x : ℝ => k * f (z.1, x)) z.2 = k * deriv (fun x : ℝ => f (z.1, x)) z.2
  rw [deriv_const_mul_field']

theorem pbc_lapS_const_mul (k : ℝ) (f : Plane → ℝ) (z : Plane) :
    Train.lapS (fun w => k * f w) z = k * Train.lapS f z := by
  have h1 : Cyl.partialQ (fun w => k * f w) = fun w => k * Cyl.partialQ f w :=
    funext (pbc_partialQ_const_mul k f)
  have h2 : Cyl.partialEta (fun w => k * f w) = fun w => k * Cyl.partialEta f w :=
    funext (pbc_partialEta_const_mul k f)
  unfold Train.lapS
  rw [h1, h2, pbc_partialQ_const_mul, pbc_partialEta_const_mul]
  ring

/-! ### The conditional theorems -/

/-- **`PbAvgLimit` from its three real-analysis leaves.** -/
theorem pbAvgLimit_of (hF : PbHmeanTimeIntegral) (hC : PbHmeanTimeContinuous)
    (hL : PbRealAvgLimit) : PbAvgLimit := by
  intro c T M p hc hT hcont hbd s hs z
  have hp1 : ContinuousOn (fun σ => p σ z) (Icc 0 T) :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun σ hσ => ⟨hσ, mem_univ z⟩)
  have hp2 : ContinuousOn (fun σ => hmean c (p σ) z.2) (Icc 0 T) := hC c T p hc hcont z.2
  refine hL T M (fun σ => p σ z - hmean c (p σ) z.2) hT (hp1.sub hp2) ?_ s hs
  intro a ha b hb hab
  have hsub : uIcc a b ⊆ Icc 0 T := by
    rw [uIcc_of_le hab.le]
    exact Icc_subset_Icc ha.1 hb.2
  have i1 : IntervalIntegrable (fun σ => p σ z) volume a b :=
    (hp1.mono hsub).intervalIntegrable
  have i2 : IntervalIntegrable (fun σ => hmean c (p σ) z.2) volume a b :=
    (hp2.mono hsub).intervalIntegrable
  have key : (b - a)⁻¹ * ∫ σ in a..b, (p σ z - hmean c (p σ) z.2) =
      pbAvg p a b z - hmean c (pbAvg p a b) z.2 := by
    have e1 : hmean c (pbAvg p a b) z.2 = (b - a)⁻¹ * ∫ σ in a..b, hmean c (p σ) z.2 := by
      have : pbAvg p a b = fun w => (b - a)⁻¹ * ∫ σ in a..b, p σ w := rfl
      rw [this, pbc_hmean_const_mul, hF c T p a b hc ha hb hcont z.2]
    rw [e1, intervalIntegral.integral_sub i1 i2]
    simp only [pbAvg]
    ring
  rw [key]
  exact hbd a ha b hb hab z

/-- **`PressureBounded` from its leaves.**  `M = M₁ + M₂`, where `M₂` bounds the `q`-average
(`PbMeanBounded`) and `M₁ = M₁(c, 4 B²)` bounds the oscillation (`PbOscLinear` applied to every
time average `pbAvg p a b`, then `PbAvgLimit`). -/
theorem pressureBounded_of (hP : PressurePoisson) (hS : CylPoisSourceBound)
    (hMean : PbMeanBounded) (hOsc : PbOscLinear) (hSm : PbTimeAvgSmooth)
    (hGr : PbTimeGrad) (hLim : PbAvgLimit) : PressureBounded := by
  intro ν c T v p h s hs
  have hc : 0 < c := zero_lt_one.trans_le h.one_le
  have hT : 0 < T := h.T_pos
  obtain ⟨M2, hM2⟩ := hMean ν c T v p h s hs
  obtain ⟨B, hB⟩ := h.bounded 1
  -- the Laplacian of the pressure is bounded, uniformly in time
  have hlap : ∀ σ ∈ Icc (0 : ℝ) T, ∀ z, |Train.lapS (p σ) z| ≤ 4 * B ^ 2 := by
    intro σ hσ z
    have hv : ContDiff ℝ ∞ (v σ) := gg_slice_contDiff hσ h.classical.smooth_v
    have h1 := hS B (v σ) hv (fun w => hB σ hσ w) z
    have h3 : Train.lapS (p σ) z = - poissonSource (v σ) z := by
      rw [hP ν c T v p h σ hσ z]
      unfold poissonSource
      ring
    rw [h3, abs_neg]
    exact h1
  obtain ⟨L, hL⟩ := hGr ν c T v p h
  obtain ⟨M1, hM1⟩ := hOsc c (4 * B ^ 2) hc
  -- oscillation bound for every time average
  have hAvg : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a < b → ∀ z : Plane,
      |pbAvg p a b z - hmean c (pbAvg p a b) z.2| ≤ M1 := by
    intro a ha b hb hab z
    obtain ⟨hP2, hPq, hPe, hPl⟩ := hSm T p a b ha hb h.classical.smooth_p
    have hba : 0 < b - a := sub_pos.2 hab
    have hsub : uIcc a b ⊆ Icc 0 T := by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc ha.1 hb.2
    have hq : pbAvg p a b = fun w => (b - a)⁻¹ * ∫ σ in a..b, p σ w := rfl
    have hC2 : ContDiff ℝ 2 (pbAvg p a b) := by
      rw [hq]
      exact contDiff_const.mul hP2
    have hper : Cyl.IsPeriodic c (pbAvg p a b) := by
      intro w
      show (b - a)⁻¹ * ∫ σ in a..b, p σ (w.1 + c, w.2) = (b - a)⁻¹ * ∫ σ in a..b, p σ w
      congr 1
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      exact h.classical.periodic_p σ (hsub hσ) w
    have hgrad : ∃ L' : ℝ, ∀ w, |Cyl.partialQ (pbAvg p a b) w| ≤ L' ∧
        |Cyl.partialEta (pbAvg p a b) w| ≤ L' := by
      refine ⟨(b - a)⁻¹ * L, fun w => ?_⟩
      obtain ⟨h1, h2⟩ := hL a ha b hb hab.le w
      rw [hq, pbc_partialQ_const_mul, pbc_partialEta_const_mul, hPq, hPe, abs_mul, abs_mul,
        abs_of_pos (inv_pos.2 hba)]
      exact ⟨mul_le_mul_of_nonneg_left h1 (inv_pos.2 hba).le,
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hba).le⟩
    have hlapq : ∀ w, |Train.lapS (pbAvg p a b) w| ≤ 4 * B ^ 2 := by
      intro w
      rw [hq, pbc_lapS_const_mul, hPl, abs_mul, abs_of_pos (inv_pos.2 hba)]
      have hint : |∫ σ in a..b, Train.lapS (p σ) w| ≤ 4 * B ^ 2 * |b - a| := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun σ => Train.lapS (p σ) w) (a := a) (b := b) (C := 4 * B ^ 2)
          (fun σ hσ => by
            rw [Set.uIoc_of_le hab.le] at hσ
            rw [Real.norm_eq_abs]
            exact hlap σ ⟨ha.1.trans hσ.1.le, hσ.2.trans hb.2⟩ w)
        simpa [Real.norm_eq_abs] using this
      calc (b - a)⁻¹ * |∫ σ in a..b, Train.lapS (p σ) w|
          ≤ (b - a)⁻¹ * (4 * B ^ 2 * |b - a|) :=
            mul_le_mul_of_nonneg_left hint (inv_pos.2 hba).le
        _ = 4 * B ^ 2 := by
            rw [abs_of_pos hba]
            field_simp
    exact hM1 (pbAvg p a b) hC2 hper hgrad hlapq z
  -- shrink the interval
  have hlim := hLim c T M1 p hc hT h.classical.smooth_p.continuousOn hAvg s hs
  refine ⟨M1 + M2, fun z => ?_⟩
  calc |p s z| = |(p s z - hmean c (p s) z.2) + hmean c (p s) z.2| := by rw [sub_add_cancel]
    _ ≤ |p s z - hmean c (p s) z.2| + |hmean c (p s) z.2| := abs_add_le _ _
    _ ≤ M1 + M2 := add_le_add (hlim z) (hM2 z.2)

end UnforcedLeray.Short.PartI
