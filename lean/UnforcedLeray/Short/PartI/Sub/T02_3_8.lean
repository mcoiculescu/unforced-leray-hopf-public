import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Lib.Cylinder.Modes

/-!
# Part I, task `PartI:T02/3/8`: bounded solutions of the cylinder pressure equation (conditional)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the bounded
periodic pressure of Gallay-Slijepcevic, line 277) and the Poisson equation for the pressure
(`Δp = -∂_i v_j ∂_j v_i`, line 447).

Target: `CylinderPoissonBound` (`Short/PartI/Sub/T02_3.lean`): for `c > 0` and `B` there is `M`
such that every smooth `c`-periodic divergence-free `u` with `‖D^k u‖ ≤ B` (`k ≤ 4`) tending to
`0` as `|η| → ∞`, and every `C²` `c`-periodic `q → 0` with `Δq = -∂_i u_j ∂_j u_i`, satisfies
`|q| ≤ M(c,B)`.



Write `S = poissonSource u` and `q = P(η) + q̃` with `P = q̄` the `q`-average.

* **Source bound.**  `|S| ≤ 4B²` (only first derivatives of `u` are needed; the second integration
  by parts in `q` of the first sketch is not needed because `Σ_{n ≠ 0} n⁻²` converges).
* **Mean part.**  For `div u = 0`, `S = ∂_η²(u_η²) + 2 ∂_q(u_η ∂_η u_q)` pointwise.  Averaging in `q`
  (periodicity kills the last term) gives `S̄ = (\overline{u_η²})''`, while `P'' = \overline{∂_η² q}
  = \overline{Δq} = -S̄` (the `∂_q²` term averages to `0`).  Hence `(P + \overline{u_η²})'' = 0`, an
  affine function; `P → 0` (decay of `q`, uniformly in `q`) and `\overline{u_η²} ≤ sup |u|² → 0`
  (decay of `u`), so it vanishes and `|P| = \overline{u_η²} ≤ B²`.  No decay of derivatives is
  needed (the "gap" of the first sketch does not exist).
* **Oscillating part.**  The `q`-mode `m_n(η)`, `n ≠ 0`, of `q` is `C²`, tends to `0` as `|η| → ∞`
  and solves `m_n'' - λ_n² m_n = (Δq)_n`, `λ_n = 2π|n|/c`, `|(Δq)_n| ≤ sup |Δq| ≤ K`.  The maximum
  principle (at a maximum of `|m_n|²` one has `(|m_n|²)'' ≤ 0`) gives `|m_n| ≤ K/λ_n²`.  Since
  `Σ n⁻² < ∞`, the Fourier series of the continuous periodic slice converges absolutely and
  `|q̃| ≤ Σ_{n ≠ 0} K c² (4π²n²)⁻¹`.

## What is proved here

`cylinderPoissonBound_of` derives `CylinderPoissonBound` from three statements: the source bound
`CylPoisSourceBound`, the mean-part bound `CylPoisMeanPartBound` and the oscillation bound
`CylPoisOscPartBound`.  The two latter are reduced to eleven elementary leaves in
`Sub/T02_3_8/Mean.lean` (`cylPoisMeanPartBound_of`, four leaves) and `Sub/T02_3_8/Osc.lean`
(`cylPoisOscPartBound_of`, six leaves).  All leaf statements are `Prop` definitions below.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### The three intermediate statements -/

/-- **Mean part** of the pressure (source line 288, `q`-average step): `|\bar q| ≤ B²`.  Hypotheses are
those of `CylinderPoissonBound` with the bound `‖u z‖ ≤ B` (order `0`). -/
def CylPoisMeanPartBound : Prop :=
  ∀ (c B : ℝ), 0 < c → ∀ (u : Plane → Vec) (q : Plane → ℝ),
    ContDiff ℝ ∞ u → ContDiff ℝ 2 q → Cyl.IsPeriodic c u → Cyl.IsPeriodic c q →
    (∀ z, Cyl.divergence u z = 0) → (∀ z, ‖u z‖ ≤ B) →
    Tendsto u (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    Tendsto q (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    (∀ z, Train.lapS q z = - poissonSource u z) → ∀ η : ℝ, |hmean c q η| ≤ B ^ 2

/-- **Oscillating part** (source line 288, Fourier modes in `q`): a `C²` `c`-periodic `q` tending to
`0` as `|η| → ∞` with `|Δq| ≤ K` differs from its `q`-average by at most `M₁(c, K)`. -/
def CylPoisOscPartBound : Prop :=
  ∀ (c K : ℝ), 0 < c → ∃ M₁ : ℝ, ∀ q : Plane → ℝ,
    ContDiff ℝ 2 q → Cyl.IsPeriodic c q →
    Tendsto q (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    (∀ z, |Train.lapS q z| ≤ K) → ∀ z : Plane, |q z - hmean c q z.2| ≤ M₁

/-- **Source bound**: `|∂_i u_j ∂_j u_i| ≤ 4B²` when `‖Du‖ ≤ B`.  With `a = ∂_q u_q`, `b = ∂_q u_η`,
`c = ∂_η u_q`, `d = ∂_η u_η`, each of absolute value `≤ ‖Du z‖ ≤ B`, the source is
`a² + 2bc + d²`.  (`Cyl.partialQ_eq_fderiv`, `norm_iteratedFDeriv_one`-type lemma such as
`norm_fderiv_iteratedFDeriv`/`iteratedFDeriv_one_apply`; coordinates of `Vec` are bounded by the
norm: `EuclideanSpace.norm_eq`, `PiLp.norm_apply_le`; `‖(1,0)‖ = ‖(0,1)‖ = 1` for the sup norm on
`ℝ × ℝ`.) -/
def CylPoisSourceBound : Prop :=
  ∀ (B : ℝ) (u : Plane → Vec), ContDiff ℝ ∞ u → (∀ z, ‖iteratedFDeriv ℝ 1 u z‖ ≤ B) →
    ∀ z, |poissonSource u z| ≤ 4 * B ^ 2

/-! ### Leaves of the mean part -/

/-- **Leaf M1** (`C²` regularity of the horizontal average).  For `C²` `f`, `hmean c f` is `C²` and
its second derivative is the horizontal average of `∂_η² f`.  Proof idea: differentiation under the
integral over the compact interval `Ioc (-c/2) (c/2)`, twice.  Template: `pmi_hasDerivAt_hmean_eta`
(`Tasks/LerayPressureGauge/PressureMeanIdentity.lean`, `C^∞` version, via `mm_hasDerivAt_avg` of
`Tasks/TrainMeanEquations/MeanMomentumU.lean`, which requires `ContDiffOn ℝ ∞`, so it does not apply
verbatim to a `C²` `f`: use `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
the bound from continuity of `∂_η f` on a compact set, exactly as inside `mm_hasDerivAt_avg`).  The
continuity of the second `η`-derivative (`Cyl.contDiff_partialEta`,
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`) gives `ContDiff ℝ 2` via
`contDiff_one_iff_deriv`/`ContDiff.differentiable_deriv_two`. -/
def CylPoisHmeanC2 : Prop :=
  ∀ (c : ℝ) (f : Plane → ℝ), 0 < c → ContDiff ℝ 2 f →
    ContDiff ℝ 2 (hmean c f) ∧
    ∀ η : ℝ, deriv (deriv (hmean c f)) η = hmean c (Cyl.partialEta (Cyl.partialEta f)) η

/-- **Leaf M2** (the `∂_q²` term averages to zero).  For a `C²` `c`-periodic `f`, the horizontal
average of `Δf = ∂_q² f + ∂_η² f` equals the horizontal average of `∂_η² f`.  Proof idea:
`Train.lapS f = ∂_q(∂_q f) + ∂_η(∂_η f)`; `∂_q f` is `C¹` and `c`-periodic (`Cyl.IsPeriodic.partialQ`,
`Cyl.contDiff_partialQ`), so its `q`-derivative integrates to zero over a period
(`mm_integral_partialQ_zero` of `Tasks/TrainMeanEquations/MeanMomentumU.lean` is the `C^∞` version;
copy its proof, which is the fundamental theorem of calculus plus `Cyl.IsPeriodic.neg_half`, for a
`C¹` periodic function); linearity of the integral (second partials of a `C²` function are
continuous, `Cyl.contDiff_partialQ`, `Cyl.contDiff_partialEta`). -/
def CylPoisHmeanLap : Prop :=
  ∀ (c : ℝ) (f : Plane → ℝ), 0 < c → ContDiff ℝ 2 f → Cyl.IsPeriodic c f →
    ∀ η : ℝ, hmean c (Train.lapS f) η = hmean c (Cyl.partialEta (Cyl.partialEta f)) η

/-- **Leaf M3** (the Poisson source of a divergence-free field is a double divergence).  For smooth
`c`-periodic `u` with `div u = 0`, the horizontal average of `∂_i u_j ∂_j u_i` is the horizontal
average of `∂_η²(u_η²)`.  Proof idea: pointwise
`poissonSource u = ∂_η²(u₁²) + 2 ∂_q(u₁ ∂_η u₀)`; indeed `∂_η²(u₁²) = 2 (∂_η u₁)² + 2 u₁ ∂_η² u₁`,
`∂_q u₀ = -∂_η u₁` (so `(∂_q u₀)² = (∂_η u₁)²`), `∂_q(u₁ ∂_η u₀) = ∂_q u₁ ∂_η u₀ + u₁ ∂_q∂_η u₀`
with `∂_q∂_η u₀ = ∂_η∂_q u₀ = -∂_η² u₁` (symmetry of second derivatives of a smooth function,
`ContDiffAt.isSymmSndFDerivAt` or `second_derivative_symmetric`; differentiate the identity
`∂_q u₀ = -∂_η u₁`).  The function `u₁ ∂_η u₀` is smooth and `c`-periodic, so the horizontal average
of its `∂_q` vanishes (`Cyl.integral_cell_deriv_q_of_periodic`, `mm_integral_partialQ_zero`). -/
def CylPoisMeanSource : Prop :=
  ∀ (c : ℝ) (u : Plane → Vec), 0 < c → ContDiff ℝ ∞ u → Cyl.IsPeriodic c u →
    (∀ z, Cyl.divergence u z = 0) → ∀ η : ℝ,
      hmean c (poissonSource u) η =
        hmean c (Cyl.partialEta (Cyl.partialEta (fun z => u z 1 ^ 2))) η

/-- **Leaf M4** (a `C²` function with vanishing second derivative that decays at infinity is zero).
Proof idea: `deriv F` has zero derivative hence is constant `a`, so `F η = a η + F 0`; the limits at
`atTop` and `atBot` (`cocompact_eq_atBot_atTop : cocompact ℝ = atBot ⊔ atTop`) force `a = 0` and `F 0 = 0`. -/
def CylPoisAffineZero : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ η, deriv (deriv F) η = 0) →
    Tendsto F (cocompact ℝ) (𝓝 0) → ∀ η, F η = 0

/-! ### Leaves of the oscillating part -/

/-- **Leaf O1** (`C²` regularity of a `q`-mode in `η`).  For a `C²` complex function `f` on the plane
the `n`-th `q`-mode `η ↦ qMode c hc n f η` (`Lib/Cylinder/Modes.lean`, the Fourier coefficient of the
slice `q ↦ f (q, η)` on `[-c/2, c/2]`) is `C²` and its second derivative is the mode of `∂_η² f`.
Proof idea: as for Leaf M1 (differentiation under the integral on the compact interval, twice),
with the bounded smooth weight `q ↦ fourier (-n) q`; unfold `Cyl.qMode_eq_integral` and use
`mm_hasDerivAt_avg`/`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
def CylPoisModeC2 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (n : ℤ) (f : Plane → ℂ), ContDiff ℝ 2 f →
    ContDiff ℝ 2 (Cyl.qMode c hc n f) ∧
    ∀ η : ℝ, deriv (deriv (Cyl.qMode c hc n f)) η =
      Cyl.qMode c hc n (Cyl.partialEta (Cyl.partialEta f)) η

/-- **Leaf O2** (the mode of the Laplacian).  For a real `C²` `c`-periodic `q` and `n ≠ 0`, with
`f = (q : ℂ)`: the `n`-th mode of `Δq` is the mode of `∂_η² f` minus `(2πn/c)²` times the mode of
`f`.  Proof idea: `Cyl.qMode_partialQ` twice (`f` and `∂_q f` are `C¹`, `c`-periodic; the second
application gives the factor `(2πin/c)² = -(2πn/c)²`), `partialQ`/`partialEta` of `fun z => (q z : ℂ)`
are the coercions of those of `q` (`HasDerivAt.ofReal_comp`), linearity of `qMode` in the function
(`Cyl.qMode_eq_integral`, `intervalIntegral.integral_add`; the second partials are continuous). -/
def CylPoisModeLaplace : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (n : ℤ) (q : Plane → ℝ), ContDiff ℝ 2 q → Cyl.IsPeriodic c q →
    n ≠ 0 → ∀ η : ℝ,
      Cyl.qMode c hc n (fun z => ((Train.lapS q z : ℝ) : ℂ)) η =
        Cyl.qMode c hc n (Cyl.partialEta (Cyl.partialEta (fun z => ((q z : ℝ) : ℂ)))) η -
          (((2 * Real.pi * n / c) ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun z => ((q z : ℝ) : ℂ)) η

/-- **Leaf O3** (size and decay of a `q`-mode).  (a) If `‖f‖ ≤ K` on the plane then `‖qMode‖ ≤ K`
(the weight has modulus `1` and the interval has length `c`: `Cyl.qMode_eq_integral`,
`intervalIntegral.norm_integral_le_of_norm_le_const`, `norm_smul`, `Complex.norm_exp`/`fourier` of
modulus one).  (b) If `f → 0` as `|η| → ∞`, uniformly in `q`, then the mode tends to `0` at
`cocompact ℝ`: given `ε`, for `|η|` large `‖f (q, η)‖ ≤ ε` for all `q`, hence `‖qMode‖ ≤ ε` by (a)
applied to the shifted bound. -/
def CylPoisQModeEstimates : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (n : ℤ) (f : Plane → ℂ),
    (∀ K : ℝ, (∀ z, ‖f z‖ ≤ K) → ∀ η, ‖Cyl.qMode c hc n f η‖ ≤ K) ∧
    (Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
      Tendsto (Cyl.qMode c hc n f) (cocompact ℝ) (𝓝 0))

/-- **Leaf O4** (maximum principle for `h'' = λ² h + g` with `h → 0`).  If `h : ℝ → ℂ` is `C²`,
`λ > 0`, `‖h'' - λ² h‖ ≤ G` and `h → 0` at infinity, then `‖h‖ ≤ 2G/λ²` (the optimal constant is
`G/λ²`; the factor `2` allows the real/imaginary route).  Proof idea (modulus route): `φ = ‖h‖²`
is `C²`, tends to `0`; if `h ≢ 0`, `φ` attains its maximum at some `η₀` (compactness of a
superlevel set, `Continuous.exists_forall_ge_of_tendsto`-type lemma or `exists_forall_ge`); there
`φ' = 0` and `φ'' ≤ 0`; and `φ'' = 2‖h'‖² + 2 Re(conj h · h'') ≥ 2 Re(conj h · h'')
= 2λ²‖h‖² + 2 Re(conj h · g) ≥ 2‖h‖(λ²‖h‖ - G)`, so `λ²‖h(η₀)‖ ≤ G`.  The second-derivative
inequality at a maximum: if `deriv (deriv φ) η₀ > 0` and `deriv φ η₀ = 0` then
`isLocalMin_of_deriv_deriv_pos` (`Mathlib/Analysis/Calculus/DerivativeTest.lean`) makes `η₀` a local
minimum as well as a local maximum, so `φ` is locally constant and `deriv (deriv φ) η₀ = 0`,
contradiction.  (Real/imaginary route: apply the real statement to `Re h`, `Im h`.) -/
def CylPoisMaxPrinciple : Prop :=
  ∀ (h : ℝ → ℂ) (lam G : ℝ), ContDiff ℝ 2 h → 0 < lam →
    (∀ η, ‖deriv (deriv h) η - ((lam ^ 2 : ℝ) : ℂ) * h η‖ ≤ G) →
    Tendsto h (cocompact ℝ) (𝓝 0) → ∀ η, ‖h η‖ ≤ 2 * G / lam ^ 2

/-- **Leaf O5** (pointwise Fourier inversion from a summable majorant).  Let `f` be continuous and
`c`-periodic in `q`; fix `η`.  If the non-zero modes of the slice are bounded by a summable
nonnegative sequence `A`, then `‖f (x, η) - (mean mode)‖ ≤ ∑' n, A n` for every `x`.  Proof idea:
lift `q ↦ f (q, η)` to `C(AddCircle c, ℂ)`; the Fourier coefficients `fourierCoeff` are the modes
(`fourierCoeff_liftIoc_eq`, `Cyl.qMode_eq_integral`, `fourierCoeffOn_eq_integral`; the lift is
continuous because `f (-c/2, η) = f (c/2, η)`, `Cyl.IsPeriodic.neg_half`); they are summable since
`‖fourierCoeff n‖ ≤ A n` for `n ≠ 0` (the term `n = 0` is a single term);
`has_pointwise_sum_fourier_series_of_summable` (`Mathlib/Analysis/Fourier/AddCircle.lean:504`)
gives `f (x, η) = ∑' n, qMode n • fourier n x`; subtract the `n = 0` term (`tsum_eq_zero_add`),
bound the rest by `‖fourier n x‖ = 1` and `A n`.  (Alternative: Parseval `Cyl.hasSum_sq_qMode` plus
`Cyl.sq_norm_le_of_periodic` of `Lib/Cylinder/SupBound.lean` gives a bound of the same shape.) -/
def CylPoisFourierPointwise : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (f : Plane → ℂ) (A : ℤ → ℝ) (η : ℝ),
    Continuous f → Cyl.IsPeriodic c f → Summable A → (∀ n, 0 ≤ A n) →
    (∀ n : ℤ, n ≠ 0 → ‖Cyl.qMode c hc n f η‖ ≤ A n) →
    ∀ x : ℝ, ‖f (x, η) - Cyl.qMode c hc 0 f η‖ ≤ ∑' n, A n

/-- **Leaf O6** (the zeroth mode of a real function is its horizontal average).
`Cyl.qAvg c (↑∘q) η = ↑(hmean c q η)`: `Ico` and `Ioc` integrals agree (`integral_Ico_eq_integral_Ioc`),
`integral_ofReal` commutes the coercion with the integral, `Complex.ofReal_inv`/`real_smul`. -/
def CylPoisQAvgReal : Prop :=
  ∀ (c : ℝ) (q : Plane → ℝ) (η : ℝ),
    Cyl.qAvg c (fun z => ((q z : ℝ) : ℂ)) η = ((hmean c q η : ℝ) : ℂ)

/-! ### The conditional theorem -/

/-- **`CylinderPoissonBound` from the source bound, the mean-part bound and the oscillation
bound.**  With `M = B² + M₁(c, 4B²)`: `|q| ≤ |q̄| + |q - q̄|`, and `|Δq| = |poissonSource u| ≤ 4B²`. -/
theorem cylinderPoissonBound_of (hS : CylPoisSourceBound) (hM : CylPoisMeanPartBound)
    (hO : CylPoisOscPartBound) : CylinderPoissonBound := by
  intro c B hc
  obtain ⟨M₁, hM₁⟩ := hO c (4 * B ^ 2) hc
  refine ⟨B ^ 2 + M₁, fun u q hu hq hup hqp hdiv hD hu0 hq0 hlap z => ?_⟩
  have hB0 : ∀ w, ‖u w‖ ≤ B := fun w => by
    have := hD 0 (by norm_num) w
    simpa using this
  have hD1 : ∀ w, ‖iteratedFDeriv ℝ 1 u w‖ ≤ B := fun w => hD 1 (by norm_num) w
  have hsrc : ∀ w, |Train.lapS q w| ≤ 4 * B ^ 2 := fun w => by
    rw [hlap w, abs_neg]
    exact hS B u hu hD1 w
  have h1 := hM c B hc u q hu hq hup hqp hdiv hB0 hu0 hq0 hlap z.2
  have h2 := hM₁ q hq hqp hq0 hsrc z
  calc |q z| = |hmean c q z.2 + (q z - hmean c q z.2)| := by rw [add_sub_cancel]
    _ ≤ |hmean c q z.2| + |q z - hmean c q z.2| := abs_add_le _ _
    _ ≤ B ^ 2 + M₁ := add_le_add h1 h2

end UnforcedLeray.Short.PartI
