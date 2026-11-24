import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Part II-b, `PartII-b:T13/1`: the dyadic-window argument for `FlatGraphExists` (organization)

Source of record: `the November 2 reference manuscript` (SP), lines 1912-1938,
with the heat estimate `free:heat-estimate` of SP 1377-1424:

  "For `ε = 0`, the same estimate follows without a limiting argument. The causal formula
  `T_0F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0F(t) dt/t` and weighted dilation give
  `‖T_0‖_{H_r→H_r} ≤ C_r/a_r` [SP 1922-1927]. On each dyadic window `[a,2a]`, cut its heat
  equation off inside `[a/2,4a]` and apply the heat estimate used above. The cutoff costs `a⁻¹`;
  multiplication by `s` cancels it [SP 1928-1930]. Finite overlap and comparability of
  `s^{r/2-5/2}` on each window prove the global bounds for `ST_0` and `νsD²T_0`, and interpolation
  gives its gradient bound [SP 1930-1933]. The cylinder heat estimate follows by applying the
  Euclidean estimate to a cutoff of `N` repeated cells, dividing its `r`-th power by `N`, and letting
  `N → ∞`. There is no period loss [SP 1933-1935]."

## Which response

`FlatCausalExists` (`Sub/T12.lean`) only exposes *some* flat response, characterised by planar
*solenoidal* tests, i.e. its equation holds modulo a pressure gradient. The heat equation that the
source cuts off is the equation of the *causal* response with source `P_0F`:
`∂_s b - νΔ_{q,η} b = (P_0F - μ b)/s` (SP 1925, divide `(μ + S - νsΔ)b = P_0F` by `s`). So the
assembly below works with the concrete objects of `PartII-b:T12`: `G = P_0F` from `FlatLerayHr`
(`flatLerayLiftOfSlice cylinderHelmholtzLr`) and `b = flatDuhamel ν μ G`, and re-runs the
(proved) T12 leaves to get `b ∈ H_r`, `IsFlatResponse ν μ F b` and `‖b‖ ≤ (C_r/a_r)‖F‖`. The one new
input about `b` is that the Duhamel integral solves the equation componentwise against *all* scalar
tests (`DuhamelFullEq`; the T12/7 proof never uses the solenoidality of the test).

## Concrete objects (new here)

* windows: `winOpen a = (a, 2a) × ℝ²`, `winSet2 a = [a/2, 4a] × ℝ²`; the window norm `hNormOn`
  (the `H_r` norm restricted to a set; weight `s^{r/2-5/2}` included) and the unweighted cylinder
  measure `cylMeas c = ds × dq/c dη` (one `q`-cell);
* the cutoff `winCut a s = winCut1 (s/a)`, `winCut1` built from `Real.smoothTransition`
  (`= 1` on `[1,2]`, support in `[1/2,4]`; SP 1928-1930);
* the windowed profile `windowProfile a b = χ_a b` and its heat source
  `windowSource a μ G b = χ_a (G - μ b)/s + χ_a' b` (SP 1928-1930);
* space-time tests `IsSTTestCoord`, the transpose `cylHeatT` of `∂_s - νΔ_{q,η}` and the
  distributional heat equation `IsCylHeat` on `ℝ × ℝ²`;
* `flatTransposeS` / `FullFlatEq`: the equation `(μ + S - νsΔ_{q,η}) b = G` component by component
  against every scalar test of `s > 0`;
* local weak derivatives `HasWeakFOOn` / `HasWeakVecOn` on an open set.

## Leaves (each a `Prop` below; tasks `PartII-b:T13/1/1` ... `/9`)

1. `WinCutProps` — the cutoff properties (SP 1928-1930).
2. `DuhamelFullEq` — the causal Duhamel integral solves the equation against all tests (SP 1925).
3. `WindowHeatEq` (proved from `WinCutProps`) — `χ_a b` solves the cut-off heat equation (SP 1928).
4. `CylHeatMaxReg` — the cylinder heat estimate (SP 1933-1935 from SP 1377-1424).
5. `CylGradInterp` — interpolation on the cylinder (SP 1932-1933).
6. `WindowWeightCompare` — `s^{r/2-5/2}` is comparable to `a^{r/2-5/2}` on `[a/2,4a]` (SP 1931).
7. `WindowBound` (proved from 1, 3, 4, 5, 6) — the window estimates (SP 1928-1933).
8. `WeakGlue` — local weak derivatives on the windows glue to global ones.
9. `DyadicSummation` — finite overlap (SP 1930-1931).

`flatGraphExists_of` assembles `FlatGraphExists` from `DuhamelFullEq`, `WindowBound`, `WeakGlue`,
`DyadicSummation` and the proved T12 leaves.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-! ## Windows, local norms and the cylinder measure -/

/-- The open dyadic window `(a, 2a) × ℝ²` in the chart `(s, (q, η))` (SP 1928). -/
def winOpen (a : ℝ) : Set Coord := Ioo a (2 * a) ×ˢ univ

/-- The enlarged window `[a/2, 4a] × ℝ²` carrying the cutoff (SP 1928-1929). -/
def winSet2 (a : ℝ) : Set Coord := Icc (a / 2) (4 * a) ×ˢ univ

/-- The `H_r` norm restricted to a set `A` (weight `s^{r/2-5/2}` included in `hMeas`). -/
def hNormOn (c r : ℝ) (A : Set Coord) (b : CProf) : ℝ≥0∞ :=
  eLpNorm b (ENNReal.ofReal r) ((hMeas c r).restrict A)

/-- The unweighted cylinder measure `ds × dq/c dη` on `ℝ × cell` (the measure of the cylinder heat
estimate, SP 1933-1935). -/
def cylMeas (c : ℝ) : Measure Coord := (volume : Measure ℝ).prod (UnforcedLeray.Cyl.avgμ c)

/-- Scalar `c`-periodicity in `q`, almost everywhere. -/
def QPeriodicS (c : ℝ) (u : Coord → ℂ) : Prop := ∀ᵐ x : Coord, u (qShift c x) = u x

/-! ## The window cutoff (SP 1928-1930) -/

/-- The base cutoff: `1` on `[1, 2]`, `0` on `(-∞, 1/2]` and on `[4, ∞)`, smooth. -/
def winCut1 (s : ℝ) : ℝ := Real.smoothTransition (2 * s - 1) * Real.smoothTransition ((4 - s) / 2)

/-- The window cutoff `χ_a(s) = winCut1 (s/a)`: `1` on `[a, 2a]`, supported in `[a/2, 4a]`, with
`|χ_a'| ≤ M/a` ("the cutoff costs `a⁻¹`", SP 1929-1930). -/
def winCut (a s : ℝ) : ℝ := winCut1 (s / a)

/-- **Leaf `PartII-b:T13/1/1`** (SP 1928-1930): the properties of the cutoff `χ_a`, with one
constant `M` for all `a > 0` (`M = sup |winCut1'|`; `deriv (winCut a) s = winCut1' (s/a)/a`). -/
def WinCutProps : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 0 < a →
    ContDiff ℝ ∞ (winCut a) ∧ (∀ s ∈ Icc a (2 * a), winCut a s = 1) ∧
      tsupport (winCut a) ⊆ Icc (a / 2) (4 * a) ∧ (∀ s, 0 ≤ winCut a s ∧ winCut a s ≤ 1) ∧
      ∀ s, |deriv (winCut a) s| ≤ M / a

/-- The windowed profile `χ_a(s) b(s, q, η)` (SP 1928). -/
def windowProfile (a : ℝ) (b : CProf) : CProf := fun x => (winCut a x.1 : ℂ) • b x

/-- The source of the cut-off heat equation (SP 1925, 1928-1930): dividing
`(μ + S - νsΔ)b = G` by `s` and multiplying by `χ_a`, `u = χ_a b` solves
`∂_s u - νΔ_{q,η} u = χ_a (G - μ b)/s + χ_a' b`. -/
def windowSource (a : ℝ) (μ : ℂ) (G b : CProf) : CProf := fun x =>
  ((winCut a x.1 / x.1 : ℝ) : ℂ) • (G x - μ • b x) + ((deriv (winCut a) x.1 : ℝ) : ℂ) • b x

/-! ## The heat equation on `ℝ × ℝ²` -/

/-- A space-time test on `ℝ × ℝ²` (no restriction to `s > 0`): smooth with compact support. -/
structure IsSTTestCoord (φ : Coord → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

/-- The transpose `-∂_sφ - νΔ_{q,η}φ` of `∂_s - νΔ_{q,η}`. -/
def cylHeatT (ν : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  -cpd 0 φ x - ν * (cpd 1 (fun y => cpd 1 φ y) x + cpd 2 (fun y => cpd 2 φ y) x)

/-- `(∂_s - νΔ_{q,η}) u = f` in distributions on `ℝ × ℝ²` (scalar, complex valued). -/
def IsCylHeat (ν : ℝ) (u f : Coord → ℂ) : Prop :=
  ∀ φ, IsSTTestCoord φ → ∫ x, u x * (cylHeatT ν φ x : ℂ) = ∫ x, f x * (φ x : ℂ)

/-- **Leaf `PartII-b:T13/1/4`** (the cylinder heat estimate, SP 1933-1935, from the Euclidean
estimate `free:heat-estimate`, SP 1377-1424 = `UnforcedLeray.Parabolic.heat_maximal_regularity`,
`Lib/ParabolicB.lean:158`, with `d = 2`). For `1 < r` there is `C = C_r` (independent of `ν` and of
the period `c`: "no period loss") such that every `q`-periodic `u, f ∈ L^r(ds dq/c dη)` (one cell,
all `s ∈ ℝ`) with `(∂_s - νΔ_{q,η})u = f` in distributions on `ℝ × ℝ²` have weak derivatives
`∂_s u = Dt` and `∂_i∂_j u = D2 i j` (`i, j ∈ {q, η}`, coordinates `i.succ` of the chart),
`q`-periodic and measurable, with `‖Dt‖ + ‖ν D2 i j‖ ≤ C ‖f‖` in `L^r(ds dq/c dη)`. -/
def CylHeatMaxReg : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ u f : Coord → ℂ,
    QPeriodicS c u → QPeriodicS c f → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume → eLpNorm u (ENNReal.ofReal r) (cylMeas c) < ⊤ →
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ → IsCylHeat ν u f →
    ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      (QPeriodicS c Dt ∧ AEStronglyMeasurable Dt volume) ∧
      (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)

/-- **Leaf `PartII-b:T13/1/5`** (interpolation on the cylinder, SP 1932-1933: "interpolation gives
its gradient bound"). For `1 < r` there is `C = C_r` (independent of `c`) such that a `q`-periodic
`u ∈ L^r(ds dq/c dη)` with weak spatial second derivatives `D2 i j ∈ L^r` (periodic, measurable)
has weak spatial first derivatives `D1 i` (periodic, measurable) with
`‖D1 i‖ ≤ C (λ⁻¹‖u‖ + λ Σ_{k,l} ‖D2 k l‖)` for every `λ > 0` (slice-wise in `s`, then integrated). -/
def CylGradInterp : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
    QPeriodicS c u → AEStronglyMeasurable u volume → eLpNorm u (ENNReal.ofReal r) (cylMeas c) < ⊤ →
    (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume ∧
      eLpNorm (D2 i j) (ENNReal.ofReal r) (cylMeas c) < ⊤) →
    (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
      ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) →
    ∃ D1 : Fin 2 → Coord → ℂ,
      (∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume) ∧
      (∀ (i : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ φ x : ℂ) = -∫ x, D1 i x * (φ x : ℂ)) ∧
      ∀ (i : Fin 2) (lam : ℝ), 0 < lam → eLpNorm (D1 i) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
          ENNReal.ofReal lam *
            ∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))

/-! ## The flat equation against all scalar tests -/

/-- Transpose of `μ + S - νsΔ_{q,η}` on a scalar test (`flatTranspose ν μ Ψ x i` is
`flatTransposeS ν μ (fun y => Ψ y i) x`). -/
def flatTransposeS (ν : ℝ) (μ : ℂ) (φ : Coord → ℝ) (x : Coord) : ℂ :=
  (μ - 1) * (φ x : ℂ) - ((x.1 * cpd 0 φ x : ℝ) : ℂ) -
    ((ν * x.1 * (cpd 1 (fun y => cpd 1 φ y) x + cpd 2 (fun y => cpd 2 φ y) x) : ℝ) : ℂ)

/-- `(μ + S - νsΔ_{q,η}) b = G` component by component against every scalar test of `s > 0`
(no pressure: SP 1925 with `G = P_0F`). -/
def FullFlatEq (ν : ℝ) (μ : ℂ) (G b : CProf) : Prop :=
  ∀ (i : Fin 2) (φ : Coord → ℝ), IsCoordTest φ →
    Integrable (fun x => b x i * flatTransposeS ν μ φ x) ∧
      Integrable (fun x => G x i * (φ x : ℂ)) ∧
      ∫ x, b x i * flatTransposeS ν μ φ x = ∫ x, G x i * (φ x : ℂ)

/-- **Leaf `PartII-b:T13/1/2`** (SP 1922-1927, the causal formula): the Duhamel integral
`b = flatDuhamel ν μ G` solves `(μ + S - νsΔ_{q,η}) b = G` against every scalar test, component by
component. This is `DuhamelEquation` (`Sub/T12.lean`, proved as `duhamelEquation`) without the
solenoidality of the test, which its proof (`Sub/T12_7.lean` and
`Tasks/FlatCausal/DuhamelEquation/**`) never uses. -/
def DuhamelFullEq : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → InHr c r (flatDuhamel ν μ G) → FullFlatEq ν μ G (flatDuhamel ν μ G)

/-- **Leaf `PartII-b:T13/1/3`** (SP 1925, 1928-1930: "cut its heat equation off inside
`[a/2,4a]`"): if `b, G ∈ H_r` and `(μ + S - νsΔ)b = G` (all scalar tests), then each component of
`u = χ_a b` solves `(∂_s - νΔ_{q,η}) u = χ_a (G - μ b)/s + χ_a' b` on `ℝ × ℝ²`. (Test the
equation with `ψ = χ_a φ/s`, a test of `s > 0`.) -/
def WindowHeatEq : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ), 0 < c → 1 < r → 0 < ν → ∀ G b : CProf, InHr c r G → InHr c r b →
    FullFlatEq ν μ G b → ∀ a : ℝ, 0 < a → ∀ i : Fin 2,
      IsCylHeat ν (fun x => windowProfile a b x i) (fun x => windowSource a μ G b x i)

/-- **Leaf `PartII-b:T13/1/6`** (SP 1931, comparability of `s^{r/2-5/2}` on each window): on
`A ⊆ [a/2, 4a] × ℝ²` the `H_r` norm and `a^{(r/2-5/2)/r}` times the unweighted cylinder norm are
comparable with constant `16` (`1 < r < 3`, so `-2 < r/2 - 5/2 < -1`). -/
def WindowWeightCompare : Prop :=
  ∀ (c r a : ℝ), 0 < c → 1 < r → r < 3 → 0 < a → ∀ A : Set Coord, MeasurableSet A →
    A ⊆ winSet2 a → ∀ f : CProf, AEStronglyMeasurable f volume →
      hNormOn c r A f ≤ ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm f (ENNReal.ofReal r) ((cylMeas c).restrict A) ∧
        ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
            eLpNorm f (ENNReal.ofReal r) ((cylMeas c).restrict A) ≤
          16 * hNormOn c r A f

/-! ## Local weak derivatives -/

/-- `g = v·∇u + d u` in distributions on the open set `U` (tests supported in `U`). -/
def HasWeakFOOn (U : Set Coord) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u g : Coord → ℂ) :
    Prop :=
  ∀ φ, IsCoordTest φ → tsupport φ ⊆ U →
    Integrable (fun x => u x * (coordTranspose v d φ x : ℂ)) ∧
      Integrable (fun x => g x * (φ x : ℂ)) ∧
      ∫ x, g x * (φ x : ℂ) = ∫ x, u x * (coordTranspose v d φ x : ℂ)

/-- Componentwise `HasWeakFOOn`. -/
def HasWeakVecOn (U : Set Coord) (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b g : CProf) : Prop :=
  ∀ i : Fin 2, HasWeakFOOn U v d (fun x => b x i) (fun x => g x i)

/-- **Leaf `PartII-b:T13/1/7`** (the window estimates, SP 1928-1933). For `1 < r < 3` and `μ` there
is `K = K_{r,μ}` (independent of `ν, c, a`) such that, if `G, b ∈ H_r` and
`(μ + S - νsΔ)b = G` (`FullFlatEq`), then on every window `(a, 2a)` the profile `b` has local weak
derivatives `S a = S b`, `Q a = ∂_q b`, `E a = ∂_η b` (`q`-periodic, measurable) with
`‖S a‖ ≤ K(‖G‖ + ‖b‖)` and `√ν ‖√s (Q a, E a)‖ ≤ K(‖G‖ + ‖b‖)`: norms of `H_r` on `(a, 2a)` on the
left and on `[a/2, 4a]` on the right. Proof: `u = χ_a b` solves the cut-off heat equation
(`WindowHeatEq`); `CylHeatMaxReg` gives `‖∂_s u‖ + ‖νD²u‖ ≲ ‖χ_a(G - μb)/s + χ_a'b‖ ≲
a⁻¹(‖G‖ + ‖b‖)` ("the cutoff costs `a⁻¹`"); multiplication by `s ≤ 2a` cancels it, so
`S a = s ∂_s u` and `ν s D²u` are bounded; `CylGradInterp` with `λ = √(νa)` bounds
`√ν √s ∇u`; `WindowWeightCompare` converts between weighted and unweighted norms. -/
def WindowBound : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, ∃ K : ℝ, 0 < K ∧ ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν μ G b →
    ∃ S Q E : ℝ → CProf, ∀ a : ℝ, 0 < a →
      HasWeakVecOn (winOpen a) vS dZero b (S a) ∧ HasWeakVecOn (winOpen a) vQ0 dZero b (Q a) ∧
      HasWeakVecOn (winOpen a) vEta dZero b (E a) ∧
      (QPeriodic c (S a) ∧ AEStronglyMeasurable (S a) volume) ∧
      (QPeriodic c (Q a) ∧ AEStronglyMeasurable (Q a) volume) ∧
      (QPeriodic c (E a) ∧ AEStronglyMeasurable (E a) volume) ∧
      hNormOn c r (winOpen a) (S a) ≤
        ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (Q a)) ≤
        ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (E a)) ≤
        ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)

/-- **Leaf `PartII-b:T13/1/8`** (weak derivatives are local): if `b` has, on every window
`(a, 2a) × ℝ²`, a local weak derivative `g a` for a first-order operator `v·∇` with smooth
coefficients (`q`-periodic and measurable), then `b` has a global weak derivative on `s > 0`, which
is `q`-periodic, measurable and equal a.e. to `g a` on each window. (Smooth partition of unity in
`s` subordinate to the windows; consistency on overlaps by the fundamental lemma.) -/
def WeakGlue : Prop :=
  ∀ v : Coord → Fin 3 → ℝ, (∀ j, ContDiff ℝ ∞ (fun x => v x j)) → ∀ (c : ℝ) (b : CProf)
    (g : ℝ → CProf), (∀ a : ℝ, 0 < a → HasWeakVecOn (winOpen a) v dZero b (g a)) →
    (∀ a : ℝ, 0 < a → QPeriodic c (g a) ∧ AEStronglyMeasurable (g a) volume) →
    ∃ Gl : CProf, HasWeakVec v dZero b Gl ∧ QPeriodic c Gl ∧ AEStronglyMeasurable Gl volume ∧
      ∀ a : ℝ, 0 < a → ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → Gl x = g a x

/-- **Leaf `PartII-b:T13/1/9`** (finite overlap, SP 1930-1931): the open dyadic windows
`(2^k, 2^{k+1})` exhaust `s > 0` up to a null set, and each `s` lies in at most four enlarged windows
`[2^{k-1}, 2^{k+2}]`, so window bounds `m‖f‖_{(2^k,2^{k+1})} ≤ K(‖g₁‖ + ‖g₂‖)_{[2^{k-1},2^{k+2}]}`
for all `k ∈ ℤ` sum (in `ℓ^r`, Minkowski) to `m‖f‖_{H_r} ≤ 4K(‖g₁‖ + ‖g₂‖)_{H_r}`
(`4^{1/r} ≤ 4`). -/
def DyadicSummation : Prop :=
  ∀ (r c : ℝ), 1 ≤ r → 0 < c → ∀ (f g₁ g₂ : CProf) (m K : ℝ), 0 ≤ m → 0 ≤ K →
    AEStronglyMeasurable f (hMeas c r) → AEStronglyMeasurable g₁ (hMeas c r) →
    AEStronglyMeasurable g₂ (hMeas c r) →
    (∀ k : ℤ, ENNReal.ofReal m * hNormOn c r (winOpen ((2 : ℝ) ^ k)) f ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₁ +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₂)) →
    ENNReal.ofReal m * hNorm c r f ≤ ENNReal.ofReal (4 * K) * (hNorm c r g₁ + hNorm c r g₂)

/-! ## Assembly -/

theorem vQ_zero : vQ 0 = vQ0 := by
  funext x i
  fin_cases i <;> simp [vQ, vQ0]

theorem dQ_zero : dQ 0 = dZero := by
  funext x
  simp [dQ, dZero]

theorem qPeriodic_sqrtS {c : ℝ} {g : CProf} (h : QPeriodic c g) : QPeriodic c (sqrtS g) := by
  filter_upwards [h] with x hx
  simp only [sqrtS, qShift] at hx ⊢
  rw [hx]

theorem aestronglyMeasurable_sqrtS {m : Measure Coord} {g : CProf}
    (h : AEStronglyMeasurable g m) : AEStronglyMeasurable (sqrtS g) m := by
  have hs : AEStronglyMeasurable (fun x : Coord => (Real.sqrt x.1 : ℂ)) m :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).aestronglyMeasurable
  exact hs.smul h

/-- `hMeas c r ≪ volume` (copy of `ageμ_ac_volume`, `Sub/PartII-b_T10_2.lean`). -/
theorem fw_hMeas_ac (c r : ℝ) : hMeas c r ≪ (volume : Measure Coord) := by
  unfold hMeas
  rw [Axi.ageμ, Measure.volume_eq_prod]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · unfold UnforcedLeray.Cyl.avgμ
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem fw_measurableSet_winOpen (a : ℝ) : MeasurableSet (winOpen a) :=
  measurableSet_Ioo.prod MeasurableSet.univ

theorem fw_hNormOn_congr {c r a : ℝ} {f g : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → f x = g x) :
    hNormOn c r (winOpen a) f = hNormOn c r (winOpen a) g := by
  unfold hNormOn
  apply eLpNorm_congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' (fw_measurableSet_winOpen a)]
  exact (Measure.ae_le_iff_absolutelyContinuous.2 (fw_hMeas_ac c r)) h

theorem fw_sqrtS_ae {a : ℝ} {f g : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → f x = g x) :
    ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → sqrtS f x = sqrtS g x := by
  filter_upwards [h] with x hx hmem
  simp only [sqrtS, hx hmem]

theorem fw_vS_smooth : ∀ j, ContDiff ℝ ∞ (fun x : Coord => vS x j) := by
  intro j
  fin_cases j <;> simp [vS] <;> fun_prop

theorem fw_vQ0_smooth : ∀ j, ContDiff ℝ ∞ (fun x : Coord => vQ0 x j) := by
  intro j
  fin_cases j <;> simp [vQ0] <;> fun_prop

theorem fw_vEta_smooth : ∀ j, ContDiff ℝ ∞ (fun x : Coord => vEta x j) := by
  intro j
  fin_cases j <;> simp [vEta] <;> fun_prop

/-- **Conditional assembly of `FlatGraphExists`** (SP 1922-1935): `G = P_0F` (`FlatLerayHr`),
`b = flatDuhamel ν μ G` (the causal formula, SP 1925), the proved T12 leaves give `b ∈ H_r`, the flat
equation and `‖b‖ ≤ (C_r/a_r)‖F‖`; `DuhamelFullEq` and `WindowBound` give the window estimates,
`WeakGlue` the global weak derivatives `Sb, Qb, Eb`, and `DyadicSummation` the global bounds. -/
theorem flatGraphExists_of (hE : DuhamelFullEq) (hW : WindowBound) (hG : WeakGlue)
    (hS : DyadicSummation) : FlatGraphExists := by
  intro r hr hr3 μ ha
  obtain ⟨CL, hCL, hL⟩ := flatLerayLiftOfSlice cylinderHelmholtzLr r hr hr3
  obtain ⟨K, hK, hWK⟩ := hW r hr hr3 μ
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = CL / (μ.re + (3 / r - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = CL + A := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg hCL.le ha.le
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hCL.le hA0
  have hK4 : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hKB : 0 ≤ 4 * K * B := mul_nonneg hK4 hB0
  refine ⟨A + 3 * (4 * K * B), fun ν c hν hc F hF => ?_⟩
  obtain ⟨G, hGH, hGn, hGs, hGp⟩ := hL c hc F hF
  -- the causal response `b = flatDuhamel ν μ G` (as in `flatCausalExists_of`)
  have hbm := duhamelMeasurable r hr hr3 μ ha ν c hν hc G hGH
  have hbn := duhamelBound r hr hr3 μ ha ν c hν hc G hGH
  have hbper := duhamelPeriodic ν μ c G hc hGH.periodic
  have hbH : InHr c r (flatDuhamel ν μ G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal r hr hr3 μ ha ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν μ F (flatDuhamel ν μ G) := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation r hr hr3 μ ha ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]
      exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]
      exact he
  have hfull := hE r hr hr3 μ ha ν c hν hc G hGH hbH
  set b := flatDuhamel ν μ G with hbdef
  -- norms of `G` and `b`
  have hbF : hNorm c r b ≤ ENNReal.ofReal A * hNorm c r F := by
    calc hNorm c r b ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * hNorm c r G := hbn
      _ ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * (ENNReal.ofReal CL * hNorm c r F) := by
          gcongr
      _ = ENNReal.ofReal A * hNorm c r F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.mpr ha).le, hA]
          congr 2
          ring
  have hP : ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F := by
    have hGbF : hNorm c r G + hNorm c r b ≤ ENNReal.ofReal B * hNorm c r F := by
      rw [hB, ENNReal.ofReal_add hCL.le hA0, add_mul]
      exact add_le_add hGn hbF
    calc ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b)
        ≤ ENNReal.ofReal (4 * K) * (ENNReal.ofReal B * hNorm c r F) := by gcongr
      _ = ENNReal.ofReal (4 * K * B) * hNorm c r F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK4]
  have hPfin : ENNReal.ofReal (4 * K * B) * hNorm c r F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  -- window estimates and global weak derivatives
  obtain ⟨S, Q, E, hw⟩ := hWK ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := hG vS fw_vS_smooth c b S
    (fun a ha => (hw a ha).1) (fun a ha => (hw a ha).2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := hG vQ0 fw_vQ0_smooth c b Q
    (fun a ha => (hw a ha).2.1) (fun a ha => (hw a ha).2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := hG vEta fw_vEta_smooth c b E
    (fun a ha => (hw a ha).2.2.1) (fun a ha => (hw a ha).2.2.2.2.2.1)
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  -- `S b`
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c r (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.1
  have hSn : hNorm c r Sb ≤ ENNReal.ofReal (4 * K * B) * hNorm c r F := by
    have h := hS r c hr.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c r)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h.trans hP
  -- `√ν √s ∂_q b`
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F :=
    (hS r c hr.le hc (sqrtS Qb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas
      hQk).trans hP
  -- `√ν √s ∂_η b`
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F :=
    (hS r c hr.le hc (sqrtS Eb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas
      hEk).trans hP
  -- finiteness
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c r (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c r (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  refine ⟨b, hresp, ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
    ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c r), lt_of_le_of_lt hSn hPfin⟩,
    ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r)), hQfin⟩,
    ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r)), hEfin⟩⟩,
    Sb, Qb, Eb, hSbw, ?_, hEbw, ?_⟩
  · rw [vQ_zero, dQ_zero]
    exact hQbw
  · calc hNorm c r b + hNorm c r Sb +
          ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))
        = hNorm c r b + hNorm c r Sb +
          (ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Qb) +
            ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Eb)) := by rw [mul_add]
      _ ≤ ENNReal.ofReal A * hNorm c r F + ENNReal.ofReal (4 * K * B) * hNorm c r F +
          (ENNReal.ofReal (4 * K * B) * hNorm c r F +
            ENNReal.ofReal (4 * K * B) * hNorm c r F) :=
          add_le_add (add_le_add hbF hSn) (add_le_add hQn hEn)
      _ = ENNReal.ofReal (A + 3 * (4 * K * B)) * hNorm c r F := by
          rw [ENNReal.ofReal_add hA0 (mul_nonneg (by norm_num) hKB),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          simp only [ENNReal.ofReal_ofNat]
          ring

end UnforcedLeray.Short.IIb

end
