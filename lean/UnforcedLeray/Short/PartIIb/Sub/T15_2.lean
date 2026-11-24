import UnforcedLeray.Short.PartIIb.Sub.T15

/-!
# Part II-b, task `PartII-b:T15/2`: the weak product rule in the `H_2` measure (conditional)

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the drift
identity `Re ⟨S w, χ² w⟩_{H_2} = (1/4)‖χ w‖² - ∫ s χ χ_s |w|² dH_2`, whose only analytic input is the
product rule `S|w|² = 2 Re(S w \bar w)` in the measure `s^{-3/2} ds`).

## Route (a change of variable removes the Friedrichs commutator)

With `s = e^t` the dilation generator `S = s∂_s` becomes `∂_t`, and the weight `s^{-3/2} ds` becomes
`e^{-t/2} dt`. Put `u(t, y) = e^{-t/4} w(e^t, y)` and `g(t, y) = e^{-t/4} (S w)(e^t, y)`
(`y = (q, η)`). Then `‖u‖_{L²(dt dy)} = ‖w‖_{H_2}` and the periodic weak identity
`∫ Sw φ = -∫ w((1 + a)φ + sφ_s) ds` with `a = -3/2` and `φ = s^{1/4}Φ(log s, y)` becomes

`∫ g Φ dλ = ∫ u (Φ/4 - ∂_tΦ) dλ`,   `λ = dt ⊗ (dq dη / c on the cell)`.   (`LogWeak`)

In these coordinates the operator is a *translation-invariant* weak derivative, so no commutator
arises and the product rule is proved with translations only:

* (`LogTranslationFormula`) `u(t + h, y) - u(t, y) = ∫_0^h G(t + σ, y) dσ` a.e., `G = g - u/4`,
  obtained by testing the weak identity with translated tests, Fubini, and the periodic
  fundamental lemma (`LogFundamental`);
* (`LogAvgConverges`, `LogTranslateContinuous`) the difference quotient converges to `G` in `L²`;
* (`LogCrossLimit`, `LogSquareLimit`) pass to the limit in
  `∫ ψ (|u(· + h)|² - |u|²)/h = Re ∫ ψ ((u(· + h) - u)/h) \bar{(u(· + h) + u)}`;
* (`LogProductRuleScalar`, `LogProductRule`) combine, and the weak product rule follows by pulling
  the result back along `E(t, y) = (e^t, y)` (`ExpChartIntegral`, `LogUMemLp`, `LogTestOfOrig`,
  `LogWeakTransfer`).

The leaves below have exact Lean statements; `weakProductRuleH2_of` is the assembly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The logarithmic chart `s = e^t` -/

/-- The measure `dt ⊗ (dq dη / c on the cell)` on the logarithmic chart `(t, (q, η))`; the type is
`Coord`, whose first coordinate is now `t = log s`. -/
def logMeas (c : ℝ) : Measure Coord := (volume : Measure ℝ).prod (Cyl.avgμ c)

/-- A test function in the logarithmic chart: smooth, `c`-periodic in `q`, vanishing for `|t|` or
`|η|` large. -/
structure LogTest (c : ℝ) (Φ : Coord → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  periodic : ∀ x : Coord, Φ (qShift c x) = Φ x
  compact : ∃ T L : ℝ, ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0

/-- The `H_2`-isometric pull-back `u_i(t, y) = e^{-t/4} w_i(e^t, y)` of the `i`th component of a
profile (`‖u_i‖_{L²(λ)}² = ∫ e^{-t/2}|w_i(e^t, y)|² dλ = ∫ |w_i|² d(s^{-3/2} ds ⊗ dy/c)`). -/
def logU (w : CProf) (i : Fin 2) (x : Coord) : ℂ :=
  ((Real.exp (-x.1 / 4) : ℝ) : ℂ) * w (Real.exp x.1, x.2) i

/-- `∂_t u = g - u/4` weakly in the logarithmic chart against `c`-periodic tests compact in
`(t, η)`: `∫ g Φ = ∫ u (Φ/4 - ∂_tΦ)` (so `G = g - u/4` is the weak `∂_t`-derivative of `u`). -/
def LogWeak (c : ℝ) (u g : Coord → ℂ) : Prop :=
  ∀ Φ : Coord → ℝ, LogTest c Φ →
    ∫ x, g x * (Φ x : ℂ) ∂(logMeas c) = ∫ x, u x * ((Φ x / 4 - cpd 0 Φ x : ℝ) : ℂ) ∂(logMeas c)

/-! ## Leaves -/

/-- **Leaf `PartII-b:T15/2/1`** (change of variable `s = e^t` for the age-weighted cylinder measure).
`ageμ c a = s^a ds|_{s>0} ⊗ avgμ c` is the image of `e^{(a+1)t} dt ⊗ avgμ c` under
`E(t, y) = (e^t, y)`. Stated for the lower integral, and for real and complex Bochner integrals
(unconditionally: both sides are non-integrable together, by the measurable embedding `E`).
Proof: `E` is a measurable embedding with image `Ioi 0 ×ˢ univ`;
`(logMeas c).withDensity (ofReal (e^{(a+1)t})).map E = ageμ c a` from `Units/B0424/Chart.lean`
(`lintegral_expChart'`, density `e^t`) or directly from `MeasurableEmbedding.lintegral_map` and
`lintegral_withDensity_eq_lintegral_mul`. -/
def ExpChartIntegral : Prop :=
  ∀ (c a : ℝ), 0 < c →
    (∀ f : Coord → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Axi.ageμ c a) =
        ∫⁻ x, ENNReal.ofReal (Real.exp ((a + 1) * x.1)) * f (Real.exp x.1, x.2) ∂(logMeas c)) ∧
    (∀ f : Coord → ℝ,
      ∫ x, f x ∂(Axi.ageμ c a) =
        ∫ x, Real.exp ((a + 1) * x.1) * f (Real.exp x.1, x.2) ∂(logMeas c)) ∧
    (∀ f : Coord → ℂ,
      ∫ x, f x ∂(Axi.ageμ c a) =
        ∫ x, ((Real.exp ((a + 1) * x.1) : ℝ) : ℂ) * f (Real.exp x.1, x.2) ∂(logMeas c))

/-- **Leaf `PartII-b:T15/2/2`** (`H_2` membership gives `L²` of the pull-back; uses `T15/2/1`).
If `w ∈ H_2` then `u_i = logU w i ∈ L²(logMeas c)`. Proof: `‖u_i‖ₑ² = ofReal (e^{-t/2}) ‖w_i(e^t, y)‖ₑ²`
and `ExpChartIntegral` with `a = -3/2` (`hMeas c 2 = ageμ c (-3/2)`) gives
`∫⁻ ‖u_i‖ₑ² dλ = ∫⁻ ‖w_i‖ₑ² d(hMeas c 2) ≤ ∫⁻ ‖w‖ₑ² < ∞` (component norm `≤` Euclidean norm);
measurability: `w ∘ E` is a.e.-strongly measurable for `λ` because the density `e^{(a+1)t} > 0`
makes `λ ≪ λ.withDensity` (`MeasurableEmbedding.aestronglyMeasurable_map_iff`,
`AEStronglyMeasurable.mono_ac`). -/
def LogUMemLp : Prop :=
  ∀ (c : ℝ) (w : CProf), 0 < c → InHr c 2 w → ∀ i : Fin 2, MemLp (logU w i) 2 (logMeas c)

/-- **Leaf `PartII-b:T15/2/3`** (original tests give logarithmic tests). If `ψ` is a smooth
`c`-periodic function vanishing outside `σ ≤ s ≤ H`, `|η| ≤ L` with `σ > 0`, then
`ψ̃(t, y) = ψ(e^t, y)` is a `LogTest`, and `∂_tψ̃(t, y) = e^t (∂_sψ)(e^t, y)`.
Proof: composition of smooth maps (`ContDiff.comp`, `(t, y) ↦ (e^t, y)` smooth); periodicity is
`qShift` commuting with `E`; vanishing for `|t| > T = |log σ| + |log |H|| + 1` since
`e^t < σ` for `t < -T` and `e^t > H` for `t > T`; the derivative is the chain rule
(`fderiv` of the composition applied to `cdir 0`). -/
def LogTestOfOrig : Prop :=
  ∀ (c : ℝ) (ψ : Coord → ℝ), ContDiff ℝ ∞ ψ → (∀ x, ψ (qShift c x) = ψ x) →
    (∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → ψ x = 0) →
    LogTest c (fun x => ψ (Real.exp x.1, x.2)) ∧
      ∀ x : Coord, cpd 0 (fun y : Coord => ψ (Real.exp y.1, y.2)) x =
        Real.exp x.1 * cpd 0 ψ (Real.exp x.1, x.2)

/-- **Leaf `PartII-b:T15/2/4`** (logarithmic tests give original periodic tests). For a `LogTest Φ`,
the function `φ(s, y) = s^{1/4} Φ(log s, y)` for `s > 0` and `0` for `s ≤ 0` is a legitimate test of
`PeriodicWeakS` (smooth, `c`-periodic, vanishing outside `σ ≤ s ≤ H`, `|η| ≤ L` with `σ > 0`), with
`φ(e^t, y) = e^{t/4} Φ(t, y)` and `e^t ∂_sφ(e^t, y) = e^{t/4}(Φ/4 + ∂_tΦ)(t, y)`.
Proof: `φ` vanishes for `s < σ = e^{-T}` (`Φ(t, ·) = 0` for `t < -T`), so it is smooth on all of
`Coord` as the gluing of the smooth function on `s > 0` (`Real.rpow`, `Real.log` are smooth there,
`ContDiffAt.rpow_const`, `Real.contDiffAt_log`) with `0` on the open set `s < σ`
(`contDiff_iff_contDiffAt`, case split on `x.1 > 0`); the derivative formula is the product and chain
rule on `s > 0`. -/
def OrigTestOfLog : Prop :=
  ∀ (c : ℝ) (Φ : Coord → ℝ), LogTest c Φ →
    ∃ φ : Coord → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x, φ (qShift c x) = φ x) ∧
      (∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → φ x = 0) ∧
      (∀ x : Coord, φ (Real.exp x.1, x.2) = Real.exp (x.1 / 4) * Φ x) ∧
      (∀ x : Coord, Real.exp x.1 * cpd 0 φ (Real.exp x.1, x.2) =
        Real.exp (x.1 / 4) * (Φ x / 4 + cpd 0 Φ x))

/-- **Leaf `PartII-b:T15/2/5`** (the weak identity in the logarithmic chart; uses `T15/2/1`,
`T15/2/4`). If `PeriodicWeakS c (-3/2) w Sw` then, for each component, `u = logU w i` and
`g = logU Sw i` satisfy `LogWeak`. Proof: given a `LogTest Φ`, take `φ` from `OrigTestOfLog` and
apply the periodic weak identity at `φ` (`a = -3/2`, `1 + a = -1/2`):
`∫ Sw_i φ dμ = ∫ w_i (φ/2 - sφ_s) dμ`; by `ExpChartIntegral` (complex Bochner part, `a = -3/2`,
density `e^{-t/2}`) the left side is `∫ e^{-t/2} Sw_i(e^t, y) e^{t/4}Φ dλ = ∫ g Φ dλ` and the right
side is `∫ e^{-t/2} w_i(e^t, y) e^{t/4}(Φ/4 - ∂_tΦ) dλ = ∫ u (Φ/4 - ∂_tΦ) dλ`
(`e^{t/4}(Φ/2 - Φ/4 - ∂_tΦ)`, pointwise algebra with `Real.exp_add`). No integrability needed. -/
def LogWeakTransfer : Prop :=
  ∀ (c : ℝ) (w Sw : CProf), 0 < c → PeriodicWeakS c (-3 / 2) w Sw →
    ∀ i : Fin 2, LogWeak c (logU w i) (logU Sw i)

/-- **Leaf `PartII-b:T15/2/6`** (periodic fundamental lemma of the calculus of variations; uses
`T15/2/15`). If
`F` is a.e.-strongly measurable, integrable on every `{|t| ≤ T, |η| ≤ L}`, and integrates to `0`
against all `LogTest`s, then `F = 0` a.e. for `logMeas c`. Proof: on the open slab
`U = ℝ × (-c/2, c/2) × ℝ`, `logMeas c = (ofReal c⁻¹) • volume` and `F` is locally integrable for
`volume`; for `ζ ∈ C_c^∞(U)` its `q`-periodization is a `LogTest` that equals `ζ` on the cell
(`PeriodizeCellTest`), whence `∫_U F ζ = 0`; apply `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(Mathlib, `Analysis/Distribution/AEEqOfIntegralContDiff`; periodization is `PeriodizeCellTest`,
`T15/2/15`); the complement of `U` in the support of
`logMeas c` (`q = -c/2`) is null. -/
def LogFundamental : Prop :=
  ∀ (c : ℝ) (F : Coord → ℂ), 0 < c → AEStronglyMeasurable F (logMeas c) →
    (∀ T L : ℝ, IntegrableOn F {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c)) →
    (∀ Φ : Coord → ℝ, LogTest c Φ → ∫ x, F x * (Φ x : ℂ) ∂(logMeas c) = 0) →
    F =ᵐ[logMeas c] 0

/-- **Leaf `PartII-b:T15/2/7`** (continuity of `t`-translation in `L²(logMeas c)`). For
`f ∈ L²(logMeas c)`, `∫ ‖f(t + σ, y) - f(t, y)‖² dλ → 0` as `σ → 0`. Proof: `logMeas c` is a
locally finite Borel measure on `ℝ³` (`ℝ × (ofReal c⁻¹ • volume|_cell)`), so continuous compactly
supported functions are dense in `L²` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`); for such a
`g` uniform continuity gives `‖g(· + σ) - g‖_{L²} ≤ sup|g(· + σ) - g| · λ(K')^{1/2} → 0`; and
`‖f(· + σ) - g(· + σ)‖_{L²} = ‖f - g‖_{L²}` because `λ` is invariant under `t`-translation
(`(measurePreserving_add_right volume σ).prod (MeasurePreserving.id _)`); finish with the `ε/3`
argument. -/
def LogTranslateContinuous : Prop :=
  ∀ (c : ℝ) (f : Coord → ℂ), 0 < c → MemLp f 2 (logMeas c) →
    Tendsto (fun σ : ℝ => ∫⁻ x, ‖f (x.1 + σ, x.2) - f x‖ₑ ^ 2 ∂(logMeas c)) (𝓝 0) (𝓝 0)

/-- **Leaf `PartII-b:T15/2/8`** (the shifted weak identity; Fubini and FTC; uses `T15/2/16`). For `u, g ∈ L²(logMeas c)` with `LogWeak c u g`, `G = g - u/4`, every `h` and `LogTest Φ`:
`∫ (u(t + h, y) - u(t, y)) Φ dλ = ∫ (∫_0^h G(t + σ, y) dσ) Φ dλ`. Proof: `G` is the weak derivative
(`∫ G Φ = -∫ u ∂_tΦ`, from `LogWeak` and `∫ uΦ/4`; all pairings are integrable since `u, g ∈ L²` and
`Φ` is bounded with support of finite `λ`-measure). By `LogShiftTest` (`T15/2/16`)
`∫ G(t + σ)Φ(t) dλ = -∫ u (∂_tΦ)(t - σ, y) dλ`. Integrate over `σ ∈ [0, h]`
(Fubini for `σ`, `(t, y)`: the function `(σ, x) ↦ G(x.1 + σ, x.2)Φ(x)` is integrable on
`[0, h] × supp Φ`), and use `∫_0^h (∂_tΦ)(t - σ) dσ = Φ(t) - Φ(t - h)` (FTC) and
`∫ u(t + h)Φ(t) dλ = ∫ u Φ(· - h) dλ`. -/
def LogShiftWeak : Prop :=
  ∀ (c : ℝ) (u g : Coord → ℂ), 0 < c → MemLp u 2 (logMeas c) → MemLp g 2 (logMeas c) →
    LogWeak c u g → ∀ (h : ℝ) (Φ : Coord → ℝ), LogTest c Φ →
      ∫ x, (u (x.1 + h, x.2) - u x) * (Φ x : ℂ) ∂(logMeas c) =
        ∫ x, (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
          ∂(logMeas c)

/-- **Leaf `PartII-b:T15/2/9`** (the translation formula; uses `T15/2/6`, `T15/2/8`, `T15/2/17`). For `u, g` as in
`LogShiftWeak`, for each `h`, a.e. in `x`:
`u(t + h, y) - u(t, y) = ∫_0^h (g - u/4)(t + σ, y) dσ`. Proof: `F = u(· + h) - u - ∫_0^h G(· + σ) dσ`
is a.e.-strongly measurable and integrable on `{|t| ≤ T, |η| ≤ L}` (the first two terms are in `L²`
of a finite-measure set, hence in `L¹`; for the average use `LogAvgLocInt`, `T15/2/17`), and by
`LogShiftWeak` it integrates to `0` against every `LogTest`; apply `LogFundamental`. -/
def LogTranslationFormula : Prop :=
  ∀ (c : ℝ) (u g : Coord → ℂ), 0 < c → MemLp u 2 (logMeas c) → MemLp g 2 (logMeas c) →
    LogWeak c u g → ∀ h : ℝ, ∀ᵐ x ∂(logMeas c),
      u (x.1 + h, x.2) - u x = ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)

/-- **Leaf `PartII-b:T15/2/10`** (averages of translates converge in `L²`; uses `T15/2/7`). For
`G ∈ L²(logMeas c)`, `‖h⁻¹ ∫_0^h G(· + σ, ·) dσ - G‖_{L²(λ)} → 0` as `h → 0`, `h ≠ 0`. Proof: for a.e.
`y`, `t ↦ G(t, y)` is in `L²(ℝ)`, hence locally integrable, so for a.e. `x` the inner integral is a
genuine integral and Jensen/Cauchy-Schwarz gives
`‖h⁻¹ ∫_0^h (G(x + σ) - G(x)) dσ‖² ≤ |h|⁻¹ |∫_0^h ‖G(x + σ) - G(x)‖² dσ|`; integrate in `x`
(Tonelli) to bound the squared norm by `sup_{|σ| ≤ |h|} ∫⁻ ‖G(· + σ) - G‖ₑ² dλ`, which tends to `0`
by `LogTranslateContinuous`. -/
def LogAvgConverges : Prop :=
  ∀ (c : ℝ) (G : Coord → ℂ), 0 < c → MemLp G 2 (logMeas c) →
    Tendsto (fun h : ℝ => ∫⁻ x, ‖(h⁻¹ : ℝ) • (∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2)) - G x‖ₑ ^ 2
      ∂(logMeas c)) (𝓝[≠] 0) (𝓝 0)

/-- **Leaf `PartII-b:T15/2/11`** (limit of the cross term; uses `T15/2/7`). If the difference
quotient `D_h = h⁻¹(u(· + h) - u)` converges to `G` in `L²(logMeas c)` and `ψ` is bounded and
continuous, then `∫ ψ D_h \overline{(u(· + h) + u)} dλ → 2 ∫ ψ G \bar u dλ`. Proof: split
`D_h \overline{u_h + u} - 2 G \bar u = (D_h - G)\overline{(u_h + u)} + G \overline{(u_h - u)}` with
`u_h = u(· + h)`; each pairing is bounded by `sup|ψ| · ‖·‖_{L²} ‖·‖_{L²}` (Cauchy-Schwarz /
`MemLp.integrable_mul`), `‖u_h + u‖_{L²} ≤ 2‖u‖_{L²}` (translation invariance) and
`‖u_h - u‖_{L²} → 0` by `LogTranslateContinuous`. -/
def LogCrossLimit : Prop :=
  ∀ (c : ℝ) (u G : Coord → ℂ), 0 < c → MemLp u 2 (logMeas c) → MemLp G 2 (logMeas c) →
    Tendsto (fun h : ℝ => ∫⁻ x, ‖(h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) - G x‖ₑ ^ 2 ∂(logMeas c))
      (𝓝[≠] 0) (𝓝 0) →
    ∀ ψ : Coord → ℝ, Continuous ψ → (∃ C : ℝ, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun h : ℝ => ∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
          (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ) ∂(logMeas c))
        (𝓝[≠] 0) (𝓝 (2 * ∫ x, G x * (starRingEnd ℂ) (u x) * (ψ x : ℂ) ∂(logMeas c)))

/-- **Leaf `PartII-b:T15/2/12`** (limit of the square term). For `u ∈ L²(logMeas c)` and a `LogTest ψ`,
`∫ ((ψ(t - h, y) - ψ(t, y))/h) ‖u‖² dλ → -∫ ∂_tψ ‖u‖² dλ` as `h → 0`, `h ≠ 0`. Proof: dominated
convergence (`tendsto_integral_filter_of_dominated_convergence`): the integrand converges pointwise
to `-∂_tψ ‖u‖²` (`HasDerivAt` of `t ↦ ψ(t, y)`, via `hasDerivAt_line`-type argument for `cpd 0`),
and is bounded by `sup|∂_tψ| ‖u‖²` (mean value theorem, `∂_tψ` is bounded because it is
continuous with compact `(t, η)`-support and `q`-periodic, so bounded on the compact cell
enlargement), which is integrable. -/
def LogSquareLimit : Prop :=
  ∀ (c : ℝ) (u : Coord → ℂ) (ψ : Coord → ℝ), 0 < c → MemLp u 2 (logMeas c) → LogTest c ψ →
    Tendsto (fun h : ℝ => ∫ x, ((ψ (x.1 - h, x.2) - ψ x) / h : ℝ) * ‖u x‖ ^ 2 ∂(logMeas c))
      (𝓝[≠] 0) (𝓝 (-∫ x, cpd 0 ψ x * ‖u x‖ ^ 2 ∂(logMeas c)))

/-- **Leaf `PartII-b:T15/2/13`** (scalar weak product rule in the logarithmic chart; uses
`T15/2/9`-`T15/2/12` and `T15/2/18`). For `u, g ∈ L²` with `LogWeak c u g` and a `LogTest ψ`:
`Re ∫ g \overline{ψ u} dλ = (1/4)∫ ψ ‖u‖² dλ - (1/2)∫ ∂_tψ ‖u‖² dλ`. Proof: let `G = g - u/4`
and `u_h = u(· + h)`. By `LogTranslationFormula` (`D_h = h⁻¹(u_h - u)` equals `h⁻¹ ∫_0^h G(· + σ)dσ`
a.e.) and `LogAvgConverges`, `D_h → G` in `L²`. Pointwise
`‖u_h‖² - ‖u‖² = Re((u_h - u)\overline{(u_h + u)})`, so
`Re ∫ ψ D_h \overline{(u_h + u)} → 2 Re ∫ ψ G \bar u` (`LogCrossLimit`), while by `LogSquareIdentity`
the same quantity equals `∫ ((ψ(t - h) - ψ(t))/h)‖u‖² dλ → -∫ ∂_tψ ‖u‖² dλ` (`LogSquareLimit`). Uniqueness of limits gives
`2 Re ∫ ψ G \bar u = -∫ ∂_tψ ‖u‖²`; finally `∫ ψ g \bar u = ∫ ψ G \bar u + (1/4)∫ ψ ‖u‖²`. -/
def LogProductRuleScalar : Prop :=
  ∀ (c : ℝ) (u g : Coord → ℂ), 0 < c → MemLp u 2 (logMeas c) → MemLp g 2 (logMeas c) →
    LogWeak c u g → ∀ ψ : Coord → ℝ, LogTest c ψ →
      (∫ x, g x * (starRingEnd ℂ) ((ψ x : ℂ) * u x) ∂(logMeas c)).re =
        (1 / 4) * ∫ x, ψ x * ‖u x‖ ^ 2 ∂(logMeas c) -
          (1 / 2) * ∫ x, cpd 0 ψ x * ‖u x‖ ^ 2 ∂(logMeas c)

/-- **Leaf `PartII-b:T15/2/14`** (vector form, sum over the two components; uses `T15/2/13`).
Proof: apply `LogProductRuleScalar` to each component and add; the integrands
`g_i \overline{ψ u_i}`, `ψ ‖u_i‖²`, `∂_tψ ‖u_i‖²` are integrable (Hölder for the product of two
`L²` functions, `MemLp.integrable_mul`; `ψ`, `∂_tψ` bounded with `(t, η)`-compact support), so
`integral_finset_sum` and `Complex.re_sum` apply. -/
def LogProductRule : Prop :=
  ∀ (c : ℝ) (u g : Coord → Fin 2 → ℂ), 0 < c →
    (∀ i, MemLp (fun x => u x i) 2 (logMeas c)) → (∀ i, MemLp (fun x => g x i) 2 (logMeas c)) →
    (∀ i, LogWeak c (fun x => u x i) (fun x => g x i)) →
    ∀ ψ : Coord → ℝ, LogTest c ψ →
      (∫ x, ∑ i : Fin 2, g x i * (starRingEnd ℂ) ((ψ x : ℂ) * u x i) ∂(logMeas c)).re =
        (1 / 4) * ∫ x, ψ x * ∑ i : Fin 2, ‖u x i‖ ^ 2 ∂(logMeas c) -
          (1 / 2) * ∫ x, cpd 0 ψ x * ∑ i : Fin 2, ‖u x i‖ ^ 2 ∂(logMeas c)

/-! ## Auxiliary leaves -/

/-- **Leaf `PartII-b:T15/2/15`** (periodization of a cell-supported test). If `ζ` is smooth with
compact support inside the open slab `ℝ × (-c/2, c/2) × ℝ`, then there is a `LogTest Φ` (the
`q`-periodization `Φ(t, q, η) = Σ_n ζ(t, q - nc, η)`) agreeing with `ζ` on the cell
`q ∈ [-c/2, c/2)`. Proof: the support of `ζ` lies in `|q| ≤ c/2 - δ`, so on `|q - q₀| < c/2` at most
two terms of the sum are non-zero (`Short/PartII-b/Tasks/FlatUnique/CellStream/Partition.lean`:
`CellPart.per`, `mem_window`, `term_zero_of_not_mem` do the same for functions of `q` alone);
smoothness is local (finite sums); periodicity is reindexing `n ↦ n + 1`; the `t` and `η` supports
are those of `ζ`. -/
def PeriodizeCellTest : Prop :=
  ∀ (c : ℝ) (ζ : Coord → ℝ), 0 < c → ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
    tsupport ζ ⊆ (univ : Set ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) →
    ∃ Φ : Coord → ℝ, LogTest c Φ ∧ ∀ x : Coord, x.2.1 ∈ Ico (-c / 2) (c / 2) → Φ x = ζ x

/-- **Leaf `PartII-b:T15/2/16`** (the weak identity at a translated test). For `u, g ∈ L²(logMeas c)`
with `LogWeak c u g`, every shift `σ` and `LogTest Φ`:
`∫ (g - u/4)(t + σ, y) Φ(t, y) dλ = -∫ u(t, y) (∂_tΦ)(t - σ, y) dλ`. Proof: `Φ_σ(x) = Φ(x.1 - σ, x.2)`
is a `LogTest` with `cpd 0 Φ_σ x = cpd 0 Φ (x.1 - σ, x.2)` (chain rule for the translation);
`λ` is invariant under `x ↦ (x.1 + σ, x.2)`
(`(measurePreserving_add_right volume σ).prod (MeasurePreserving.id _)`), so the left side is
`∫ (g - u/4) Φ_σ dλ`; apply `LogWeak` to `Φ_σ`, `∫ g Φ_σ = ∫ u (Φ_σ/4 - ∂_tΦ_σ)`, and subtract
`(1/4)∫ u Φ_σ`. All integrands are integrable: product of two `L²` functions or `L²` times a bounded
function (`MemLp.integrable_mul`; `Φ` is bounded with support in `{|t| ≤ T + |σ|, |η| ≤ L}` of finite
`λ`-measure). -/
def LogShiftTest : Prop :=
  ∀ (c : ℝ) (u g : Coord → ℂ), 0 < c → MemLp u 2 (logMeas c) → MemLp g 2 (logMeas c) →
    LogWeak c u g → ∀ (σ : ℝ) (Φ : Coord → ℝ), LogTest c Φ →
      ∫ x, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4) * (Φ x : ℂ) ∂(logMeas c) =
        -∫ x, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ) ∂(logMeas c)

/-- **Leaf `PartII-b:T15/2/17`** (local integrability of the translate-average). For
`G ∈ L²(logMeas c)` and any `h`, `x ↦ ∫_0^h G(t + σ, y) dσ` is a.e.-strongly measurable and
integrable on every `{|t| ≤ T, |η| ≤ L}`. Proof: take a strongly measurable representative of `G`
(null sets of `λ` pull back to null sets of `(σ, x) ↦ (x.1 + σ, x.2)` by Fubini, which does not
change the average for a.e. `x`); `(σ, x) ↦ G(x.1 + σ, x.2)` is measurable on `ℝ × Coord`, so
`StronglyMeasurable.integral_prod_right` gives measurability; for integrability on `K` (finite
`λ`-measure) bound `‖avg‖ ≤ ∫_{[0,h]} ‖G(x.1 + σ, x.2)‖ dσ` and use Tonelli and translation
invariance of `λ`: `∫_K ∫_{[0,h]} ‖G(x.1 + σ, x.2)‖ ≤ |h| ‖G‖_{L¹(K')}` with
`K' = {|t| ≤ T + |h|, |η| ≤ L}` of finite measure, `G ∈ L² ⊂ L¹(K')`. -/
def LogAvgLocInt : Prop :=
  ∀ (c : ℝ) (G : Coord → ℂ), 0 < c → MemLp G 2 (logMeas c) → ∀ h : ℝ,
    AEStronglyMeasurable (fun x : Coord => ∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2)) (logMeas c) ∧
    ∀ T L : ℝ, IntegrableOn (fun x : Coord => ∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2))
      {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c)

/-- **Leaf `PartII-b:T15/2/18`** (the exact identity behind the square term). For `u ∈ L²`, a
`LogTest ψ` and `h ≠ 0`, with `u_h = u(· + h, ·)`:
`Re ∫ ψ h⁻¹(u_h - u) \overline{(u_h + u)} dλ = ∫ ((ψ(t - h, y) - ψ(t, y))/h) ‖u‖² dλ`. Proof:
pointwise `Re((a - b)\overline{(a + b)}) = ‖a‖² - ‖b‖²` (the cross terms `a \bar b - b \bar a` are
purely imaginary), so the left side is `h⁻¹(∫ ψ ‖u_h‖² - ∫ ψ ‖u‖²)`; translation invariance of `λ`
gives `∫ ψ(x) ‖u(x.1 + h, x.2)‖² dλ = ∫ ψ(x.1 - h, x.2) ‖u‖² dλ`; `ψ ‖u‖²`, `ψ(· - h)‖u‖²` are
integrable (`ψ` bounded, `‖u‖²` integrable by `MemLp`, `memLp_two_iff_integrable_sq_norm`). -/
def LogSquareIdentity : Prop :=
  ∀ (c : ℝ) (u : Coord → ℂ) (ψ : Coord → ℝ), 0 < c → MemLp u 2 (logMeas c) → LogTest c ψ →
    ∀ h : ℝ, h ≠ 0 →
      (∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
          (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ) ∂(logMeas c)).re =
        ∫ x, ((ψ (x.1 - h, x.2) - ψ x) / h : ℝ) * ‖u x‖ ^ 2 ∂(logMeas c)

/-- **Leaf `PartII-b:T15/2/19`** (basic bounds for logarithmic tests; used by `T15/2/8`, `/12`, `/13`,
`/14`, `/16`, `/18`). A `LogTest Φ` and its `t`-derivative are bounded, and pair integrably with every
`L²(logMeas c)` function. Proof: `Φ` vanishes for `|t| > T` or `|η| > L`; it is `c`-periodic in `q`
(`Φ (qShift c x) = Φ x`), so `Φ` and `cpd 0 Φ` (which is continuous, `ContDiff.continuous_fderiv`,
and again `q`-periodic and supported in the same box) are determined by their values on the compact
box `[-T, T] × [-c/2, c/2] × [-L, L]`: reduce `q` into the cell with `Int.fract`-type arithmetic or
`Function.Periodic`, use `IsCompact.exists_bound_of_continuousOn`. For integrability, the support of
the product lies in the box `{|t| ≤ T, |η| ≤ L}`, which has finite `logMeas c`-measure
(`volume (Icc (-T) T) * ofReal c⁻¹ * volume (Icc (-L) L)`-type computation, `Measure.prod_prod`,
`Measure.restrict_apply`); on this set a function in `L²` is in `L¹` (`MemLp.integrableOn`-type /
Cauchy-Schwarz with the constant `1`), and `Integrable.bdd_mul` handles the bounded factor. -/
def LogTestBounds : Prop :=
  ∀ (c : ℝ) (Φ : Coord → ℝ), 0 < c → LogTest c Φ →
    (∃ C : ℝ, ∀ x, |Φ x| ≤ C) ∧ (∃ C : ℝ, ∀ x, |cpd 0 Φ x| ≤ C) ∧
    (∀ f : Coord → ℂ, MemLp f 2 (logMeas c) →
      Integrable (fun x => f x * (Φ x : ℂ)) (logMeas c) ∧
        Integrable (fun x => f x * ((cpd 0 Φ x : ℝ) : ℂ)) (logMeas c))

/-! ## Assembly -/

/-- **Conditional weak product rule** (`PartII-b:T15/2`): pull the vector product rule in the
logarithmic chart back along `E(t, y) = (e^t, y)`. -/
theorem weakProductRuleH2_of (h1 : ExpChartIntegral) (h2 : LogUMemLp) (h3 : LogTestOfOrig)
    (h5 : LogWeakTransfer) (h14 : LogProductRule) : WeakProductRuleH2 := by
  intro c w Sw hc hw hSw hP ψ hψ hper hsupp
  have hμ : hMeas c 2 = Axi.ageμ c (-3 / 2) := by
    unfold hMeas
    congr 1
    norm_num
  obtain ⟨hlt, hder⟩ := h3 c ψ hψ hper hsupp
  have hwk := h5 c w Sw hc hP
  have hcore := h14 c (fun x i => logU w i x) (fun x i => logU Sw i x) hc
    (fun i => h2 c w hc hw i) (fun i => h2 c Sw hc hSw i) hwk
    (fun x => ψ (Real.exp x.1, x.2)) hlt
  obtain ⟨-, hR, hC⟩ := h1 c (-3 / 2) hc
  have hexp : ∀ x : Coord, Real.exp (-x.1 / 4) * Real.exp (-x.1 / 4) =
      Real.exp ((-3 / 2 + 1) * x.1) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : ∀ (x : Coord) (i : Fin 2), ‖logU w i x‖ ^ 2 =
      Real.exp ((-3 / 2 + 1) * x.1) * ‖w (Real.exp x.1, x.2) i‖ ^ 2 := by
    intro x i
    simp only [logU, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [mul_pow, sq, hexp x]
  have hsum : ∀ x : Coord, ∑ i : Fin 2, ‖logU w i x‖ ^ 2 =
      Real.exp ((-3 / 2 + 1) * x.1) * ∑ i : Fin 2, ‖w (Real.exp x.1, x.2) i‖ ^ 2 := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hs x i
  have p1 : ∀ x : Coord, ((Real.exp ((-3 / 2 + 1) * x.1) : ℝ) : ℂ) *
      ∑ i : Fin 2, Sw (Real.exp x.1, x.2) i *
        (starRingEnd ℂ) (((ψ (Real.exp x.1, x.2) : ℝ) : ℂ) * w (Real.exp x.1, x.2) i) =
      ∑ i : Fin 2, logU Sw i x *
        (starRingEnd ℂ) (((ψ (Real.exp x.1, x.2) : ℝ) : ℂ) * logU w i x) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [logU, map_mul, Complex.conj_ofReal]
    rw [← hexp x]
    push_cast
    ring
  have p2 : ∀ x : Coord, Real.exp ((-3 / 2 + 1) * x.1) *
      (ψ (Real.exp x.1, x.2) * ∑ i : Fin 2, ‖w (Real.exp x.1, x.2) i‖ ^ 2) =
      ψ (Real.exp x.1, x.2) * ∑ i : Fin 2, ‖logU w i x‖ ^ 2 := by
    intro x
    rw [hsum x]
    ring
  have p3 : ∀ x : Coord, Real.exp ((-3 / 2 + 1) * x.1) *
      (Real.exp x.1 * cpd 0 ψ (Real.exp x.1, x.2) *
        ∑ i : Fin 2, ‖w (Real.exp x.1, x.2) i‖ ^ 2) =
      cpd 0 (fun y : Coord => ψ (Real.exp y.1, y.2)) x * ∑ i : Fin 2, ‖logU w i x‖ ^ 2 := by
    intro x
    rw [hsum x, hder x]
    ring
  rw [hμ, hC, hR, hR]
  simp only [p1, p2, p3]
  exact hcore

end UnforcedLeray.Short.IIb
