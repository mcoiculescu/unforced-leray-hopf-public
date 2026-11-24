import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: the Biot-Savart law of the train (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 261-266
(`v = ∇^⊥ψ` with decaying stream), 270-288 (the `BUC` train, smooth for positive time; zero
circulation; `v(-q,-η,s) = -v(q,η,s)`), 2081-2084 (`E_c = curl v_c`; `K_c` includes the horizontal
mean mode), 2117-2121 (the cylinder kernel is bounded away from its common local `1/|x - y|`
singularity), 3052-3057 (integrable near part, bounded far part, horizontal mean), 3121 (`K_d` is
the cylindrical Biot-Savart operator).

## The target

`TjTrainBSRep m` (`Train/Defs.lean`): for `0 < ν ≤ 1`, `c = ν⁻²`, a `BUC` train with the bounds
`LadTrainBdd` satisfies `v(ρ) = K_c E(ρ)` on `[0, ∞) × ℝ²` (`K_c = Cyl.K c`, the convolution over
the centred cell with the periodic kernel `Cyl.bsKernel c`, velocity `(Re, -Im)` of
`(2πi)⁻¹(π/c)cot(πz/c)`).

## The route (at a fixed age `ρ ≥ 0`, `ω = E(ρ)`, `u = K_cω`, `c ≥ 1`)

1. `ω` is `C^∞`, `c`-periodic, even (`B0238.Ec_even`), and `ω`, `Dω` decay with the weight
   `(1 + x₂²)^{(m+1)/2}` (`TjVortDecay`, `TjLadGrad`, `BsrFDerivNorm`).
2. **`u` is differentiable, `div u = 0`, `curl u = ω`** (`BsrKcDivCurl`, proved in `Assembly.lean`
   from `BsrWeightIntShift`, `BsrKcHasFDeriv`, `BsrKcFDerivEval`, `BsrKerPointwiseDecay`): the
   derivative passes under the centred integral (`∂_j u = K_c(∂_jω)`), and the identities
   `K_c(∂_qω)_q + K_c(∂_ηω)_η = 0`, `K_c(∂_qω)_η - K_c(∂_ηω)_q = ω` are, after `K_c(x - y) =
   -K_c(y - x)`, the proved pointwise kernel identities `KerDivPointwise`, `KerCurlPointwise`
   (`K_d = ∇^⊥G_d`, `ΔG_d = Σ_n δ_{(nd, 0)}`, tested against cylinder tests), extended from tests to
   decaying `ω` by cutoffs in `η` (`BsrCutoffApprox`) and dominated convergence
   (`BsrKerPointwiseDecay`, dominator from `BsrWeightIntShift`).
3. `w = v(ρ) - u` is bounded (`IsBUCTrain`, `TjKcBound`), differentiable, divergence free
   (`IsTrain.solenoidal`) and curl free (`E = curl v`), so `w₁ - iw₂` is a bounded entire function
   and `w` is constant (`BsrLiouville`).
4. `v(ρ)` is odd (`IsTrain.odd`, SP 286-288) and `u` is odd (`BsrKcOdd`: `ω` even, the kernel odd),
   so `w(0) = 0` and `w = 0`.

The leaves are manuscript-independent facts about the cylinder kernel and plane calculus.

## Status (all compiled, axioms `propext`, `Classical.choice`, `Quot.sound`)

Every leaf of this file is proved in `BSRep/`: `bsrFDerivNorm`, `bsrLiouville`, `bsrKcOdd`,
`bsrWeightIntShift_of`, `bsrKcFDerivEval_of` (`Proved.lean`), `bsrCutoffApprox` (`Cutoff.lean`),
`bsrKerPointwiseDecay_of` (`Pointwise.lean`), `bsrWeightInt` (`WeightInt.lean`),
`bsrKcHasFDeriv_of` (`HasFDeriv.lean`); `bsrKcDivCurl_of`, `tjTrainBSRep_of` (`Assembly.lean`).
`tjTrainBSRep_of_trainLeaves` (`Final.lean`) proves `TjTrainBSRep m` from the train leaves
`TjTrainVort`, `TjLadGrad m`, `TjDecayOfGrad`, `TjCirculationBdd`, `TjKcBound` of `Train/Defs.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Leaves: calculus -/

/-- **The operator norm of a planar derivative by its partials** (calculus): for `f` differentiable
at `y`, `‖Df(y)‖ ≤ |∂_q f(y)| + |∂_η f(y)|` (`ℝ × ℝ` carries the sup norm; `Df(y)(h₁, h₂) =
h₁ ∂_q f(y) + h₂ ∂_η f(y)` and `|h_i| ≤ ‖h‖`). -/
def BsrFDerivNorm : Prop :=
  ∀ (f : ℝ × ℝ → ℝ) (y : ℝ × ℝ), DifferentiableAt ℝ f y →
    ‖fderiv ℝ f y‖ ≤ |UnforcedLeray.Cyl.partialQ f y| + |UnforcedLeray.Cyl.partialEta f y|

/-- **Liouville for bounded divergence- and curl-free fields** (complex analysis; step 3 of the
route): a differentiable bounded field `w` on the plane with `div w = ∂_q w₁ + ∂_η w₂ = 0` and
`curl w = ∂_q w₂ - ∂_η w₁ = 0` everywhere is constant. (`F(q + iη) = w₁(q, η) - i w₂(q, η)` is
`ℝ`-differentiable and its real derivative is `ℂ`-linear by the Cauchy-Riemann equations
`∂_q w₁ = -∂_η w₂`, `∂_η w₁ = ∂_q w₂`, so `F` is entire (`differentiableAt_iff_restrictScalars`);
it is bounded, hence constant (`Differentiable.apply_eq_apply_of_bounded`).) -/
def BsrLiouville : Prop :=
  ∀ w : ℝ × ℝ → UnforcedLeray.Cyl.Vec2, Differentiable ℝ w →
    (∀ x : ℝ × ℝ, UnforcedLeray.Cyl.divergence w x = 0) →
    (∀ x : ℝ × ℝ, UnforcedLeray.Cyl.curl w x = 0) →
    (∃ M : ℝ, ∀ x : ℝ × ℝ, ‖w x‖ ≤ M) → ∀ x y : ℝ × ℝ, w x = w y

/-- **Cylinder tests approximating a smooth periodic field** (calculus; the cutoff of step 2): for
`φ` `C^∞` and `d`-periodic in `q` there are cylinder tests `ψ n` (e.g. `ψ n x = φ x χ(x₂/(n+1))`,
`χ` a smooth bump equal to `1` on `[-1, 1]` and `0` off `(-2, 2)`) that agree with `φ` together with
their first partials at every fixed `x` for large `n`, with `|∂_j ψ n| ≤ ‖Dφ‖ + K|φ|` uniformly
(`K = sup |χ'|`). -/
def BsrCutoffApprox : Prop :=
  ∀ (d : ℝ) (φ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ φ → (∀ x : ℝ × ℝ, φ (x.1 + d, x.2) = φ x) →
    ∃ (ψ : ℕ → ℝ × ℝ → ℝ) (K : ℝ), 0 ≤ K ∧ (∀ n : ℕ, B0579.IsCylTest d (ψ n)) ∧
      (∀ x : ℝ × ℝ, ∀ᶠ n in atTop,
        ψ n x = φ x ∧ ∀ j : Fin 2, B0579.pd j (ψ n) x = B0579.pd j φ x) ∧
      (∀ (n : ℕ) (j : Fin 2) (x : ℝ × ℝ), |B0579.pd j (ψ n) x| ≤ ‖fderiv ℝ φ x‖ + K * |φ x|)

/-! ## Leaves: the cylinder kernel (SP 2081-2084, 2117-2121, 3052-3057, 3121) -/

/-- **The kernel against a transverse weight is integrable on the cell** (SP 2117-2121, 3052-3057:
integrable near part, bounded far part; `Cyl.bsKernel_split`: on the cell `K_c = k_near + k_far`,
`∫_cell |k_near| ≤ C`, `|k_far| ≤ 2`, for `c ≥ 1`): for `c ≥ 1`, `β > 1` and every `a`,
`y ↦ (1 + (a - y₂)²)^{-β/2} ‖K_c(y)‖` is integrable on the centred cell (the weight is `≤ 1` on the
near part; on the far part `∫_cell (1 + (a - y₂)²)^{-β/2} dy = c ∫_ℝ (1 + s²)^{-β/2} ds < ∞`). -/
def BsrWeightInt : Prop :=
  ∀ c β : ℝ, 1 ≤ c → 1 < β → ∀ a : ℝ,
    IntegrableOn (fun y : ℝ × ℝ => (1 + (a - y.2) ^ 2) ^ (-(β / 2)) *
      ‖UnforcedLeray.Cyl.bsKernel c y‖) (UnforcedLeray.Cyl.cell c)

/-- **The shifted form of `BsrWeightInt`**: for `c ≥ 1`, `β > 1` and every `x`,
`y ↦ (1 + y₂²)^{-β/2} ‖K_c(y - x)‖` is integrable on the centred cell. (The integrand is
`c`-periodic in `y₁`; `Cyl.lintegral_cell_comp_sub_left` turns its cell integral into that of
`y ↦ (1 + (x₂ - y₂)²)^{-β/2} ‖K_c(-y)‖`, and `‖K_c(-y)‖ = ‖K_c(y)‖`: the kernel is odd.) -/
def BsrWeightIntShift : Prop :=
  ∀ c β : ℝ, 1 ≤ c → 1 < β → ∀ x : ℝ × ℝ,
    IntegrableOn (fun y : ℝ × ℝ => (1 + y.2 ^ 2) ^ (-(β / 2)) *
      ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖) (UnforcedLeray.Cyl.cell c)

/-- **The derivative passes under the centred integral** (measure theory; SP 2081-2084, 3052-3057):
for `c ≥ 1`, `β > 1` and `ω` `C¹`, `c`-periodic, with `(1 + y₂²)^{β/2}|ω(y)| ≤ A` and
`(1 + y₂²)^{β/2}‖Dω(y)‖ ≤ A`, `K_cω` has at every `x` the Fréchet derivative
`∫_cell Dω(x - y) ⊗ K_c(y) dy`. (`Cyl.K_eq_reflect`: `K_cω(z) = ∫_cell ω(z - y) K_c(y) dy`;
`hasFDerivAt_integral_of_dominated_of_fderiv_le` on `Metric.ball x 1`, dominated by
`A 3^{β/2}(1 + (x₂ - y₂)²)^{-β/2}‖K_c(y)‖`, integrable by `BsrWeightInt` with `a = x₂`.) -/
def BsrKcHasFDeriv : Prop :=
  ∀ c β A : ℝ, 1 ≤ c → 1 < β → ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ 1 g →
    UnforcedLeray.Cyl.IsPeriodic c g →
    (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * |g y| ≤ A) →
    (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * ‖fderiv ℝ g y‖ ≤ A) →
    ∀ x : ℝ × ℝ, HasFDerivAt (UnforcedLeray.Cyl.K c g)
      (∫ y in UnforcedLeray.Cyl.cell c,
        (fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y)) x

/-- **The partial derivatives of `K_cω` are `K_c` of the partials** (measure theory): the derivative
of `BsrKcHasFDeriv` evaluated at `e_q = (1, 0)`, `e_η = (0, 1)` is `K_c(∂_qω)(x)`, `K_c(∂_ηω)(x)`.
(`ContinuousLinearMap.integral_apply`, the integrand being integrable by the weighted bound of `Dω`
and `BsrWeightInt`; `(L.smulRight v) h = L h • v`; `Dω(z)(1, 0) = ∂_qω(z)`
(`Cyl.partialQ_eq_fderiv`); `Cyl.K_eq_reflect` for the `c`-periodic `∂_qω`, `∂_ηω`.) -/
def BsrKcFDerivEval : Prop :=
  ∀ c β A : ℝ, 1 ≤ c → 1 < β → ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ 1 g →
    UnforcedLeray.Cyl.IsPeriodic c g →
    (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * ‖fderiv ℝ g y‖ ≤ A) →
    ∀ x : ℝ × ℝ,
      (∫ y in UnforcedLeray.Cyl.cell c,
          (fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y)) (1, 0) =
        UnforcedLeray.Cyl.K c (UnforcedLeray.Cyl.partialQ g) x ∧
      (∫ y in UnforcedLeray.Cyl.cell c,
          (fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y)) (0, 1) =
        UnforcedLeray.Cyl.K c (UnforcedLeray.Cyl.partialEta g) x

/-- **The pointwise kernel identities for decaying fields** (SP 2081-2084, 3121: `K_d = ∇^⊥G_d`,
`ΔG_d = Σ_n δ_{(nd, 0)}`): the identities `KerDivPointwise`, `KerCurlPointwise` (`T21_2_1/KernelDefs`,
proved for cylinder tests: `kerDivPointwise_of kerNearFar`, `kerCurlPointwise_of kerNearFar`) hold
for every `C^∞`, `d`-periodic `φ` with `(1 + x₂²)^{β/2}|φ|, (1 + x₂²)^{β/2}‖Dφ‖ ≤ A`, `β > 1`:
`∫_{C_d} K_d(x - y)·∇φ(x) dx = 0` and `∫_{C_d} (K_d(x - y)_q ∂_ηφ(x) - K_d(x - y)_η ∂_qφ(x)) dx =
φ(y)`. (Apply them to the tests of `BsrCutoffApprox` and pass to the limit by dominated convergence:
the integrands are eventually equal pointwise and dominated by
`2(1 + K)A(1 + x₂²)^{-β/2}‖K_d(x - y)‖`, integrable by `BsrWeightIntShift`.) -/
def BsrKerPointwiseDecay : Prop :=
  ∀ d β A : ℝ, 1 ≤ d → 1 < β → ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ →
    (∀ x : ℝ × ℝ, φ (x.1 + d, x.2) = φ x) →
    (∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |φ x| ≤ A) →
    (∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * ‖fderiv ℝ φ x‖ ≤ A) →
    ∀ y : ℝ × ℝ,
      (∫ x in B0579.cell d,
          (kerD d (x - y) 0 * B0579.pd 0 φ x + kerD d (x - y) 1 * B0579.pd 1 φ x)) = 0 ∧
      (∫ x in B0579.cell d,
          (kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x)) = φ y

/-- **`K_c` of an even periodic field is odd** (SP 286-288: the train is centrally odd, its
vorticity even): for `c > 0`, `ω` `c`-periodic and even, `K_cω(-x) = -K_cω(x)`. (`Cyl.K_eq_reflect`
and evenness give `K_cω(-x) = ∫_cell ω(x + y) K_c(y) dy`; `Cyl.integral_cell_comp_sub_left` at the
point `0` for the `c`-periodic `y ↦ ω(x + y) K_c(y)` and `K_c(-y) = -K_c(y)` turn this into
`-∫_cell ω(x - y) K_c(y) dy`.) -/
def BsrKcOdd : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g : ℝ × ℝ → ℝ, UnforcedLeray.Cyl.IsPeriodic c g →
    (∀ y : ℝ × ℝ, g (-y) = g y) → ∀ x : ℝ × ℝ,
      UnforcedLeray.Cyl.K c g (-x) = -UnforcedLeray.Cyl.K c g x

/-! ## Intermediate statement (proved in `Assembly.lean`) -/

/-- **`K_cω` is differentiable, divergence free, with curl `ω`** (step 2 of the route;
`bsrKcDivCurl_of`). -/
def BsrKcDivCurl : Prop :=
  ∀ c β A : ℝ, 1 ≤ c → 1 < β → ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g →
    UnforcedLeray.Cyl.IsPeriodic c g →
    (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * |g y| ≤ A) →
    (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * ‖fderiv ℝ g y‖ ≤ A) →
    Differentiable ℝ (UnforcedLeray.Cyl.K c g) ∧
      ∀ x : ℝ × ℝ, UnforcedLeray.Cyl.divergence (UnforcedLeray.Cyl.K c g) x = 0 ∧
        UnforcedLeray.Cyl.curl (UnforcedLeray.Cyl.K c g) x = g x

end UnforcedLeray.Short.IIIa
