import UnforcedLeray.Short.PartIIb.Sub.T22_1.Plan

/-!
# Stages of the plan for `PartII-b:T22/1`: the heat toolbox and the Duhamel convolution

Statements only (each is `def ... : Prop`, to be proved by the task named in its docstring; see
`Plan.lean` for the reduction `cylClassicalExists_of_parts` and the mathematics). Source of record:
`the November 2 reference manuscript`, lines 2074-2093 and 2103-2105 (the cylinder
equation and "smoothing"); the statements are standard heat-kernel calculus.

Conventions: `Pl = ℝ × ℝ`, `heatK a` the Gaussian kernel of `e^{aΔ}`, `heatSG a g = K_a * g`
(`a > 0`; the identity for `a ≤ 0`), `heatSGd i a g = (∂_i K_a) * g`, `WB B g` means
`|g| cosh η ≤ B`, `W2 g x = |g| + |∇g| + |∇²g|`. Everything is pointwise in the plane variable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-! ## The heat toolbox (tasks `T22/1/3` - `T22/1/9`) -/

/-- **`T22/1/3`** Gaussian moments. For `a > 0`: `K_a > 0` is integrable with integral `1`;
`∫ K_a(z) cosh z₂ dz = e^a` (`z₂ ~ N(0, 2a)`); and the derivative kernel has
`∫ |∂_i K_a(z)| cosh z₂ dz ≤ e^a (1 + a^{-1/2})` (exactly `e^a/√(πa)` for `i = 0` and
`e^a (1/√(πa) + 1)` for `i = 1`). -/
def HeatKernelMoments : Prop := ∀ a : ℝ, 0 < a →
  (∀ z : Pl, 0 < heatK a z) ∧ Integrable (heatK a) ∧ (∫ z : Pl, heatK a z) = 1 ∧
  Integrable (fun z : Pl => heatK a z * Real.cosh z.2) ∧
  (∫ z : Pl, heatK a z * Real.cosh z.2) = Real.exp a ∧
  ∀ i : Fin 2, Integrable (fun z : Pl => |heatKd i a z| * Real.cosh z.2) ∧
    (∫ z : Pl, |heatKd i a z| * Real.cosh z.2) ≤ Real.exp a * (1 + a ^ (-(1 / 2 : ℝ)))

/-- **`T22/1/4`** The heat semigroup and the derivative kernel preserve the weight `cosh η`:
`|e^{aΔ} g| cosh η ≤ 2 e^a B` for `a ≥ 0` and
`|(∂_i K_a) * g| cosh η ≤ 2 e^a (1 + a^{-1/2}) B` for `a > 0`, when `|g| cosh η ≤ B`
(from `cosh(x₂) ≤ 2 cosh(x₂ - y₂) cosh(y₂)`, and `HeatKernelMoments`). No measurability of `g` is
assumed: a non-integrable integral is `0` in Lean and the bound is trivial there. -/
def HeatWBounds : Prop := ∀ (B : ℝ) (g : Pl → ℝ), WB B g →
  (∀ a : ℝ, 0 ≤ a → ∀ x : Pl, |heatSG a g x| * Real.cosh x.2 ≤ 2 * Real.exp a * B) ∧
  (∀ a : ℝ, 0 < a → ∀ (i : Fin 2) (x : Pl),
    |heatSGd i a g x| * Real.cosh x.2 ≤ 2 * Real.exp a * (1 + a ^ (-(1 / 2 : ℝ))) * B)

/-- **`T22/1/5`** `q`-periodicity is preserved (translation invariance of Lebesgue measure). -/
def HeatPeriodic : Prop := ∀ (c : ℝ) (g : Pl → ℝ), (∀ x : Pl, g (x.1 + c, x.2) = g x) →
  ∀ (a : ℝ) (x : Pl), heatSG a g (x.1 + c, x.2) = heatSG a g x ∧
    ∀ i : Fin 2, heatSGd i a g (x.1 + c, x.2) = heatSGd i a g x

/-- **`T22/1/6`** Differentiation under the integral sign: for `a > 0` and `g` continuous with
`|g| cosh η ≤ B`, `e^{aΔ} g` is differentiable, `∂_i (K_a * g) = (∂_i K_a) * g`, and the latter is
continuous. -/
def HeatGradFormula : Prop := ∀ (B : ℝ) (g : Pl → ℝ), Continuous g → WB B g → ∀ a : ℝ, 0 < a →
  Differentiable ℝ (heatSG a g) ∧
    (∀ (i : Fin 2) (x : Pl), B0579.pd i (heatSG a g) x = heatSGd i a g x) ∧
    ∀ i : Fin 2, Continuous (heatSGd i a g)

/-- **`T22/1/7`** Derivatives commute with the semigroup: for `g ∈ C¹` with `g` and `∇g` bounded in
the weight, `∂_j (e^{aΔ} g) = e^{aΔ} (∂_j g)` (integration by parts against `∂_j K_a`, no boundary
term by the decay of `g`). -/
def HeatCommute : Prop := ∀ (B : ℝ) (g : Pl → ℝ), ContDiff ℝ 1 g → WB B g →
  (∀ j : Fin 2, WB B (B0579.pd j g)) →
  ∀ (a : ℝ) (j : Fin 2) (x : Pl), B0579.pd j (heatSG a g) x = heatSG a (B0579.pd j g) x

/-- **`T22/1/8`** The heat equation in the time variable `a`, for `g ∈ C²` with `g`, `∇g`, `∇²g`
bounded in the weight: `∂_a (e^{aΔ} g)(x) = (e^{aΔ} Δg)(x)` for `a > 0` (two-sided), and the right
derivative at `a = 0` is `Δg(x)`. -/
def HeatEqn : Prop := ∀ (B : ℝ) (g : Pl → ℝ), ContDiff ℝ 2 g → WB B g →
  (∀ j : Fin 2, WB B (B0579.pd j g)) → (∀ i j : Fin 2, WB B (B0579.pd i (B0579.pd j g))) →
  ∀ x : Pl,
    (∀ a : ℝ, 0 < a → HasDerivAt (fun b => heatSG b g x) (heatSG a (lapP g) x) a) ∧
      HasDerivWithinAt (fun b => heatSG b g x) (lapP g x) (Ici 0) 0

/-- **`T22/1/9`** Joint continuity of `(a, x) ↦ e^{aΔ} g (x)` on `[0, ∞) × Pl` for `g` continuous
and weighted-bounded (including `a = 0`, approximate identity). -/
def HeatCont : Prop := ∀ (B : ℝ) (g : Pl → ℝ), Continuous g → WB B g →
  ContinuousOn (fun z : ℝ × Pl => heatSG z.1 g z.2) (Ici 0 ×ˢ univ)

/-! ## The Duhamel convolution (tasks `T22/1/10`, `T22/1/11`) -/

/-- **`T22/1/10`** Spatial regularity and size of `G(τ) = ∫_s^τ e^{ν(τ-r)Δ} F(r) dr`. There is
`K ≥ 0`, depending only on `ν` and `T - s` (`K = 2 e^{ν(T-s)} (7 + 6 ν^{-1/2})` works), such that for
every `F` of class `FReg` with `|F(r)| cosh η ≤ b(r)`, `|∇F(r)| cosh η ≤ b(r)` for a continuous
`b ≥ 0` on `[s, T]`:
* `G(τ) ∈ C²`, `∂_i G(τ) = ∫ (∂_i K_{ν(τ-r)}) * F(r) dr`,
  `∂_i∂_j G(τ) = ∫ (∂_i K_{ν(τ-r)}) * ∂_j F(r) dr`;
* `G`, `∇G`, `∇²G` are jointly continuous in `(τ, x)` on `[s, T] × Pl`;
* `G(τ)` is `c`-periodic whenever every `F(r)` is;
* `W2(G(τ)) cosh η ≤ K ∫_s^τ (1 + (τ - r)^{-1/2}) b(r) dr`. -/
def ConvRegular : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ → Pl → ℝ), FReg s T F → ∀ b : ℝ → ℝ, ContinuousOn b (Icc s T) →
    (∀ r ∈ Icc s T, 0 ≤ b r) →
    (∀ r ∈ Icc s T, WB (b r) (F r) ∧ ∀ j : Fin 2, WB (b r) (B0579.pd j (F r))) →
    (∀ τ ∈ Icc s T,
      ContDiff ℝ 2 (duhamelConv ν s F τ) ∧
      (∀ (i : Fin 2) (x : Pl), B0579.pd i (duhamelConv ν s F τ) x =
        ∫ r in s..τ, heatSGd i (ν * (τ - r)) (F r) x) ∧
      (∀ (i j : Fin 2) (x : Pl), B0579.pd i (B0579.pd j (duhamelConv ν s F τ)) x =
        ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd j (F r)) x)) ∧
    ContinuousOn (fun z : ℝ × Pl => duhamelConv ν s F z.1 z.2) (Icc s T ×ˢ univ) ∧
    (∀ j : Fin 2, ContinuousOn (fun z : ℝ × Pl => B0579.pd j (duhamelConv ν s F z.1) z.2)
      (Icc s T ×ˢ univ)) ∧
    (∀ i j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (duhamelConv ν s F z.1)) z.2) (Icc s T ×ˢ univ)) ∧
    (∀ c : ℝ, (∀ r ∈ Icc s T, ∀ y : Pl, F r (y.1 + c, y.2) = F r y) →
      ∀ τ ∈ Icc s T, ∀ x : Pl, duhamelConv ν s F τ (x.1 + c, x.2) = duhamelConv ν s F τ x) ∧
    (∀ τ ∈ Icc s T, ∀ x : Pl, W2 (duhamelConv ν s F τ) x * Real.cosh x.2 ≤
      K * ∫ r in s..τ, (1 + (τ - r) ^ (-(1 / 2 : ℝ))) * b r)

/-- **`T22/1/11`** The time derivative of the Duhamel convolution: for `F` of class `FReg` with
`|F| cosh η, |∇F| cosh η ≤ B`,
`∂_τ G(τ)(x) = F(τ)(x) + ν Σ_i ∫_s^τ ((∂_i K_{ν(τ-r)}) * ∂_i F(r))(x) dr`
(= `F(τ) + ν Δ G(τ)` by `ConvRegular`), one-sided within `[s, T]`. The singularity
`(τ - r)^{-1/2}` of the kernel is integrable and the difference quotient of the kernel
`(K_{a+h} - K_a)/h = νΔ ∫...` is dominated by it. -/
def ConvTimeDeriv : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, HasDerivWithinAt (fun t => duhamelConv ν s F t x)
      (F τ x + ν * ∑ i : Fin 2, ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x)
      (Icc s T) τ

/-! ## The free part and the transport term (tasks `T22/1/12`, `T22/1/13`) -/

/-- **`T22/1/12`** The free evolution `σ ↦ e^{ν(σ-s)Δ} f` of a cylinder test function `f`: `C²`,
periodic, derivatives commute with the semigroup, jointly continuous with first and second
derivatives, bounded in `W2 · cosh` uniformly on `[s, T]`, and solves the heat equation in `σ`
(one-sided within `[s, T]`). Requires `0 < c` (for `c = 0` the test function `q² φ(η)` is not
bounded in `W2 · cosh`). -/
def FreePart : Prop := ∀ (c ν s T : ℝ) (f : Pl → ℝ), 0 < c → 0 < ν → s ≤ T → B0579.IsCylTest c f →
  (∀ σ ∈ Icc s T, ContDiff ℝ 2 (heatSG (ν * (σ - s)) f)) ∧
  (∀ σ ∈ Icc s T, ∀ x : Pl,
    heatSG (ν * (σ - s)) f (x.1 + c, x.2) = heatSG (ν * (σ - s)) f x) ∧
  (∀ σ ∈ Icc s T, ∀ (j : Fin 2) (x : Pl),
    B0579.pd j (heatSG (ν * (σ - s)) f) x = heatSG (ν * (σ - s)) (B0579.pd j f) x) ∧
  (∀ σ ∈ Icc s T, ∀ (i j : Fin 2) (x : Pl),
    B0579.pd i (B0579.pd j (heatSG (ν * (σ - s)) f)) x =
      heatSG (ν * (σ - s)) (B0579.pd i (B0579.pd j f)) x) ∧
  ContinuousOn (fun z : ℝ × Pl => heatSG (ν * (z.1 - s)) f z.2) (Icc s T ×ˢ univ) ∧
  (∀ j : Fin 2, ContinuousOn
    (fun z : ℝ × Pl => B0579.pd j (heatSG (ν * (z.1 - s)) f) z.2) (Icc s T ×ˢ univ)) ∧
  (∀ i j : Fin 2, ContinuousOn
    (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (heatSG (ν * (z.1 - s)) f)) z.2)
    (Icc s T ×ˢ univ)) ∧
  (∃ B : ℝ, ∀ σ ∈ Icc s T, ∀ x : Pl,
    W2 (heatSG (ν * (σ - s)) f) x * Real.cosh x.2 ≤ B) ∧
  (∀ σ ∈ Icc s T, ∀ x : Pl, HasDerivWithinAt (fun t => heatSG (ν * (t - s)) f x)
    (ν * lapP (heatSG (ν * (σ - s)) f) x) (Icc s T) σ)

/-- **`T22/1/13`** The transport term `F = v·∇u` of a `C²` family `u` with
`W2(u(σ)) cosh η ≤ b(σ)` is an integrand of class `FReg` with `|F| cosh η, |∇F| cosh η ≤ K b`,
`K = 2(M + M₁)` for `|v| ≤ M`, `|Dv| ≤ M₁` (`∂_j(v_k ∂_k u) = ∂_j v_k ∂_k u + v_k ∂_j∂_k u`). -/
def TranspClass : Prop := ∀ (c s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec),
  CylCoeff c T v → 0 ≤ s → s ≤ T → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (u : ℝ → Pl → ℝ) (b : ℝ → ℝ),
      (∀ σ ∈ Icc s T, ContDiff ℝ 2 (u σ)) →
      ContinuousOn (fun z : ℝ × Pl => u z.1 z.2) (Icc s T ×ˢ univ) →
      (∀ j : Fin 2, ContinuousOn (fun z : ℝ × Pl => B0579.pd j (u z.1) z.2) (Icc s T ×ˢ univ)) →
      (∀ i j : Fin 2, ContinuousOn
        (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (u z.1)) z.2) (Icc s T ×ˢ univ)) →
      (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (u σ) x * Real.cosh x.2 ≤ b σ) →
      FReg s T (transp v u) ∧
        ∀ r ∈ Icc s T, WB (K * b r) (transp v u r) ∧
          ∀ j : Fin 2, WB (K * b r) (B0579.pd j (transp v u r))

end CylPDE

end UnforcedLeray.Short.IIb
