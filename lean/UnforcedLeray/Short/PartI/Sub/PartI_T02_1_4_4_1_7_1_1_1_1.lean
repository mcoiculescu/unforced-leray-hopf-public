import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1`: the `H^3` generator at age zero from componentwise `L^2` limits

Source `the November 2 reference manuscript`, lines 261-288.

The generator limit `HeatGeneratorAtZero5` cannot be obtained from the age derivative (that is
circular: `HeatAgeDerivSmooth5` is reduced to it).  It follows from the derivative-by-derivative
`L^2` statement: the `H^3` norm is the sum over `|α| ≤ 3` of the `L^2` norms of `∂^α`.
Three leaves:
* `HeatTaylorUniform`: uniform second-order Taylor bound for the Gaussian average of a smooth field;
* `HeatL2GeneratorSmooth`: the `L^2(cell)` generator limit for every derivative of a smooth field;
* `HeatH3DerivQuot`: the `H^3`-derivative form of the generator limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf 1 (uniform Taylor bound; source lines 261-288).** For cylinder-smooth `f`, the Gaussian
average `heatVecConvolution h f` (kernel `heatKernel2 h`, `∂_h K = ΔK`) satisfies
`‖h⁻¹ (heatVecConvolution h f x - f x) - Δ f x‖ ≤ C √h` uniformly in `x` for `0 < h ≤ 1`.
Proof idea: third-order Taylor expansion of `f(x-w)` (derivatives of `f` bounded since `f` is
periodic with compact transversal support), Gaussian moments `∫K_h = 1`, `∫K_h w = 0`,
`∫K_h w_i w_j = 2h δ_ij`, `∫K_h |w|³ = C h^{3/2}`. -/
def HeatTaylorUniform : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (f : Plane → Cyl.Vec2) (_hf : Sob.IsCylSmooth c f),
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : Plane,
      ‖h⁻¹ • (HeatCylinder.heatVecConvolution h f x - f x)
        - (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f x)‖ ≤ C * Real.sqrt h

/-- **Leaf 2 (`L^2(cell)` generator limit for every derivative; source lines 261-288).**
For cylinder-smooth `T` with cylinder-smooth Laplacian `ΔT` and every direction list `vs`, with
`x = [∂^vs T]` and `y = [∂^vs ΔT]` in `L^2(cellMeasure c)`:
`h⁻¹ (S(h) x - x) → y` in `L^2` as `h → 0+` (`S` = `heatVecL2CLM`). -/
def HeatL2GeneratorSmooth : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T)
    (hΔ : Sob.IsCylSmooth c (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
      + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x)) (vs : List Plane),
    Tendsto (fun h : ℝ => ‖h⁻¹ •
        (HeatCylinder.heatVecL2CLM hc h
            ((HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT vs).toLp (Sob.iterD vs T))
          - (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hT vs).toLp (Sob.iterD vs T))
        - (HeatCylinder.memLp_iterD_vec_cylSmooth_normalized hc hΔ vs).toLp
            (Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
              + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x))‖)
      (𝓝[>] 0) (𝓝 0)

/-- **Leaf 3 (`H^3` derivatives of the generator quotient; source lines 261-288).** For every
derivative index `α` of order `≤ 3`, `‖∂^α (h⁻¹ (S(h) z - z) - Δ z)‖_{L^2} → 0` as `h → 0+`,
with `z = smoothH5Field T` restricted to `H^3`. -/
def HeatH3DerivQuot : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T) (α : Sob.Idx 2 3),
    Tendsto (fun h : ℝ => ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (h⁻¹ • (HeatCylinder.heatVecH3Semigroup (c := c) (θ := h) hc
            (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) :
              Cyl.H ℝ Cyl.Vec2 c 0 3)
          - (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) :
              Cyl.H ℝ Cyl.Vec2 c 0 3))
          - hLap c 3 (smoothH5Field hc T hT))‖)
      (𝓝[>] 0) (𝓝 0)

/-- The generator limit follows from the componentwise `H^3` derivative limits. -/
theorem heatGeneratorAtZero5_of (hQ : HeatH3DerivQuot) : HeatGeneratorAtZero5 := by
  intro c hc T hT
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun h : ℝ => ∑ α : Sob.Idx 2 3,
      ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α
        (h⁻¹ • (HeatCylinder.heatVecH3Semigroup (c := c) (θ := h) hc
            (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) :
              Cyl.H ℝ Cyl.Vec2 c 0 3)
          - (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) :
              Cyl.H ℝ Cyl.Vec2 c 0 3))
          - hLap c 3 (smoothH5Field hc T hT))‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Sob.Idx 2 3))
      (fun α _ => (hQ c hc T hT α).pow 2)
    simpa using h
  have hsq := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
  simp only [Real.sqrt_zero] at hsq
  refine hsq.congr (fun h => ?_)
  simp only [Function.comp_apply]
  rw [← Sob.W.norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

end UnforcedLeray.Short.PartI
