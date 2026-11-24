import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2`: `UnitHeatKernelDeriv` from four lemmas

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Write `realHeat τ φ y = ∫ heatKernel2 τ w φ(y - w)` for the real planar heat flow.  The cell pairing
of the first component of `B0284.heat τ f` against a `q`-periodic test is, by Fubini and
`q`-periodicity of `f`, the cell pairing of `f₁` against `realHeat τ φ` (lemma A, duality); the age
derivative of `realHeat τ φ y` is `realHeat τ (Δφ) y` (lemma B, `∂_τ G = ΔG` plus integration by
parts); `realHeat` is continuous in `y` and bounded by the sup norm (lemma B').  Differentiation
under the cell integral with dominant `K |f₁|` then gives the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology Metric

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The real planar heat flow. -/
def realHeat (τ : ℝ) (φ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * φ (y - w)

/-- A (duality): cell pairing of the Gaussian flow equals pairing of the lift against the heat flow
of the test.  Source 2819-2836. -/
def UnitHeatDuality : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m)
    (w : UnforcedLeray.B0579.X c m) (φ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c φ →
      ∀ τ : ℝ, 0 < τ →
        ∫ z in UnforcedLeray.B0579.cell c,
            (UnforcedLeray.B0284.heat τ (xColumnHeatLift (Fact.out : 0 < c) w) z).1 * φ z =
          ∫ y in UnforcedLeray.B0579.cell c,
            (xColumnHeatLift (Fact.out : 0 < c) w y).1 * realHeat τ φ y

/-- D: the lift is integrable on the cell for Lebesgue measure (`X_{m,c} ⊂ L¹(cell)`,
`m ≥ 1`). -/
def UnitHeatLiftIntegrable : Prop :=
  ∀ (c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (w : UnforcedLeray.B0579.X c m),
    IntegrableOn (fun y => (xColumnHeatLift (Fact.out : 0 < c) w y).1)
      (UnforcedLeray.B0579.cell c)

/-- B: age derivative of the real heat flow of a cylinder test (`∂_τ G = ΔG`, integration by
parts).  The cylinder has period `c = ν⁻² > 0` (source 2819-2836); `0 < c` is needed: at `c = 0`
periodicity is vacuous and `φ(q,η) = exp(q²)χ(η)` is a test whose heat flow blows up as `τ ↑ 1/4`
and is `0` (non-integrable) for `τ ≥ 1/4`, so it has no age derivative at `θ = 1/4`. -/
def RealHeatDeriv : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (φ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c φ →
    ∀ θ : ℝ, 0 < θ → ∀ y : ℝ × ℝ,
      HasDerivAt (fun τ => realHeat τ φ y) (realHeat θ (lapP φ) y) θ

/-- B': the real heat flow of a bounded continuous function is continuous and bounded by the
same constant (`∫ G = 1`, `G ≥ 0`). -/
def RealHeatBound : Prop :=
  ∀ (g : ℝ × ℝ → ℝ), Continuous g → ∀ K : ℝ, (∀ z, |g z| ≤ K) →
    ∀ τ : ℝ, 0 < τ → Continuous (realHeat τ g) ∧ ∀ y, |realHeat τ g y| ≤ K

/-- G: the planar Laplacian of a cylinder test is again a cylinder test (`pd` of a test is a test,
sums of tests are tests); cylinder tests are bounded (continuous, periodic, band-supported); `0 < c` is needed (at `c = 0` periodicity is vacuous and `q·χ(η)` is an unbounded test). -/
def LapTestBounded : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (φ : ℝ × ℝ → ℝ), UnforcedLeray.B0579.IsCylTest c φ →
    UnforcedLeray.B0579.IsCylTest c (lapP φ) ∧ (∃ K0 : ℝ, ∀ z, |φ z| ≤ K0) ∧
      ∃ K : ℝ, ∀ z, |lapP φ z| ≤ K

theorem unitHeatKernelDeriv_of (hA : UnitHeatDuality) (hD : UnitHeatLiftIntegrable)
    (hB : RealHeatDeriv) (hB' : RealHeatBound) (hG : LapTestBounded) :
    UnitHeatKernelDeriv := by
  intro c m _ hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro w φ hφ θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hc : 0 < c := Fact.out
  obtain ⟨hlt, ⟨K0, hK0⟩, K, hK⟩ := hG c hc φ hφ
  have hlc : Continuous (lapP φ) := hlt.continuous
  set F0 : ℝ × ℝ → ℝ := fun y => (xColumnHeatLift hc w.1 y).1 with hF0
  set μ := volume.restrict (UnforcedLeray.B0579.cell c) with hμ
  have hint : Integrable F0 μ := hD c m hm w.1
  have hφc : Continuous φ := hφ.continuous
  have key : HasDerivAt (fun τ : ℝ => ∫ y, F0 y * realHeat τ φ y ∂μ)
      (∫ y, F0 y * realHeat θ (lapP φ) y ∂μ) θ := by
    have hmeas : ∀ τ, 0 < τ → AEStronglyMeasurable (fun y => F0 y * realHeat τ φ y) μ := by
      intro τ hτ
      exact hint.aestronglyMeasurable.mul (hB' φ hφc K0 hK0 τ hτ).1.aestronglyMeasurable
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun τ y => F0 y * realHeat τ φ y)
      (F' := fun τ y => F0 y * realHeat τ (lapP φ) y) (x₀ := θ) (bound := fun y => K * |F0 y|)
      (s := Ioi (0:ℝ)) (Ioi_mem_nhds hθ0)
      (by
        filter_upwards [Ioi_mem_nhds hθ0] with τ hτ using hmeas τ hτ)
      (by
        refine ((hint.norm.const_mul K0).mono' (hmeas θ hθ0) ?_)
        refine Filter.Eventually.of_forall ?_
        intro y
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |F0 y| * |realHeat θ φ y| ≤ |F0 y| * K0 :=
              mul_le_mul_of_nonneg_left ((hB' φ hφc K0 hK0 θ hθ0).2 y) (abs_nonneg _)
          _ = K0 * ‖F0 y‖ := by rw [mul_comm, Real.norm_eq_abs])
      (hint.aestronglyMeasurable.mul (hB' _ hlc K hK θ hθ0).1.aestronglyMeasurable)
      (by
        refine Filter.Eventually.of_forall ?_
        intro y τ hτ
        have hτ0 : 0 < τ := hτ
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |F0 y| * |realHeat τ (lapP φ) y| ≤ |F0 y| * K :=
              mul_le_mul_of_nonneg_left ((hB' _ hlc K hK τ hτ0).2 y) (abs_nonneg _)
          _ = K * |F0 y| := mul_comm _ _)
      (hint.norm.const_mul K)
      (by
        refine Filter.Eventually.of_forall ?_
        intro y τ hτ
        have hτ0 : 0 < τ := hτ
        exact (hB c hc φ hφ τ hτ0 y).const_mul (F0 y))
    exact this.2
  have hev : (fun τ : ℝ => ∫ z in UnforcedLeray.B0579.cell c,
        (UnforcedLeray.B0284.heat τ (xColumnHeatLift hc w.1) z).1 * φ z) =ᶠ[𝓝 θ]
      (fun τ : ℝ => ∫ y, F0 y * realHeat τ φ y ∂μ) := by
    filter_upwards [Ioi_mem_nhds hθ0] with τ hτ
    exact hA c m hm w.1 φ hφ τ hτ
  have h2 := hA c m hm w.1 (lapP φ) hlt θ hθ0
  have h3 := key.congr_of_eventuallyEq hev
  rw [h2]
  exact h3
end UnforcedLeray.Short.IIIa.Exist
