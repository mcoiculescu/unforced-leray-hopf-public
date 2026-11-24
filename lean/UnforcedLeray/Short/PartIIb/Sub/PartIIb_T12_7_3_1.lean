import UnforcedLeray.Short.PartIIb.Sub.T12_7_3

/-!
# Part II-b, task `PartII-b:T12/7/3/1` (`deqhsAbsInt`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the heat
semigroup is self-adjoint; absolute integrability of the Fubini integrand).

Route.  Write `K = flatHeatKernel θ` and `convAbs θ g z = ∫⁻ w, K w ‖g (z - w)‖ₑ` (the convolution of
`‖g‖` with the heat kernel, as a lintegral).  Then

* `DeqhsAbsMeas`: the integrand and its coordinate versions are a.e. strongly measurable on the
  product (a strongly measurable representative of `g`, and `(z, w) ↦ z - w` is quasi measure
  preserving);
* `DeqhsConvPeriodic`: `convAbs θ g` is measurable and *everywhere* `c`-periodic in `q` (a.e. periodicity
  of `g` is transferred through the quasi measure preserving map `w ↦ z - w`);
* `DeqhsConvLp`: `convAbs θ g ∈ L^r(Cyl.cellμ c)` (Minkowski with unit-mass kernel; compare
  `Tasks/FlatCausal/FlatHeatContraction.lean` and `Cyl.eLpNorm_conv_periodic_le`);
* `DeqhsPeriodicBox`: an everywhere periodic measurable `h` in `L^r(cell)` has finite lintegral on every
  box `[-R,R]²` (the box meets finitely many strips; Hölder on a finite measure set);
* `DeqhsAbsLint`: the lintegral of `K(w) ‖g(z-w)‖ |ψ(z)|` over the product is finite (Tonelli, then the
  three previous leaves and `|ψ| ≤ ‖ψ‖∞ 1_box`).

Proved here: `deqhsAbsInt_of : DeqhsAbsMeas → DeqhsAbsLint → DeqhsAbsInt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The lintegral convolution of `‖g‖` with the planar heat kernel (SP 1923-1927). -/
def convAbs (θ : ℝ) (g : ℝ × ℝ → CMerid) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (flatHeatKernel θ w) * ‖g (z - w)‖ₑ

/-- **Leaf `PartII-b:T12/7/3/1/1`** (SP 1923-1927): a.e. strong measurability of the Fubini integrand
and of its coordinate versions on `(ℝ×ℝ) × (ℝ×ℝ)`. -/
def DeqhsAbsMeas : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ → ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ →
      AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|) (volume.prod volume) ∧
        ∀ i : Fin 2, AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          (flatHeatKernel θ p.2 : ℂ) * g (p.1 - p.2) i * (ψ p.1 : ℂ)) (volume.prod volume)

/-- **Leaf `PartII-b:T12/7/3/1/2`** (SP 1923-1927): `convAbs θ g` is measurable and everywhere
`c`-periodic in the first variable. -/
def DeqhsConvPeriodic : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ →
      Measurable (convAbs θ g) ∧ ∀ z : ℝ × ℝ, convAbs θ g (z.1 + c, z.2) = convAbs θ g z

/-- **Leaf `PartII-b:T12/7/3/1/3`** (SP 1923-1927): `convAbs θ g` has finite `L^r` norm on the cell. -/
def DeqhsConvLp : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ →
      eLpNorm (convAbs θ g) (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) < ⊤

/-- **Leaf `PartII-b:T12/7/3/1/4`** (SP 1923-1927): a measurable, everywhere `c`-periodic function in
`L^r(cell)`, `r > 1`, has finite lintegral over every box (finitely many strips, Hölder on a finite
measure set). -/
def DeqhsPeriodicBox : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ h : ℝ × ℝ → ℝ≥0∞, Measurable h →
    (∀ z : ℝ × ℝ, h (z.1 + c, z.2) = h z) →
      eLpNorm h (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) < ⊤ →
        ∀ R : ℝ, ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z < ⊤

/-- **Leaf `PartII-b:T12/7/3/1/5`** (SP 1923-1927): finiteness of the lintegral of the Fubini integrand
(Tonelli, `DeqhsAbsMeas`, `DeqhsConvPeriodic`, `DeqhsConvLp`, `DeqhsPeriodicBox`). -/
def DeqhsAbsLint : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ → ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ → HasCompactSupport ψ →
      ∫⁻ p : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|)
          ∂(volume.prod volume) < ⊤

theorem deqhsAbsInt_of (h1 : DeqhsAbsMeas) (h2 : DeqhsAbsLint) : DeqhsAbsInt := by
  intro c r g hc hr hg θ hθ ψ hψ hψc
  obtain ⟨hm, hmi⟩ := h1 c r g hc hr hg θ hθ ψ hψ
  have hl := h2 c r g hc hr hg θ hθ ψ hψ hψc
  have hK : ∀ w : ℝ × ℝ, 0 ≤ flatHeatKernel θ w := fun w => by
    unfold flatHeatKernel
    have := Real.pi_pos
    positivity
  have hI : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|) (volume.prod volume) := by
    refine ⟨hm, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hl
    congr 1
    funext p
    exact Real.enorm_eq_ofReal (mul_nonneg (mul_nonneg (hK _) (norm_nonneg _)) (abs_nonneg _))
  refine ⟨hI, fun i => ?_⟩
  refine hI.mono' (hmi i) (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (hK _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (g (p.1 - p.2)) i) (hK _)) (abs_nonneg _)

end UnforcedLeray.Short.IIb
