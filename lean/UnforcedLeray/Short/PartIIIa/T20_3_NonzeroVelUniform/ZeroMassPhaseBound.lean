import UnforcedLeray.Short.PartIIIa.Sub.T20_3

/-!
# Part III-a, task `PartIII-a:T20/3/5`: the zero-mass phase bound

Proof of `CTE.T20_3.ZeroMassPhaseBound` (`Sub/T20_3.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3237 ("zero mass gives
`|f^(ξ)| ≤ |ξ| ∫|y||f|`").

Write `E x = exp(-i(κ x₁ + 2πξ x₂))`. Since `∫ u = 0`, `∫ E u = ∫ (E - 1) u`. The pointwise bound
`‖E x - 1‖ ≤ (|κ| + 2π|ξ|)(|x₁| + |x₂|)` then gives the estimate, by `norm_integral_le_of_norm_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

/-- Pointwise phase bound: `‖e^{-iA} - 1‖ ≤ (|κ| + 2π|ξ|)(|x₁| + |x₂|)` for `A = κ x₁ + 2πξ x₂`. -/
theorem zeroMassPhaseBound_norm_sub_one_le (κ ξ : ℝ) (x : ℝ × ℝ) :
    ‖Complex.exp (-(Complex.I * ((κ * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))) - 1‖ ≤
      (|κ| + 2 * π * |ξ|) * (|x.1| + |x.2|) := by
  have h1 : Complex.exp (-(Complex.I * ((κ * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((-(κ * x.1 + 2 * π * ξ * x.2) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [h1]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_neg]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h2 : |2 * π * ξ * x.2| = 2 * π * |ξ| * |x.2| := by
    rw [abs_mul, abs_mul, abs_of_pos hpi]
  have hA : |κ * x.1 + 2 * π * ξ * x.2| ≤ |κ| * |x.1| + 2 * π * |ξ| * |x.2| := by
    calc |κ * x.1 + 2 * π * ξ * x.2| ≤ |κ * x.1| + |2 * π * ξ * x.2| := abs_add_le _ _
      _ = |κ| * |x.1| + 2 * π * |ξ| * |x.2| := by
        rw [abs_mul, h2]
  have hk : 0 ≤ |κ| * |x.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hx : 0 ≤ 2 * π * |ξ| * |x.1| :=
    mul_nonneg (mul_nonneg hpi.le (abs_nonneg _)) (abs_nonneg _)
  nlinarith [hA, hk, hx]

/-- Abstract zero-mass estimate. If `‖E x - 1‖ ≤ K w(x)` pointwise, `u` is integrable with
`K w ‖u‖` integrable and `∫ u = 0`, then `‖∫ E u‖ ≤ K ∫ w ‖u‖`. -/
theorem zeroMassPhaseBound_core (μ : Measure (ℝ × ℝ)) (E u : ℝ × ℝ → ℂ) (w : ℝ × ℝ → ℝ)
    (K : ℝ) (hE : AEStronglyMeasurable E μ) (hu : Integrable u μ)
    (hw : ∀ x, ‖E x - 1‖ ≤ K * w x)
    (hwu : Integrable (fun x => K * (w x * ‖u x‖)) μ)
    (hzero : ∫ x, u x ∂μ = 0) :
    ‖∫ x, E x * u x ∂μ‖ ≤ K * ∫ x, w x * ‖u x‖ ∂μ := by
  have hbound : ∀ x, ‖(E x - 1) * u x‖ ≤ K * (w x * ‖u x‖) := by
    intro x
    rw [norm_mul]
    calc ‖E x - 1‖ * ‖u x‖ ≤ (K * w x) * ‖u x‖ :=
          mul_le_mul_of_nonneg_right (hw x) (norm_nonneg _)
      _ = K * (w x * ‖u x‖) := by ring
  have hfI : Integrable (fun x => (E x - 1) * u x) μ :=
    Integrable.mono' hwu ((hE.sub aestronglyMeasurable_const).mul hu.aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  have hsplit : ∫ x, E x * u x ∂μ = ∫ x, (E x - 1) * u x ∂μ := by
    have h := integral_add hfI hu
    rw [hzero, add_zero] at h
    rw [← h]
    congr 1
    funext x
    ring
  rw [hsplit]
  calc ‖∫ x, (E x - 1) * u x ∂μ‖ ≤ ∫ x, K * (w x * ‖u x‖) ∂μ :=
        norm_integral_le_of_norm_le hwu (Filter.Eventually.of_forall hbound)
    _ = K * ∫ x, w x * ‖u x‖ ∂μ := integral_const_mul K (fun x => w x * ‖u x‖)

/-- **Zero-mass phase bound** (task `PartIII-a:T20/3/5`; SP 3236-3237, "zero mass gives
`|f^(ξ)| ≤ |ξ| ∫|y||f|`"). Proves `ZeroMassPhaseBound` (`Sub/T20_3.lean`). -/
theorem zeroMassPhaseBound : ZeroMassPhaseBound := by
  intro c κ ξ u hu hmom hzero
  have hEc : Continuous (fun x : ℝ × ℝ =>
      Complex.exp (-(Complex.I * ((κ * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ)))) := by
    fun_prop
  exact zeroMassPhaseBound_core (B0581.cellVol c)
    (fun x => Complex.exp (-(Complex.I * ((κ * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))))
    u (fun x => |x.1| + |x.2|) (|κ| + 2 * π * |ξ|)
    hEc.aestronglyMeasurable hu
    (fun x => zeroMassPhaseBound_norm_sub_one_le κ ξ x)
    (hmom.const_mul (|κ| + 2 * π * |ξ|)) hzero

end UnforcedLeray.Short.IIIa.CTE.T20_3
