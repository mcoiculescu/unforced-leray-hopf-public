import UnforcedLeray.Lib.CZL2.NewtonConv

/-!
# The Newton Hessian kernel (INF01 level L0, target T1)

Blueprint: INF01 target T1 (scoping note `INF01-CZ.md` §4.2, §5). Manuscript:
`R_iR_k = ∂_i∂_k(-Δ)^{-1}` (`paper/main.tex` lines 107–111), whose off-support kernel is
`K_ik = ∂_i∂_k N = (3xᵢxₖ - δᵢₖ|x|²)/(4π|x|⁵)`.

We define the kernel, identify it with the classical second derivative of the compiled
Newton potential away from the origin, and prove the size bound `|K_ik(x)| ≤ π⁻¹|x|⁻³`.
At `x = 0` the formula gives `0` by real division; no statement here uses that value.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- The Newton Hessian kernel `∂ᵢ∂ₖN(x) = (3xᵢxₖ - δᵢₖ|x|²)/(4π|x|⁵)` (INF01 T1). -/
def newtonHessianKernel (i k : Fin 3) (x : Space) : ℝ :=
  (3 * x i * x k - (if i = k then ‖x‖ ^ 2 else 0)) / (4 * Real.pi * ‖x‖ ^ 5)

theorem newtonHessianKernel_symm (i k : Fin 3) (x : Space) :
    newtonHessianKernel i k x = newtonHessianKernel k i x := by
  unfold newtonHessianKernel
  by_cases h : i = k
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

theorem newtonHessianKernel_neg (i k : Fin 3) (x : Space) :
    newtonHessianKernel i k (-x) = newtonHessianKernel i k x := by
  simp [newtonHessianKernel]

theorem newtonHessianKernel_measurable (i k : Fin 3) :
    Measurable (newtonHessianKernel i k) := by
  unfold newtonHessianKernel
  have h1 : Measurable fun x : Space => x i := (EuclideanSpace.proj i).continuous.measurable
  have h2 : Measurable fun x : Space => x k := (EuclideanSpace.proj k).continuous.measurable
  have h3 : Measurable fun x : Space => (if i = k then ‖x‖ ^ 2 else 0) := by
    split_ifs
    · exact (continuous_norm.pow 2).measurable
    · exact measurable_const
  exact (((measurable_const.mul h1).mul h2).sub h3).div
    (measurable_const.mul (continuous_norm.pow 5).measurable)

private lemma norm_sq_rpow_neg_five_halves (x : Space) :
    (‖x‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1 - 1) = (‖x‖ ^ 5)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

/-- The Newton gradient kernel written with a real power, valid at every point. -/
private lemma newtonGradientKernel_eq_rpow (k : Fin 3) (y : Space) :
    newtonGradientKernel k y =
      -(y k) * ((4 * Real.pi)⁻¹ * (‖y‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1)) := by
  rw [newtonGradientKernel, norm_sq_rpow_neg_three_halves]
  rw [div_eq_mul_inv, mul_inv]

/-- Classical derivative of the Newton gradient kernel away from the origin. -/
theorem hasFDerivAt_newtonGradientKernel (k : Fin 3) {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (newtonGradientKernel k)
      ((-(x k)) • ((4 * Real.pi)⁻¹ • (((-(1 : ℝ) / 2 - 1) *
          (‖x‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1 - 1)) • (2 • innerSL ℝ x))) +
        ((4 * Real.pi)⁻¹ * (‖x‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1)) •
          (-(EuclideanSpace.proj k : Space →L[ℝ] ℝ)))
      x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hr := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := -(1 : ℝ) / 2 - 1) (Or.inl (pow_ne_zero 2 hn))).const_mul ((4 * Real.pi)⁻¹)
  have hc : HasFDerivAt (fun y : Space => -(y k : ℝ))
      (-(EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x := by
    refine HasFDerivAt.neg (f := fun y : Space => (y k : ℝ)) ?_
    exact (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
  have h := hc.mul hr
  have he : (fun y : Space => -(y k) * ((4 * Real.pi)⁻¹ * (‖y‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1))) =
      newtonGradientKernel k := by
    funext y; rw [newtonGradientKernel_eq_rpow]
  rw [← he]
  exact h

/-- **INF01 T1.** Away from the origin the kernel is the classical second derivative of the
compiled Newton potential: `K_ik(x) = ∂ᵢ(∂ₖN)(x)`. -/
theorem newtonHessianKernel_eq (i k : Fin 3) {x : Space} (hx : x ≠ 0) :
    newtonHessianKernel i k x =
      fderiv ℝ (fun y => fderiv ℝ newtonPotential y (coordinateVector k)) x
        (coordinateVector i) := by
  have hev : (fun y => fderiv ℝ newtonPotential y (coordinateVector k)) =ᶠ[𝓝 x]
      newtonGradientKernel k := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact fderiv_newtonPotential_coordinate hy k
  rw [hev.fderiv_eq, (hasFDerivAt_newtonGradientKernel k hx).fderiv]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : inner ℝ x (coordinateVector i) = x i := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  have hk : (coordinateVector i) k = if i = k then 1 else 0 := by
    simp [coordinateVector, eq_comm]
  simp only [add_apply, smul_apply,
    neg_apply, innerSL_apply_apply, smul_eq_mul,
    norm_sq_rpow_neg_five_halves, norm_sq_rpow_neg_three_halves, hi]
  rw [show (EuclideanSpace.proj k) (coordinateVector i) = (coordinateVector i) k from rfl, hk]
  unfold newtonHessianKernel
  split_ifs with h
  · subst h
    field_simp
    ring
  · field_simp
    ring

/-- **INF01 T1.** Size bound `|K_ik(x)| ≤ π⁻¹ |x|⁻³` (the value at `0` is `0` on both sides). -/
theorem norm_newtonHessianKernel_le (i k : Fin 3) (x : Space) :
    |newtonHessianKernel i k x| ≤ Real.pi⁻¹ * ‖x‖ ^ (-3 : ℝ) := by
  by_cases hx : x = 0
  · subst hx; simp [newtonHessianKernel]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have hxk : |x k| ≤ ‖x‖ := PiLp.norm_apply_le x k
  have hnum : |3 * x i * x k - (if i = k then ‖x‖ ^ 2 else 0)| ≤ 4 * ‖x‖ ^ 2 := by
    have h1 : |3 * x i * x k| ≤ 3 * ‖x‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [abs_nonneg (x i), abs_nonneg (x k)]
    have h2 : |(if i = k then ‖x‖ ^ 2 else 0)| ≤ ‖x‖ ^ 2 := by
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
      · simp
    calc _ ≤ |3 * x i * x k| + |(if i = k then ‖x‖ ^ 2 else 0)| := abs_sub _ _
      _ ≤ 4 * ‖x‖ ^ 2 := by linarith
  unfold newtonHessianKernel
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi * ‖x‖ ^ 5),
    Real.rpow_neg hn.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    div_le_iff₀ (by positivity)]
  calc _ ≤ 4 * ‖x‖ ^ 2 := hnum
    _ = Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ * (4 * Real.pi * ‖x‖ ^ 5) := by
      field_simp

end UnforcedLeray.RieszLp
