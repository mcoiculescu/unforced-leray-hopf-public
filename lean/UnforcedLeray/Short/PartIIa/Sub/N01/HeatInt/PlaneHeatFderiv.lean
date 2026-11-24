import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4

/-!
# `PartII-a:N01/9/1/2/4/4` (heat integral): `PlaneHeatFderiv`

Source `the November 2 reference manuscript`
lines 3373-3383.  For `θ > 0` the cylinder heat `planeHeat θ u` is the planar Gaussian average
`x ↦ ∫ G_θ(y) u(x - ι y) dy`; for a bounded `C¹` function with bounded derivative the average is
differentiable and the derivative falls on `u` (dominated differentiation under the integral).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

theorem planeHeatFderiv : UnforcedLeray.Short.PartIIa.N01.PlaneHeatFderiv := by
  intro θ hθ u hu hbdd hder
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨M', hM'⟩ := hder
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have huc : Continuous u := hu.continuous
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hG : MeasureTheory.Integrable
      (fun y : UnforcedLeray.Gaussian.Euc 2 => UnforcedLeray.Gaussian.gaussKernel 2 θ y) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  have hGnn : ∀ y : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y :=
    fun y => UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθ y
  have hGcont : Continuous (UnforcedLeray.Gaussian.gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) θ
  have hιc : Continuous (UnforcedLeray.B0224.planeι : UnforcedLeray.Gaussian.Euc 2 → ℝ × ℝ) :=
    UnforcedLeray.B0224.continuous_planeι
  -- integrability of the integrand at every point
  have hint : ∀ x : ℝ × ℝ, MeasureTheory.Integrable
      (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) := by
    intro x
    refine (hG.const_mul M).mono' ?_ ?_
    · exact (hGcont.smul (huc.comp (continuous_const.sub hιc))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_smul, Real.norm_of_nonneg (hGnn y), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _) (hGnn y)
  -- the pointwise derivative in `x`
  have hderivInt : ∀ x : ℝ × ℝ, ∀ y : UnforcedLeray.Gaussian.Euc 2,
      HasFDerivAt (fun x' : ℝ × ℝ =>
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x' - UnforcedLeray.B0224.planeι y))
        (UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)) x := by
    intro x y
    have h2 : HasFDerivAt (fun x' : ℝ × ℝ => x' - UnforcedLeray.B0224.planeι y)
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      (hasFDerivAt_id x).sub_const (UnforcedLeray.B0224.planeι y)
    have h3 : HasFDerivAt (fun x' : ℝ × ℝ => u (x' - UnforcedLeray.B0224.planeι y))
        (fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)) x := by
      exact (hu1 (x - UnforcedLeray.B0224.planeι y)).hasFDerivAt.comp x h2
    exact h3.const_smul (UnforcedLeray.Gaussian.gaussKernel 2 θ y)
  -- bound on the derivative
  have hbound : ∀ x : ℝ × ℝ, ∀ y : UnforcedLeray.Gaussian.Euc 2,
      ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)‖
        ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y * M' := by
    intro x y
    rw [norm_smul, Real.norm_of_nonneg (hGnn y)]
    exact mul_le_mul_of_nonneg_left (hM' _) (hGnn y)
  have hF'int : ∀ x : ℝ × ℝ, MeasureTheory.Integrable
      (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)) := by
    intro x
    refine (hG.mul_const M').mono' ?_ ?_
    · exact (hGcont.smul (hd.comp (continuous_const.sub hιc))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => hbound x y
  have hfd : ∀ x : ℝ × ℝ, HasFDerivAt (UnforcedLeray.B0224.planeHeat θ u)
      (∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x - UnforcedLeray.B0224.planeι y)) x := by
    intro x
    have heq : UnforcedLeray.B0224.planeHeat θ u =
        fun x' : ℝ × ℝ => ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x' - UnforcedLeray.B0224.planeι y) :=
      funext fun x' => UnforcedLeray.B0224.planeHeat_of_pos hθ u x'
    rw [heq]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun y =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * M') (s := Set.univ)
      (F := fun x' y => UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x' - UnforcedLeray.B0224.planeι y))
      (F' := fun x' y => UnforcedLeray.Gaussian.gaussKernel 2 θ y • fderiv ℝ u (x' - UnforcedLeray.B0224.planeι y))
      Filter.univ_mem ?_ (hint x) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x' =>
        (hGcont.smul (huc.comp (continuous_const.sub hιc))).aestronglyMeasurable
    · exact (hGcont.smul (hd.comp (continuous_const.sub hιc))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y x' _ => hbound x' y
    · exact hG.mul_const M'
    · exact Filter.Eventually.of_forall fun y x' _ => hderivInt x' y
  refine ⟨fun x => (hfd x).differentiableAt, fun x v => ?_⟩
  rw [(hfd x).fderiv, ContinuousLinearMap.integral_apply (hF'int x) v,
    UnforcedLeray.B0224.planeHeat_of_pos hθ]
  congr 1
