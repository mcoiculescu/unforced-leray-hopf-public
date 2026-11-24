import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.PlaneHeatFderiv

/-!
# `PartII-a:N01/9/1/2/4/6/2/2` (helper): norms of the planar heat

Source `the November 2 reference manuscript`
lines 3373-3383.  For a `C¹` field `u` with `‖u‖ ≤ K`, `‖Du‖ ≤ K`, the planar heat `planeHeat θ u`
is differentiable, keeps the bounds `K`, and its derivative is the planar heat of the derivative.
For `θ > 0` the value bound is the Gaussian average of a bounded field; for `θ ≤ 0` the heat is
the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

/-- For `θ > 0`, the planar heat of a field bounded by `K'` is bounded by `K'`. -/
theorem hgi_planeHeat_bound_pos {θ : ℝ} (hθ : 0 < θ)
    (g : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (K' : ℝ) (hg : ∀ y, ‖g y‖ ≤ K') (x : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ g x‖ ≤ K' := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  calc ‖∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • g (x - UnforcedLeray.B0224.planeι y)‖
      ≤ ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y * K' := by
        refine norm_integral_le_of_norm_le
          ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const K')
          (ae_of_all _ fun y => ?_)
        rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
        exact mul_le_mul_of_nonneg_left (hg _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
    _ = K' := by
        rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, one_mul]

theorem hgiPlaneHeatNorm : UnforcedLeray.Short.PartIIa.N01.HGIPlaneHeatNorm := by
  intro θ K u hu hKu hKd
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hKu 0)
  rcases lt_or_ge 0 θ with hθ | hθ
  · obtain ⟨hdiff, hform⟩ :=
      planeHeat_fderiv_apply θ hθ u hu ⟨K, fun x => ⟨hKu x, hKd x⟩⟩
    refine ⟨hdiff, fun x => ?_, fun x => ?_, hform⟩
    · exact hgi_planeHeat_bound_pos hθ u K (fun y => hKu y) x
    · refine ContinuousLinearMap.opNorm_le_bound _ hK0 (fun v => ?_)
      rw [hform x v]
      have hg : ∀ y, ‖fderiv ℝ u y v‖ ≤ K * ‖v‖ := fun y =>
        (ContinuousLinearMap.le_opNorm (fderiv ℝ u y) v).trans
          (mul_le_mul_of_nonneg_right (hKd y) (norm_nonneg v))
      exact hgi_planeHeat_bound_pos hθ (fun y => fderiv ℝ u y v) (K * ‖v‖) hg x
  · have hdu : Differentiable ℝ u := fun x => (hu.differentiable (by norm_num)) x
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [UnforcedLeray.B0224.planeHeat_of_nonpos hθ u]
      exact hdu
    · intro x
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos hθ u]
      exact hKu x
    · intro x
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos hθ u]
      exact hKd x
    · intro x v
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos hθ u,
        UnforcedLeray.B0224.planeHeat_of_nonpos hθ (fun y => fderiv ℝ u y v)]

end UnforcedLeray.Short.PartIIa.N01
