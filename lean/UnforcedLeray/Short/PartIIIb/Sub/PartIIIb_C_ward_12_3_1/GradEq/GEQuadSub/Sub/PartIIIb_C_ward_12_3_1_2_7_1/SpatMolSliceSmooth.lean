import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1

/-!
# Smoothness of spatial mollifications on a.e. phase slice

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), 2525-2531.

For a.e. `τ ∈ (0,P]`, Fubini applied to `f ∈ L^1_loc` gives that the slice `y ↦ f(τ,y)` is
locally integrable on `ℝ³`; then `y ↦ spatMol ρ f (τ,y)` is the convolution of the smooth compactly
supported kernel `ρ` with that slice, which is `C^∞` (Mathlib `HasCompactSupport.contDiff_convolution_left`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Mollified slices are `C¹`** (source 2562-2564). -/
theorem spatMol_sliceSmooth : SpatMolSliceSmooth := by
  intro P _ ρ hρs hρc f hf
  -- for a.e. `τ`, every ball slice of `f` is integrable (Fubini on each cell `(0,P] × B(0,N)`)
  have hae : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ N : ℕ,
      Integrable (fun y : UnforcedLeray.Space => f (τ, y))
        (volume.restrict (Metric.closedBall 0 (N : ℝ))) := by
    rw [ae_all_iff]
    intro N
    exact Integrable.prod_right_ae (memLp_one_iff_integrable.1 (hf (N : ℝ)))
  filter_upwards [hae] with τ hτ
  have hloc : LocallyIntegrable (fun y : UnforcedLeray.Space => f (τ, y)) volume := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have hxN : x ∈ Metric.ball (0 : UnforcedLeray.Space) (N : ℝ) := by
      rw [mem_ball_zero_iff]
      exact hN
    exact ⟨Metric.ball 0 (N : ℝ), IsOpen.mem_nhds Metric.isOpen_ball hxN,
      IntegrableOn.mono_set (hτ N) Metric.ball_subset_closedBall⟩
  have hρC : ContDiff ℝ 1 (fun y : UnforcedLeray.Space => (ρ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hρs.of_le (by simp))
  have hρK : HasCompactSupport (fun y : UnforcedLeray.Space => (ρ y : ℂ)) :=
    hρc.comp_left Complex.ofReal_zero
  have hconv := hρK.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hρC hloc
  have key : (fun y : UnforcedLeray.Space => spatMol ρ f (τ, y)) =
      convolution (fun y : UnforcedLeray.Space => (ρ y : ℂ))
        (fun y : UnforcedLeray.Space => f (τ, y)) (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext y
    simp [spatMol, convolution_def]
  rw [key]
  exact hconv

end UnforcedLeray.Short.PartIIIb.Concrete
