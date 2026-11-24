import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_defs
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# `PartII-b:T10/org/3/2/1`: derivatives of the joint Newton potential (`NewtonJointFDeriv`)

Source of record `the November 2 reference manuscript`,
lines 119-120 (`(-Δ)^{-1} = N ∗`) and 1474-1475 (Leray commutes with heat and phase translation:
derivatives in `τ` and `y` pass through the Newton potential).

`newtonJoint D q = (N ⋆ D(q.1, ·))(q.2)` is a convolution depending on the parameter `q.1`; the
source has its spatial support in one fixed ball, so Mathlib's
`hasFDerivAt_convolution_right_with_param` differentiates it in `(τ, y)` jointly (`N` is locally
integrable), and `convolution_precompR_apply` evaluates the derivative in the direction `v`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.PressureAnalysis

/-- **`NewtonJointFDeriv`**: `∂_v (N ∗ D) = N ∗ ∂_v D` for a real scalar phase test `D`. -/
theorem newtonJointFDeriv_proof : NewtonJointFDeriv := by
  intro P D hD p v
  obtain ⟨R, hR⟩ := hD.bounded_support
  let g : ℝ → Space → ℝ := fun τ x => D (τ, x)
  have hug : (Function.HasUncurry.uncurry g : ℝ × Space → ℝ) = D := by
    funext q
    rfl
  have hconv : newtonJoint D = fun q : ℝ × Space =>
      (newtonPotential ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g q.1) q.2 := by
    funext q
    exact congrFun (newtonConv_eq_convolution (fun x => D (q.1, x))) q.2
  have hk : IsCompact (Metric.closedBall (0 : Space) (max R 0)) := isCompact_closedBall _ _
  have hfar : ∀ x : Space, x ∉ Metric.closedBall (0 : Space) (max R 0) → R < ‖x‖ := by
    intro x hx
    have h1 : max R 0 < ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    exact lt_of_le_of_lt (le_max_left _ _) h1
  have hgs : ∀ (τ : ℝ) (x : Space), τ ∈ (univ : Set ℝ) →
      x ∉ Metric.closedBall (0 : Space) (max R 0) → g τ x = 0 :=
    fun τ x _ hx => hR τ x (hfar x hx)
  have hg : ContDiffOn ℝ 1 (Function.HasUncurry.uncurry g) (univ ×ˢ univ) := by
    rw [hug]
    exact (hD.smooth.of_le (by simp)).contDiffOn
  have hd := hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℝ) isOpen_univ
    hk hgs newtonPotential_locallyIntegrable hg p (mem_univ _)
  rw [hconv, hd.fderiv, hug]
  have hcs : HasCompactSupport (fun x : Space => fderiv ℝ D (p.1, x)) := by
    refine HasCompactSupport.intro hk fun x hx => ?_
    exact fderiv_eq_zero_of_far hR (hfar x hx)
  have hcont : Continuous (fun x : Space => fderiv ℝ D (p.1, x)) :=
    (hD.smooth.continuous_fderiv (by simp)).comp (Continuous.prodMk_right p.1)
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) newtonPotential_locallyIntegrable
    hcs hcont p.2 v]
  show _ = newtonConv (fun x => fderiv ℝ D (p.1, x) v) p.2
  rw [newtonConv_eq_convolution]

#print axioms newtonJointFDeriv_proof

end UnforcedLeray.Short.IIb.LTS
