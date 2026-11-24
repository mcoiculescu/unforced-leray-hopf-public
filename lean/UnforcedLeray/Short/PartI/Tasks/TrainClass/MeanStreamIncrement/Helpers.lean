import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanVelDecay
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStressDecay
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1

/-!
# Helpers for `PartI:TC/6` (`MeanStreamIncrement`)

Source of record: `the November 2 reference manuscript`, lines 397-404.
Derivative and bound facts for the mean velocity `u = meanVel1` and the mean stress `g`
at a fixed age `s ≥ 0`, and the splitting `S(s,0) = S(s,R) + ∫₀^R u(s,t) dt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The mean velocity has the η-derivative `hmean c G1`, `G1 z = ∂_η v₁(z)`, at every `η`. -/
theorem msi_hasDerivAt_meanVel1 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (η : ℝ) :
    HasDerivAt (meanVel1 tr s)
      (hmean c (fun z : Plane => fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0) η) η := by
  have hV3 : ContDiff ℝ ∞ (tr.v s) := bucVel_vslice_contDiff tr hs
  have hV2 : ContDiff ℝ 1 (fderiv ℝ (tr.v s)) := hV3.fderiv_right (m := 1) (by simp)
  have hcontFD : Continuous (fderiv ℝ (tr.v s)) := hV2.continuous
  have hcontG : Continuous (fun z : Plane => fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0) :=
    (PiLp.continuous_apply _ _ 0).comp (hcontFD.clm_apply continuous_const)
  have hcont0 : Continuous (fun z : Plane => tr.v s z 0) :=
    (PiLp.continuous_apply _ _ 0).comp hV3.continuous
  have hpart : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => tr.v s (q, y) 0)
      (fderiv ℝ (tr.v s) (q, e) ((0 : ℝ), (1 : ℝ)) 0) e := by
    intro q e
    have hp : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    have hdiff : DifferentiableAt ℝ (tr.v s) (q, e) := hV3.differentiable (by simp) (q, e)
    have hA : HasDerivAt (fun y : ℝ => tr.v s (q, y)) (fderiv ℝ (tr.v s) (q, e) ((0 : ℝ), (1 : ℝ))) e :=
      hdiff.hasFDerivAt.comp_hasDerivAt e hp
    exact (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt e hA
  exact trainMeanV1_hasDerivAt_hmean (c := c) (f := fun z : Plane => tr.v s z 0)
    (g := fun z : Plane => fderiv ℝ (tr.v s) z ((0 : ℝ), (1 : ℝ)) 0) hcont0 hcontG hpart η

/-- `|∂_η u(s,η)| ≤ M₁` at every `η`, when the first order derivatives of `v(s,·)` are bounded by `M₁`. -/
theorem msi_deriv_meanVel1_bound {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) {M1 : ℝ} (hM1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ M1) (η : ℝ) :
    |deriv (meanVel1 tr s) η| ≤ M1 := by
  rw [(msi_hasDerivAt_meanVel1 tr hs η).deriv]
  refine bucVel_hmean_abs_le hc _ η M1 (fun q => ?_)
  show |fderiv ℝ (tr.v s) (q, η) ((0 : ℝ), (1 : ℝ)) 0| ≤ M1
  have h1 : |fderiv ℝ (tr.v s) (q, η) ((0 : ℝ), (1 : ℝ)) 0| ≤
      ‖fderiv ℝ (tr.v s) (q, η) ((0 : ℝ), (1 : ℝ))‖ := by
    have := PiLp.norm_apply_le (fderiv ℝ (tr.v s) (q, η) ((0 : ℝ), (1 : ℝ))) 0
    simpa [Real.norm_eq_abs] using this
  have h2 : ‖fderiv ℝ (tr.v s) (q, η) ((0 : ℝ), (1 : ℝ))‖ ≤
      ‖fderiv ℝ (tr.v s) (q, η)‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
    (fderiv ℝ (tr.v s) (q, η)).le_opNorm _
  have h3 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have h4 : ‖fderiv ℝ (tr.v s) (q, η)‖ ≤ M1 := by
    rw [← norm_iteratedFDeriv_one]
    exact hM1 _
  rw [h3, mul_one] at h2
  linarith

/-- `|g(s,η)| ≤ M₀²` when `‖v(s,·)‖ ≤ M₀`. -/
theorem msi_meanStress_bound {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) {s : ℝ}
    {M0 : ℝ} (hM0 : ∀ z : Plane, ‖tr.v s z‖ ≤ M0) (η : ℝ) :
    |meanStress tr s η| ≤ M0 * M0 := by
  refine bucStress_hmean_abs_le hc _ η (M0 * M0) (fun q => ?_)
  show |tr.v s (q, η) 0 * tr.v s (q, η) 1| ≤ M0 * M0
  have hcoord : ∀ i : Fin 2, |tr.v s (q, η) i| ≤ M0 := fun i => by
    have h := PiLp.norm_apply_le (tr.v s (q, η)) i
    rw [Real.norm_eq_abs] at h
    exact h.trans (hM0 _)
  rw [abs_mul]
  exact mul_le_mul (hcoord 0) (hcoord 1) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hcoord 0))

/-- Splitting of the mean stream at the origin: `S(s,0) = S(s,R) + ∫₀^R u(s,t) dt`. -/
theorem msi_stream_split {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (R : ℝ) :
    meanStream tr s 0 = meanStream tr s R + ∫ t in (0 : ℝ)..R, meanVel1 tr s t := by
  have hcontU : Continuous (meanVel1 tr s) :=
    continuous_iff_continuousAt.2 fun x => (msi_hasDerivAt_meanVel1 tr hs x).continuousAt
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun e : ℝ => meanStream tr s e) ((fun x => -meanVel1 tr s x) x) x :=
    fun x _ => bucVel_S_deriv tr hs x
  have hint : IntervalIntegrable (fun x => -meanVel1 tr s x) volume 0 R :=
    (hcontU.neg).intervalIntegrable 0 R
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at key
  linarith

end UnforcedLeray.Short.PartI
