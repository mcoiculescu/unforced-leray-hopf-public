import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.PsiS

/-!
Global-regularity version of `psipAMixedX_of` (source 4973-4980): the `s`-derivative formula
comes from `psipA_hasDerivAt_glob`; only the Gaussian bounds `PAMXSVBound`, `PAMXBallMajor` remain.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipAMixedX_glob (h2 : PAMXSVBound) (h3 : PAMXBallMajor) (ν : ℝ) (hν : 0 < ν)
    (χf : ℝ → ℝ) (A : ℝ → Mat3) (hC : ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y => deriv (fun s' => psipA ν χf A s' y) s) x := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hs0 : 0 < s := hs
  have hfun : (fun y => deriv (fun s' => psipA ν χf A s' y) s) =
      fun y => ∑' n : ℤ, sV ν (xj ν n y) (Ay ν χf A s) (deriv (Ay ν χf A) s) s :=
    funext fun y => (psipA_hasDerivAt_glob ν hν χf A hC s hs y).deriv
  rw [hfun]
  set Mt := Ay ν χf A s with hMt
  set D := deriv (Ay ν χf A) s with hD
  have hMb : ∀ i j, |Mt i j| ≤ ‖Mt‖ := fun i j => sp_entry_le _ i j
  have hDb : ∀ i j, |D i j| ≤ ‖D‖ := fun i j => sp_entry_le _ i j
  obtain ⟨C, hC0, hC⟩ := h2 ν hν ‖Mt‖ ‖D‖ (norm_nonneg _) (norm_nonneg _)
  obtain ⟨u, hu, hub⟩ := h3 ν hν s ha1 x C hC0
  have hc0 : 0 ≤ 10 * ν * ‖Mt‖ + 8 * ‖D‖ := by positivity
  obtain ⟨u', hu', hub'⟩ := h3 ν hν s ha1 x _ hc0
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    le_trans (by positivity) (hub n x (by simp))
  have hF : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      HasFDerivAt (fun w => sV ν (xj ν n w) Mt D s)
        ((fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z := by
    intro n z _
    have hd := (hC Mt D s ha1 hMb hDb (xj ν n z)).1
    exact hd.hasFDerivAt.comp z (xj_hasFDerivAt ν n z)
  have hbound : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      ‖(fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))‖ ≤ u n := by
    intro n z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (hu0 n)
    intro v
    have h1' := (hC Mt D s ha1 hMb hDb (xj ν n z)).2 v
    have h2' := hub n z (mem_ball_iff_norm.mp hz)
    have hv := norm_nonneg v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    calc ‖(fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)) v‖
        ≤ C * ‖v‖ * ((1 + ‖xj ν n z‖) ^ 5 *
            Real.exp (-(sq2 (xj ν n z)) / (4 * ageA ν s))) := h1'
      _ = ‖v‖ * (C * ((1 + ‖xj ν n z‖) ^ 5 *
            Real.exp (-(sq2 (xj ν n z)) / (4 * ageA ν s)))) := by ring
      _ ≤ ‖v‖ * u n := mul_le_mul_of_nonneg_left h2' hv
      _ = u n * ‖v‖ := by ring
  have hf0 : Summable (fun n : ℤ => sV ν (xj ν n x) Mt D s) := by
    refine Summable.of_norm_bounded hu' (fun n => ?_)
    rw [Real.norm_eq_abs]
    have b1 := sV_bound ν hν (xj ν n x) ‖Mt‖ ‖D‖ Mt D s hs0 hMb hDb
    have b2 := hub' n x (by simp)
    have hR1 : (1:ℝ) ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
    have hE : 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    have hp : (1 + ‖xj ν n x‖) ^ 4 ≤ (1 + ‖xj ν n x‖) ^ 5 :=
      pow_le_pow_right₀ hR1 (by norm_num)
    refine b1.trans (le_trans ?_ b2)
    have := mul_le_mul_of_nonneg_right hp hE
    calc (10 * ν * ‖Mt‖ + 8 * ‖D‖) * (1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))
        = (10 * ν * ‖Mt‖ + 8 * ‖D‖) * ((1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hc0
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => sV ν (xj ν n w) Mt D s)
    (f' := fun n z => (fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
    (u := u) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hF hbound
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt


end UnforcedLeray.Short.PartIIIb.Concrete
