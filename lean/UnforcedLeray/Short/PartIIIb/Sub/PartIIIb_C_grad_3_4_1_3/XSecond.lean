import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.PsipAXSecond

/-!
`x`-only version of `psipAXSecond` (source 4973-4980): no regularity of `A` is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipAXSecond_glob (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ)
    (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) x := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have heq : (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) =
      fun y => ∑' n : ℤ, psiPhiD ν s (Ay ν χf A s) (xj ν n y) (0, 1) :=
    funext fun y => fderiv_psipA_ei ν χf A s hν hs y
  rw [heq]
  have hu := ub4_summable ν s ha1 x ‖Ay ν χf A s‖ hν
  obtain ⟨-, hsum⟩ := psiPhi_tsum_hasFDerivAt ν s hν hs (Ay ν χf A s) x
  have hf0 : Summable (fun n : ℤ => psiPhiD ν s (Ay ν χf A s) (xj ν n x) (0, 1)) := by
    have := hsum.mapL (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))
    simp only [ContinuousLinearMap.apply_apply] at this
    exact this.congr fun n => fderiv_term ν s (Ay ν χf A s) n x _
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => psiPhiD ν s (Ay ν χf A s) (xj ν n w) (0, 1))
    (f' := fun n z => fderiv ℝ (fun u => psiPhiD ν s (Ay ν χf A s) (xj ν n u) (0, 1)) z)
    (u := ub4 ν s x ‖Ay ν χf A s‖) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
    (fun n z _ => (G_diff ν s (Ay ν χf A s) n z).hasFDerivAt)
    (fun n z hz => fderiv_G_bound ν s ha1 (Ay ν χf A s) x z (mem_ball_iff_norm.mp hz) n)
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt


end UnforcedLeray.Short.PartIIIb.Concrete
