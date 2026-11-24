import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable

/-!
`x`-only version of `hpADiffX_of` (source 4973-4980).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpADiffX_glob (hmaj : HpTermMajorant) (ν : ℝ) (hν : 0 < ν) (χf : ℝ → ℝ)
    (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (hpA ν χf A s) x := by
  have hC2 := vjContDiff2
  obtain ⟨u, hu, hb⟩ := hmaj ν hν s hs (Ay ν χf A s) x
  set M := Ay ν χf A s with hM
  have hd : ∀ j : ℤ, Differentiable ℝ (fun w => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w))) := by
    intro j
    have hV : Differentiable ℝ (Vj ν s j) := (hC2 ν s j).differentiable (by norm_num)
    have hDV : Differentiable ℝ (fderiv ℝ (Vj ν s j)) :=
      ((hC2 ν s j).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have h1 : Differentiable ℝ (fun w => merApply M (Vj ν s j w)) := by
      unfold merApply
      have h1 := hV.fst
      have h2 := hV.snd
      fun_prop
    have h2 : Differentiable ℝ (fun w : ℝ × ℝ => merApply M (xj ν j w)) := by
      unfold merApply xj
      fun_prop
    exact h1.sub (hDV.clm_apply h2)
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (j : ℤ) (w : ℝ × ℝ) => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w)))
    (f' := fun j z => fderiv ℝ (fun w => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w))) z)
    (u := u) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
    (fun j z _ => (hd j z).hasFDerivAt)
    (fun j z hz => hb j z (mem_ball_iff_norm.mp hz))
    (Metric.mem_ball_self one_pos) (hpPsiTermSummable ν χf A s x hν hs).1 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt


end UnforcedLeray.Short.PartIIIb.Concrete
