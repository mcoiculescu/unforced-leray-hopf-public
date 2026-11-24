import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Der
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Val
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L1

/-!
# `PartIII-b:C/grad/3/4/1/1/3/2`: x-local majorants of the lattice terms of `h^p_A`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`hpXData` : on the ball of radius `1` around `x`, the `j`-th term `gradHpTm i` is differentiable
in `x` and its `x`-derivative is dominated by `2 C gradF M g₁ j`, where `g₁` is the summable
Gaussian majorant of `gradW` (`gradW_ball_majorant`), `C` is the `∂_q, ∂_η` envelope constant
(`gradHpDerEnv`).  The value summability at `(s, x)` comes from `gradHpValEnv`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A real-valued derivative of a function on `ℝ × ℝ` is bounded by the sum of its two basis
values. -/
lemma norm_fderiv_le_basis_real (F : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    ‖fderiv ℝ F y‖ ≤ |fderiv ℝ F y (ei 0)| + |fderiv ℝ F y (ei 1)| := by
  set L := fderiv ℝ F y with hLdef
  apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
  intro v
  have hv : L v = v.1 * L (ei 0) + v.2 * L (ei 1) := by
    have h2 : L v = L (v.1 • ei 0 + v.2 • ei 1) := by
      congr 1
      ext <;> simp [ei]
    rw [h2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h1 : |v.1| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le v
  rw [hv, Real.norm_eq_abs]
  calc |v.1 * L (ei 0) + v.2 * L (ei 1)|
      ≤ |v.1 * L (ei 0)| + |v.2 * L (ei 1)| := abs_add_le _ _
    _ = |v.1| * |L (ei 0)| + |v.2| * |L (ei 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |L (ei 0)| + ‖v‖ * |L (ei 1)| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    _ = (|L (ei 0)| + |L (ei 1)|) * ‖v‖ := by ring

/-- Each component of the `j`-th lattice term of `h^p_A` is differentiable in `x`. -/
lemma gradHpTm_diff (i : Fin 2) (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (s : ℝ)
    (y : ℝ × ℝ) : DifferentiableAt ℝ (gradHpTm i ν χ A j s) y := by
  have hfun : gradHpTm i ν χ A j s =
      fun z => if i = 0 then (drPhi ν χ A s j z).1 else (drPhi ν χ A s j z).2 := by
    funext z
    simp only [gradHpTm, dr_hpA_eq]
  rw [hfun]
  by_cases h : i = 0
  · simp only [if_pos h]
    exact (dr_drPhi_diff ν χ A s j y).fst
  · simp only [if_neg h]
    exact (dr_drPhi_diff ν χ A s j y).snd

theorem hpXData : HpXData := by
  intro ν s χf A hd x i
  have hν : 0 < ν := hd.1
  have hs0 : 0 ≤ gradF ν χf A s := gradF_nonneg ν χf A s
  obtain ⟨C1, -, e1⟩ := gradHpValEnv
  obtain ⟨C2, hC2, e2⟩ := gradHpDerEnv
  obtain ⟨M, g1, hM, hg1, hball⟩ := gradW_ball_majorant ν hν x
  have hK : 0 ≤ C2 * gradF ν χf A s := mul_nonneg hC2 hs0
  have hW := gradW_summable gradLatticeSummable ν hν x
  refine ⟨1, one_pos, fun j => 2 * (C2 * gradF ν χf A s) * M * g1 j,
    hg1.mul_left (2 * (C2 * gradF ν χf A s) * M), ?_, ?_⟩
  · refine Summable.of_norm_bounded (hW.mul_left (C1 * gradF ν χf A s)) (fun j => ?_)
    rw [Real.norm_eq_abs]
    exact e1 ν s χf A hd x i j
  · intro j y hy
    have hyd : dist y x ≤ 1 := (mem_ball.mp hy).le
    refine ⟨gradHpTm_diff i ν χf A j s y, ?_⟩
    calc ‖fderiv ℝ (gradHpTm i ν χf A j s) y‖
        ≤ |fderiv ℝ (gradHpTm i ν χf A j s) y (ei 0)|
          + |fderiv ℝ (gradHpTm i ν χf A j s) y (ei 1)| :=
          norm_fderiv_le_basis_real _ y
      _ ≤ (C2 * gradF ν χf A s) * gradW ν y j + (C2 * gradF ν χf A s) * gradW ν y j :=
          add_le_add (e2 ν s χf A hd y i j).1 (e2 ν s χf A hd y i j).2
      _ ≤ (C2 * gradF ν χf A s) * (M * g1 j) + (C2 * gradF ν χf A s) * (M * g1 j) :=
          add_le_add (mul_le_mul_of_nonneg_left (hball y hyd j) hK)
            (mul_le_mul_of_nonneg_left (hball y hyd j) hK)
      _ = 2 * (C2 * gradF ν χf A s) * M * g1 j := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
