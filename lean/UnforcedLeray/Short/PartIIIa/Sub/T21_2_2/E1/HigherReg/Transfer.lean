import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Scale

/-!
# Transfer of the weighted `L²` integrability to the moving cell (SP 3036-3047)

`∫_{C_d} p_d⁻¹ |g(√a ·)|²` is finite when `g ∈ L²(C_c, ⟨x⟩^{-2m})`, `d = c/√a`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Real

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem transfer_weight_int (m c R : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hR : 0 < R)
    (g : ℝ × ℝ → ℂ) (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun y => periodicWeight (-m) (c / R) y * ‖g (R • y)‖ ^ 2)
      (B0579.cell (c / R)) := by
  set F : ℝ × ℝ → ℝ := fun x => B0579.jb x ^ (-m) * ‖g x‖ ^ 2 with hF
  have hI : IntegrableOn F (B0579.cell c) := by
    have h2 : Integrable (fun x => ‖g x‖ ^ 2) (B0579.cellMeasure c (-m)) :=
      (memLp_two_iff_integrable_sq_norm hg.1).1 hg
    have h3 := (B0579.integrable_cellMeasure_iff c (-m)).1 h2
    refine h3.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [hF, NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  have hFi : Integrable ((B0579.cell c).indicator F) :=
    (integrable_indicator_iff (B0579.measurableSet_cell c)).2 hI
  have hC : Integrable (fun y : ℝ × ℝ => (B0579.cell c).indicator F (R • y)) :=
    hFi.comp_smul hR.ne'
  have hG : IntegrableOn (fun y : ℝ × ℝ => F (R • y)) (B0579.cell (c / R)) := by
    rw [← integrable_indicator_iff (B0579.measurableSet_cell (c / R))]
    refine hC.congr (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ B0579.cell (c / R)
    · have hy' : R • y ∈ B0579.cell c := (smul_mem_cell_iff c R hR y).2 hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hy']
    · have hy' : R • y ∉ B0579.cell c := fun h => hy ((smul_mem_cell_iff c R hR y).1 h)
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  have hjb : ∀ x : ℝ × ℝ, B0579.jb x ^ m * B0579.jb x ^ (-m) = 1 := fun x => by
    rw [← Real.rpow_add (B0579.jb_pos x)]
    simp
  have hmeasW : Measurable (fun y : ℝ × ℝ =>
      periodicWeight (-m) (c / R) y * B0579.jb (R • y) ^ m) := by
    unfold periodicWeight B0579.jb
    fun_prop
  refine Integrable.mono' (hG.const_mul (((4 / π ^ 2) / (1 + R ^ 2)) ^ (-m))) ?_ ?_
  · refine (hmeasW.aestronglyMeasurable.mul hG.1).congr
      (Filter.Eventually.of_forall fun y => ?_)
    have := hjb (R • y)
    simp only [hF, Pi.mul_apply]
    linear_combination (periodicWeight (-m) (c / R) y * ‖g (R • y)‖ ^ 2) * this
  · refine (ae_restrict_mem (B0579.measurableSet_cell (c / R))).mono fun y hy => ?_
    have hn : 0 ≤ ‖g (R • y)‖ ^ 2 := by positivity
    have hw := periodicWeight_le_jb m c R hm hc hR y hy
    have hwnn : 0 ≤ periodicWeight (-m) (c / R) y := by
      unfold periodicWeight
      positivity
    rw [Real.norm_of_nonneg (mul_nonneg hwnn hn)]
    simp only [hF]
    calc periodicWeight (-m) (c / R) y * ‖g (R • y)‖ ^ 2
        ≤ ((4 / π ^ 2) / (1 + R ^ 2)) ^ (-m) * B0579.jb (R • y) ^ (-m) * ‖g (R • y)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw hn
      _ = ((4 / π ^ 2) / (1 + R ^ 2)) ^ (-m) * (B0579.jb (R • y) ^ (-m) * ‖g (R • y)‖ ^ 2) := by
          ring

end UnforcedLeray.Short.IIIa.AdjE1
