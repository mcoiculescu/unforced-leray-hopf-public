import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# Fubini on a cell: `∫ h(y) f(t,y) dy` is integrable in `t`

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem cellIntegrable : CellIntegrable := by
  intro P hP f R hf h hcont hzero
  have hprod : (volume.restrict (Ioc 0 P)).prod (volume.restrict (closedBall (0 : Space) R)) =
      volume.restrict (Ioc 0 P ×ˢ closedBall (0 : Space) R) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod ℝ Space]
  have hf' : Integrable f
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict (closedBall (0 : Space) R))) := by
    rw [hprod]
    exact hf
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ y : Space, ‖h y‖ ≤ max C 0 := by
    intro y
    by_cases hy : ‖y‖ ≤ R
    · exact le_max_of_le_left (hC y (mem_closedBall_zero_iff.2 hy))
    · rw [hzero y (not_le.mp hy)]
      simp
  have hmeas : AEStronglyMeasurable (fun p : ℝ × Space => h p.2)
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict (closedBall (0 : Space) R))) :=
    (hcont.comp continuous_snd).aestronglyMeasurable
  have H1 : Integrable (fun p : ℝ × Space => h p.2 * f p)
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict (closedBall (0 : Space) R))) :=
    Integrable.bdd_mul hf' hmeas (Filter.Eventually.of_forall fun p => hbound p.2)
  have H4 : Integrable (fun t : ℝ => ∫ y in closedBall (0 : Space) R, h y * f (t, y))
      (volume.restrict (Ioc 0 P)) :=
    H1.integral_prod_left
  have H3 : ∀ t : ℝ, ∫ y in closedBall (0 : Space) R, h y * f (t, y) =
      ∫ y : Space, h y * f (t, y) := by
    intro t
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y (not_le.mp (fun hle => hy (mem_closedBall_zero_iff.2 hle))), zero_mul]
  have H5 : (fun t : ℝ => ∫ y : Space, h y * f (t, y)) =
      fun t : ℝ => ∫ y in closedBall (0 : Space) R, h y * f (t, y) :=
    funext fun t => (H3 t).symm
  unfold IntegrableOn
  rw [H5]
  exact H4

end UnforcedLeray.Short.PartIIIb.Concrete
