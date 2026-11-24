import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

/-!
# Local integrability of the periodic kernel on the cell (helper for `kerVelSmooth`)

`K_d` is integrable on `C_d ∩ ball(0,1)` (`KerNearFar`), bounded on `C_d \ ball(0,1)`, hence
integrable on every `C_d ∩ S` with `S` measurable of finite measure. Its indicator on the cell is
therefore locally integrable on the plane.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerD_near_integrableOn {d : ℝ} (hd : 1 ≤ d) (j : Fin 2) :
    IntegrableOn (fun z => kerD d z j) (B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) := by
  have hNF0 := kerNearFar
  unfold KerNearFar at hNF0
  obtain ⟨C, hC0, hNF⟩ := hNF0
  obtain ⟨hmeasK, -, -, hnear, -⟩ := hNF d hd
  have hmeas : MeasurableSet (B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) :=
    (B0579.measurableSet_cell d).inter Metric.isOpen_ball.measurableSet
  refine ⟨(hmeasK j).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d z j‖ₑ ≤
      ∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j', ‖kerD d z j'‖ₑ := by
    refine setLIntegral_mono' hmeas fun z _ => ?_
    exact Finset.single_le_sum (f := fun j' => ‖kerD d z j'‖ₑ) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  exact lt_of_le_of_lt hle (lt_of_le_of_lt hnear ENNReal.ofReal_lt_top)

theorem kerD_cell_integrableOn {d : ℝ} (hd : 1 ≤ d) (j : Fin 2) (S : Set (ℝ × ℝ))
    (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    IntegrableOn (fun z => kerD d z j) (B0579.cell d ∩ S) := by
  have hNF0 := kerNearFar
  unfold KerNearFar at hNF0
  obtain ⟨C, hC0, hNF⟩ := hNF0
  obtain ⟨hmeasK, -, -, -, hfar⟩ := hNF d hd
  have hsplit : B0579.cell d ∩ S =
      (B0579.cell d ∩ S ∩ Metric.ball (0 : ℝ × ℝ) 1) ∪
        ((B0579.cell d ∩ S) \ Metric.ball (0 : ℝ × ℝ) 1) := by
    ext z
    simp only [mem_union, mem_inter_iff, mem_diff]
    tauto
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · exact (kerD_near_integrableOn hd j).mono_set (fun z hz => ⟨hz.1.1, hz.2⟩)
  · have hmeasSet : MeasurableSet ((B0579.cell d ∩ S) \ Metric.ball (0 : ℝ × ℝ) 1) :=
      ((B0579.measurableSet_cell d).inter hSm).diff Metric.isOpen_ball.measurableSet
    refine Measure.integrableOn_of_bounded (M := C)
      (ne_top_of_le_ne_top hS (measure_mono (fun z hz => hz.1.2))) (hmeasK j).aestronglyMeasurable ?_
    refine (ae_restrict_mem hmeasSet).mono fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact hfar z hz.1.1 hz.2 j

theorem kerD_indicator_locInt {d : ℝ} (hd : 1 ≤ d) (j : Fin 2) :
    LocallyIntegrable ((B0579.cell d).indicator (fun z => kerD d z j)) volume := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine IntegrableOn.mono_set ?_ hr
  rw [integrableOn_indicator_iff (B0579.measurableSet_cell d)]
  exact kerD_cell_integrableOn hd j _ Metric.isClosed_closedBall.measurableSet
    measure_closedBall_lt_top.ne

end UnforcedLeray.Short.IIIa
