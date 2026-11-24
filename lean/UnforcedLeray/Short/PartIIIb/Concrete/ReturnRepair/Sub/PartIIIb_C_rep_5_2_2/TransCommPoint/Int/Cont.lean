import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Half2

/-!
# Continuity along the half line `ρ ↦ (ρ,0,z)` and integrability of the majorant
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcd_int_shift (a r : ℝ) (hr : 0 < r - a) :
    IntegrableOn (fun ρ : ℝ => (ρ - a) ^ (-(3 / 2 : ℝ))) (Ioi r) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (c := r - a) (by norm_num) hr
  have h2 : Integrable ((Ioi (r - a)).indicator (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 h
  have h3 := h2.comp_sub_right a
  refine (integrable_indicator_iff measurableSet_Ioi).1 ?_
  refine h3.congr (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [indicator, mem_Ioi]
  by_cases h : r < ρ
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

theorem tcd_pt_cont (z : ℝ) : Continuous (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) := by
  fun_prop

theorem tcd_pt_maps {rOut : ℝ} (hr : 0 ≤ rOut) (z : ℝ) :
    MapsTo (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) (Ioi rOut) {y : Space | rOut < ϱ y} := by
  intro ρ hρ
  show rOut < ϱ (!₂[ρ, 0, z] : Space)
  rw [tcd_varrho (hr.trans (le_of_lt hρ))]
  exact hρ

theorem tcd_cont_val {Z : Space → Space} {rOut : ℝ} (hr : 0 ≤ rOut)
    (hZ : ContDiffOn ℝ 2 Z {y : Space | rOut < ϱ y}) (z : ℝ) :
    ContinuousOn (fun ρ : ℝ => Z (!₂[ρ, 0, z] : Space)) (Ioi rOut) :=
  hZ.continuousOn.comp (tcd_pt_cont z).continuousOn (tcd_pt_maps hr z)

theorem tcd_cont_fderiv {Z : Space → Space} {rOut : ℝ} (hr : 0 ≤ rOut)
    (hZ : ContDiffOn ℝ 2 Z {y : Space | rOut < ϱ y}) (z : ℝ) :
    ContinuousOn (fun ρ : ℝ => fderiv ℝ Z (!₂[ρ, 0, z] : Space)) (Ioi rOut) := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  exact (hZ.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp (tcd_pt_cont z).continuousOn
    (tcd_pt_maps hr z)

theorem tcd_cont_hess {Z : Space → Space} {rOut : ℝ} (hr : 0 ≤ rOut)
    (hZ : ContDiffOn ℝ 2 Z {y : Space | rOut < ϱ y}) (z : ℝ) :
    ContinuousOn (fun ρ : ℝ => fderiv ℝ (fderiv ℝ Z) (!₂[ρ, 0, z] : Space)) (Ioi rOut) := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ Z) {y : Space | rOut < ϱ y} :=
    hZ.fderiv_of_isOpen hU (by norm_num)
  exact (h1.continuousOn_fderiv_of_isOpen hU le_rfl).comp (tcd_pt_cont z).continuousOn
    (tcd_pt_maps hr z)

theorem tcd_cont_lap {Z : Space → Space} {rOut : ℝ} (hr : 0 ≤ rOut)
    (hZ : ContDiffOn ℝ 2 Z {y : Space | rOut < ϱ y}) (z : ℝ) :
    ContinuousOn (fun ρ : ℝ => physLap Z (!₂[ρ, 0, z] : Space)) (Ioi rOut) := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hH := tcd_cont_hess hr hZ z
  have e : ∀ ρ ∈ Ioi rOut, physLap Z (!₂[ρ, 0, z] : Space) =
      ∑ j : Fin 3, fderiv ℝ (fderiv ℝ Z) (!₂[ρ, 0, z] : Space) (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector j) := by
    intro ρ hρ
    have hmem := tcd_pt_maps hr z hρ
    have hcd : ContDiffAt ℝ 2 Z (!₂[ρ, 0, z] : Space) := hZ.contDiffAt (hU.mem_nhds hmem)
    unfold physLap physPd2 physPd
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact tcd_fderiv_dir hcd _ _
  refine ContinuousOn.congr ?_ e
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  exact (hH.clm_apply continuousOn_const).clm_apply continuousOn_const

end UnforcedLeray.Short.PartIIIb.Concrete

end
