import UnforcedLeray.Analysis.Heat.SobolevSmoothing
import UnforcedLeray.Analysis.Heat.StrongContinuity

/-!
# Positive-time Sobolev continuity of the actual heat semigroup

The actual all-L² heat flow is continuous in the complete weak H¹ and H²
graphs at every positive time. A fixed positive smoothing time and the actual
semigroup law give local factorization through a bounded L²-to-Sobolev map.
No regularity of the datum beyond L² is required. The auxiliary paths are zero
at nonpositive times; no Sobolev continuity at zero is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Heat

open Classical in
/-- Actual H¹ heat values at positive times; zero outside that domain. -/
def heatH1Path (F : L2Space) (t : ℝ) : SobolevGraph.H1 :=
  if ht : 0 < t then heatToH1 ht F else 0

open Classical in
/-- Actual H² heat values at positive times; zero outside that domain. -/
def heatH2Path (F : L2Space) (t : ℝ) : SobolevGraph.H2 :=
  if ht : 0 < t then heatToH2 ht F else 0

@[simp] theorem heatH1Path_pos (F : L2Space) {t : ℝ} (ht : 0 < t) :
    heatH1Path F t = heatToH1 ht F := by simp only [heatH1Path, dite_eq_left ht]

@[simp] theorem heatH2Path_pos (F : L2Space) {t : ℝ} (ht : 0 < t) :
    heatH2Path F t = heatToH2 ht F := by simp only [heatH2Path, dite_eq_left ht]

theorem heatH1Path_value (F : L2Space) {t : ℝ} (ht : 0 < t) :
    (heatH1Path F t).value = heatOperator t F := by
  rw [heatH1Path_pos F ht, heatToH1_value, heatOperator_pos ht]

theorem heatH2Path_value (F : L2Space) {t : ℝ} (ht : 0 < t) :
    (heatH2Path F t).value = heatOperator t F := by
  rw [heatH2Path_pos F ht, heatToH2_value, heatOperator_pos ht]

/-- Fixed-time smoothing factorization in the actual H¹ graph. -/
theorem heatH1Path_factor (F : L2Space) {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    heatH1Path F t = heatToH1 hr (heatOperator (t-r) F) := by
  apply SobolevGraph.H1.ext
  rw [heatH1Path_value F (hr.trans hrt), heatToH1_value, ← heatOperator_pos hr]
  have h := congrArg (fun A : L2Space →L[ℝ] L2Space => A F)
    (heatOperator_add_time hr.le (sub_nonneg.mpr hrt.le))
  simpa only [show r+(t-r)=t by ring, ContinuousLinearMap.comp_apply] using h

/-- Fixed-time smoothing factorization in the actual H² graph. -/
theorem heatH2Path_factor (F : L2Space) {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    heatH2Path F t = heatToH2 hr (heatOperator (t-r) F) := by
  apply SobolevGraph.H2.ext
  rw [heatH2Path_value F (hr.trans hrt), heatToH2_value, ← heatOperator_pos hr]
  have h := congrArg (fun A : L2Space →L[ℝ] L2Space => A F)
    (heatOperator_add_time hr.le (sub_nonneg.mpr hrt.le))
  simpa only [show r+(t-r)=t by ring, ContinuousLinearMap.comp_apply] using h

/-- Strong H¹ continuity at every positive time for arbitrary L² data. -/
theorem heatH1Path_continuousAt (F : L2Space) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatH1Path F) t := by
  have hr : 0 < t/2 := by positivity
  have hc : Continuous (fun s : ℝ => heatToH1 hr (heatOperator (s-t/2) F)) :=
    (heatToH1 hr).continuous.comp
      ((heatOperator_strongly_continuous F).comp (continuous_id.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  exact heatH1Path_factor F hr hs

/-- Strong H² continuity at every positive time for arbitrary L² data. -/
theorem heatH2Path_continuousAt (F : L2Space) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatH2Path F) t := by
  have hr : 0 < t/2 := by positivity
  have hc : Continuous (fun s : ℝ => heatToH2 hr (heatOperator (s-t/2) F)) :=
    (heatToH2 hr).continuous.comp
      ((heatOperator_strongly_continuous F).comp (continuous_id.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  exact heatH2Path_factor F hr hs

theorem heatH1Path_continuousOn (F : L2Space) :
    ContinuousOn (heatH1Path F) (Ioi 0) :=
  fun _ ht => (heatH1Path_continuousAt F ht).continuousWithinAt

theorem heatH2Path_continuousOn (F : L2Space) :
    ContinuousOn (heatH2Path F) (Ioi 0) :=
  fun _ ht => (heatH2Path_continuousAt F ht).continuousWithinAt

/-- Every positive closed time slab has actual H² continuity. -/
theorem heatH2Path_continuousOn_slab (F : L2Space) {δ T : ℝ} (hδ : 0 < δ) :
    ContinuousOn (heatH2Path F) (Icc δ T) :=
  (heatH2Path_continuousOn F).mono (fun _ ht => hδ.trans_le ht.1)

end UnforcedLeray.Heat
