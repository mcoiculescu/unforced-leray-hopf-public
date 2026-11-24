import UnforcedLeray.Analysis.Heat.StrongContinuity
import UnforcedLeray.Consequences

/-!
# The actual raw heat flow and its strong initial datum

The spatial field is the ordinary Gaussian convolution at every positive time
and equals its supplied datum at time zero. The norm and topology statements
refer to exactly the concrete L² and trace conventions of Statement.lean.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace UnforcedLeray.Heat

open Classical in
def flow (f : SpatialField) : Velocity :=
  fun t => if 0 < t then average t f else f

theorem flow_pos (f : SpatialField) {t : ℝ} (ht : 0 < t) :
    flow f t = average t f := by simp only [flow, ite_eq_left ht]

theorem flow_nonpos (f : SpatialField) {t : ℝ} (ht : t ≤ 0) : flow f t = f := by
  simp only [flow, ite_eq_right (not_lt.mpr ht)]

@[simp] theorem flow_zero (f : SpatialField) : flow f 0 = f := flow_nonpos f le_rfl

theorem flow_memLp {f : SpatialField} (hf : MemLp f 2 volume) (t : ℝ) :
    MemLp (flow f t) 2 volume := by
  by_cases ht : 0 < t
  · rw [flow_pos f ht]
    exact memLp_convolution (kernel_integrable ht) hf
  · rw [flow_nonpos f (le_of_not_gt ht)]
    exact hf

/-- The actual pointwise flow is represented by precisely the constructed heat operator. -/
theorem toL2_flow {f : SpatialField} (hf : MemLp f 2 volume) (t : ℝ) :
    toL2 (flow f t) = heatOperator t (toL2 f) := by
  by_cases ht : 0 < t
  · apply Lp.ext
    have hraw := average_congr_ae (coeFn_toL2 hf) t
    have he : (heatOperator t (toL2 f) : SpatialField) =ᵐ[volume] flow f t := by
      rw [flow_pos f ht]
      exact (heatOperator_rep ht (toL2 f)).trans
        (Eventually.of_forall (fun x => congrFun hraw x))
    exact (coeFn_toL2 (flow_memLp hf t)).trans he.symm
  · rw [flow_nonpos f (le_of_not_gt ht), heatOperator_nonpos (le_of_not_gt ht)]
    rfl

/-- Real L² norm contraction for the actual field representative. -/
theorem flow_l2Norm_le {f : SpatialField} (hf : MemLp f 2 volume) (t : ℝ) :
    l2Norm (flow f t) ≤ l2Norm f := by
  rw [← norm_toL2 (flow_memLp hf t), toL2_flow hf]
  exact (heatOperator_apply_norm_le t (toL2 f)).trans_eq (norm_toL2 hf)

theorem flow_continuousL2 {f : SpatialField} (hf : MemLp f 2 volume) :
    Continuous (fun t => toL2 (flow f t)) := by
  simp_rw [toL2_flow hf]
  exact heatOperator_strongly_continuous (toL2 f)

/-- Strong initial trace in the manuscript's explicit real L² norm. -/
theorem flow_strong_initial_trace {f : SpatialField} (hf : MemLp f 2 volume) :
    Tendsto (fun t => l2Norm (flow f t - f)) (𝓝[Set.Ici 0] 0) (𝓝 0) := by
  have he : (fun t => l2Norm (flow f t - f)) =
      fun t => dist (toL2 (flow f t)) (toL2 f) :=
    funext (fun t => (dist_toL2 (flow_memLp hf t) hf).symm)
  rw [he]
  have hc := (flow_continuousL2 hf).dist (continuous_const (y := toL2 f))
  have h := hc.continuousAt.tendsto (x := (0 : ℝ))
  simpa only [flow_zero, dist_self] using h.mono_left nhdsWithin_le_nhds

/-- The same trace holds on the precise closed interval filter used in the main statement. -/
theorem flow_strong_initial_trace_Icc {f : SpatialField} (hf : MemLp f 2 volume) (T : ℝ) :
    Tendsto (fun t => l2Norm (flow f t - f)) (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0) :=
  (flow_strong_initial_trace hf).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)

end UnforcedLeray.Heat
