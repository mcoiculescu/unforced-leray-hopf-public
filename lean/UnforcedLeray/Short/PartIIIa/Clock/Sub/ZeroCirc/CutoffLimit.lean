import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves

namespace UnforcedLeray.Short.IIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal

theorem zcCutoffLimit : UnforcedLeray.Short.IIIa.ZCCutoffLimit := by
  unfold UnforcedLeray.Short.IIIa.ZCCutoffLimit
  intro c ω hω
  refine tendsto_integral_of_dominated_convergence (fun x => ‖ω x‖)
    (fun n => hω.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (B0285.cutT_test c n).smooth.continuous).aestronglyMeasurable)
    hω.norm (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (B0285.abs_cutT_le n x)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [B0285.eventually_cutT_eq_one x] with n hn
    rw [hn, Complex.ofReal_one, mul_one]

end UnforcedLeray.Short.IIIa
