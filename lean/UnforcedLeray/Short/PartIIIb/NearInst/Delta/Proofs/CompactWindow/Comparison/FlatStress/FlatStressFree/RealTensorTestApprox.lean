import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.GenericStressReal

/-!
# `PartIII-b:C/near/delta/8/2/3/4/org/4`: `RealTensorTestApprox` (source 1678)

First half of `genericStressReal` (`GenericStressReal.lean`): real smooth tensor tests
approximate a real tensor in `H_T`.  Take smooth tests `M n` with `‖F - M n‖ < 1/(n+1)`, replace
them by their componentwise real parts (`gsrReFn`), which stay smooth tensor tests and do not
increase the distance to the real field `F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

theorem realTensorTestApprox : RealTensorTestApprox := by
  intro c hc F hF
  choose M hMtest hMl hMdist using fun n : ℕ =>
    Masked.tensorTestDense c hc F (1 / ((n : ℝ) + 1)) (by positivity)
  have hN : ∀ n, MemLp (gsrReFn (M n)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
    intro n
    refine MemLp.of_le (hMl n) ?_ (Eventually.of_forall fun p => gsrRe_norm_le (M n p))
    exact (gsrReL.continuous.comp_aestronglyMeasurable (hMl n).aestronglyMeasurable)
  refine ⟨fun n => gsrReFn (M n), hN, fun n => gsrReFn_isTensorTest (hMtest n),
    fun n p k => gsrReFn_realValued (M n) p k, ?_⟩
  have hdist : ∀ n : ℕ, ‖(hN n).toLp (gsrReFn (M n)) - F‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [norm_sub_rev]
    exact (gsr_dist_le c F hF (M n) (hMl n) (hN n)).trans (hMdist n).le
  refine squeeze_zero (fun n => norm_nonneg _) hdist tendsto_one_div_add_atTop_nhds_zero_nat

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
