import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_Lem
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_1.Pointwise
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof

/-!
# `liftPPointwise_old`: pointwise decay of `p_lift`, Old range `s > 1/ν` (`ϱ < R√ν`, near the axis)

Source `the November 2 reference manuscript`
lines 439-446 (`sct:fluctuation`), 1213-1225, 2541-2552, 2697-2713.

The estimate is derived from the Part I statement `PartI.TrainFluctuationDecay` (the pressure
conjunct, `ρ = 2`, weight `m = 4`, `(ℓ, j) = (0,0), (0,1), (1,0)`): by `lpt_train_bounds`
`(1+|η|)^4 (|p| + ‖Dp‖) ≤ A e^{-a s}` for all ages `s > 0`, and by the chain rule through the
ring chart (`lpc_grad_bound`) with `t = √s = R/ϱ`, `t(1+|y|) ≤ t + R + |η|`, the exponential
absorbs every power of `t` (`lpc_core`), giving `|p_lift|, |∇p_lift| ≤ C(1+|y|)^{-2}` on all of
space, hence on this range (`lpp_seq`).  The theorem is conditional only on that Part I statement
(the repo's convention, as `flatFluctBound_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI

theorem liftPPointwise_old_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, LiftPPointwiseOn (D.level n)
      {y | (D.level n).ν⁻¹ < age (D.level n).ε⁻¹ y} := by
  filter_upwards [lpp_seq hF D hst] with n hn
  exact liftPPointwiseOn_mono (subset_univ _) hn

theorem liftPPointwise_old (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, LiftPPointwiseOn (D.level n)
      {y | (D.level n).ν⁻¹ < age (D.level n).ε⁻¹ y} := by
  have hHN : OverlapHighNormUniform := overlap_highnorm_uniform
  have hOFD : OverlapFluctuationDecay := overlap_fluctuation_decay hHN
  have hMP : OverlapMeanPrimitive := overlap_mean_primitive
  have hMD : OverlapMeanDecay := overlap_mean_decay hHN hOFD hMP
  have hOv : TrainOverlap := trainOverlap_proof hOFD hMD
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  have hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hOFD hOv
  exact liftPPointwise_old_of hFD D hst

end UnforcedLeray.Short.PartIIIb.Concrete

end
