import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull

/-!
# `FmPointwise` (source 3996-4011)

Off the axis `srcNorm (cartLift R c f) = gAx R c f` (`cartLiftNormOffAxis_holds`), and the axis is
Lebesgue-null (`axisNull_holds`), so for almost every `z` the integrand of `fullMaj` is bounded by
`K` times the integrand of `dilMajG`, using `gradKNorm ≤ K · fmKer` pointwise in `l ∈ (0,1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem fmPointwise : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmPointwise := by
  intro R c ν μ K hK f x
  have hN : volume {z : UnforcedLeray.Space | hRad z = 0} = 0 :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.axisNull_holds
  have hae : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space), hRad z ≠ 0 := by
    rw [ae_iff]
    simpa using hN
  unfold fullMaj dilMajG
  calc _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal K * (ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : UnforcedLeray.Space, fmKer ν l (chartY R x - l • z) *
            gAx R c f (chartTau R x + 2 * Real.log l) z) := by
        refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
        have hmain : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space),
            gradKNorm (ν * (1 - l ^ 2)) (chartY R x - l • z) *
              ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
                (cartLift R c f (chartTau R x + 2 * Real.log l) z)) ≤
            ENNReal.ofReal K * (fmKer ν l (chartY R x - l • z) *
              gAx R c f (chartTau R x + 2 * Real.log l) z) := by
          filter_upwards [hae] with z hz
          have hsrc : ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
              (cartLift R c f (chartTau R x + 2 * Real.log l) z)) =
              gAx R c f (chartTau R x + 2 * Real.log l) z :=
            UnforcedLeray.Short.PartIIIb.NearInst.Masked.cartLiftNormOffAxis_holds R c f
              (chartTau R x + 2 * Real.log l) z hz
          rw [hsrc]
          calc gradKNorm (ν * (1 - l ^ 2)) (chartY R x - l • z) *
                gAx R c f (chartTau R x + 2 * Real.log l) z
              ≤ (ENNReal.ofReal K * fmKer ν l (chartY R x - l • z)) *
                gAx R c f (chartTau R x + 2 * Real.log l) z :=
                mul_le_mul_of_nonneg_right (hK l hl _) (by positivity)
            _ = ENNReal.ofReal K * (fmKer ν l (chartY R x - l • z) *
                gAx R c f (chartTau R x + 2 * Real.log l) z) := by ring
        calc ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
              gradKNorm (ν * (1 - l ^ 2)) (chartY R x - l • z) *
                ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
                  (cartLift R c f (chartTau R x + 2 * Real.log l) z))
            ≤ ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
              ENNReal.ofReal K * (fmKer ν l (chartY R x - l • z) *
                gAx R c f (chartTau R x + 2 * Real.log l) z) :=
              mul_le_mul_of_nonneg_left (lintegral_mono_ae hmain) (by positivity)
          _ = ENNReal.ofReal K * (ENNReal.ofReal (l ^ (2 * μ + 2)) *
              ∫⁻ z : UnforcedLeray.Space, fmKer ν l (chartY R x - l • z) *
                gAx R c f (chartTau R x + 2 * Real.log l) z) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              ring
    _ = ENNReal.ofReal K * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : UnforcedLeray.Space, fmKer ν l (chartY R x - l • z) *
            gAx R c f (chartTau R x + 2 * Real.log l) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
