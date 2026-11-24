import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The pointwise majorant by the dilated positive kernel (source 3996-3998)

At a chart point `x` of age `0 < x.1 < sm`, `farMajE` is at most `dilMaj` with truncation radius
`d = (1 - e^{-δ/2}) R/√sm`:
* off the axis `srcNorm (cartLift R c f) = gAx R c f` (`CartLiftNormOffAxis`), and the axis is
  Lebesgue-null (`AxisNull`), so the `z`-integrals agree almost everywhere;
* where the mask `e^δ x.1 < R²/|z'|²` holds, `FarSeparation` with `hRad (chartY R x) = R/√x.1`
  gives `|y - l z| ≥ (1 - e^{-δ/2}) R/√x.1 ≥ d`, so the kernel `|y - l z|^{-4}` is `farKern d`;
* where the mask fails the integrand is `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem farMajorantPointwise_of (hSep : FarSeparation) (hC : CartLiftNormOffAxis)
    (hN : AxisNull) : FarMajorantPointwise := by
  intro R c δ μ sm hR hδ hsm f x hx0 hxsm
  have hN' : volume {z : UnforcedLeray.Space | hRad z = 0} = 0 := hN
  have hae : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space), hRad z ≠ 0 := by
    rw [ae_iff]
    simpa using hN'
  have hyr : hRad (chartY R x) = R / Real.sqrt x.1 := by
    show Real.sqrt (((R / Real.sqrt x.1) ^ 2) + (0 : ℝ) ^ 2) = R / Real.sqrt x.1
    rw [zero_pow two_ne_zero, add_zero]
    exact Real.sqrt_sq (div_nonneg hR.le (Real.sqrt_nonneg _))
  have hd0 : 0 ≤ 1 - Real.exp (-δ / 2) := by
    have : Real.exp (-δ / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hdd : (1 - Real.exp (-δ / 2)) * R / Real.sqrt sm ≤
      (1 - Real.exp (-δ / 2)) * (R / Real.sqrt x.1) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hR.le (Real.sqrt_pos.2 hx0)
        (Real.sqrt_le_sqrt hxsm.le)) hd0
  unfold farMajE dilMaj
  refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with z hz
  by_cases hc : Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · have hsep := hSep R δ x.1 hR hδ hx0 (chartY R x) z l hl.1 hl.2 hyr hc
    have hdw : (1 - Real.exp (-δ / 2)) * R / Real.sqrt sm ≤ ‖chartY R x - l • z‖ :=
      le_trans hdd hsep
    have hG : farKern ((1 - Real.exp (-δ / 2)) * R / Real.sqrt sm) (chartY R x - l • z) =
        ENNReal.ofReal (‖chartY R x - l • z‖ ^ (-4 : ℝ)) := by
      unfold farKern
      rw [if_pos hdw]
    rw [if_pos hc, hC R c f _ z hz, hG]
  · rw [if_neg hc]
    exact zero_le

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
