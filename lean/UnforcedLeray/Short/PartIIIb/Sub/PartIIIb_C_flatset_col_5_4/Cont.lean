import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.KcSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Fixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Unif

/-!
# `FcvEllCont`: continuity of `r ↦ ℓ_r(ω(r))` (source 2819-2836, 4610-4615)

`ℓ_r` is real-linear in `ω` (`FcvKcSub` and `xFn_sub` a.e.) and integrable on the cell for `r > 0`
(the bound of `fcvEllCoef`, as in `fcvEllFixed`).  Splitting
`ℓ_r(ω r) = ℓ_r(ω r - ω r₀) + ℓ_r(ω r₀)`, the second term is continuous at `r₀` (`fcvEllFixed`) and
the first is squeezed by `C_T ‖ω r - ω r₀‖` (`fcvEllUnif` with `T = 2 r₀`), which tends to `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The tested integrand is integrable on the cell for `r > 0`. -/
theorem fcvc_integrable {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest c φ)
    (ω : Xmc c m) (r : ℝ) (hr : 0 < r) :
    Integrable (fun y => IIIa.flowIntegrand tr (xFn ω) (kcC ω) r φ y)
      (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.band
  obtain ⟨A, B, hAB⟩ := (fcvEllCoef : FcvEllCoef) ν c tr φ hφ r
  have hband : MeasurableSet {z : ℝ × ℝ | |z.2| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  have hind : Integrable
      ({z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖))
      (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hband]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hband]
    have hS : {z : ℝ × ℝ | |z.2| ≤ R} ∩ B0579.cell c ⊆ B0579.cell c := inter_subset_right
    have hfin' : volume ({z : ℝ × ℝ | |z.2| ≤ R} ∩ B0579.cell c) ≠ ⊤ := by
      rw [inter_comm]
      exact fxF_band_fin c R
    exact (fxF_kcC_norm_integrable ω 0 hS hfin').add (fxF_kcC_norm_integrable ω 1 hS hfin')
  have hbnd : Integrable (fun y => A * ‖xFn ω y‖ +
      B * {z : ℝ × ℝ | |z.2| ≤ R}.indicator (fun z => ‖kcC ω z 0‖ + ‖kcC ω z 1‖) y)
      (volume.restrict (B0579.cell c)) :=
    ((xFn_integrableOn ω).norm.const_mul A).add (hind.const_mul B)
  refine Integrable.mono' hbnd (fxF_aesm tr φ hφ ω r hr) ?_
  refine cell_ae_of_mem fun y hy => ?_
  obtain ⟨hA, hB⟩ := hAB r ⟨hr.le, le_rfl⟩ y hy
  exact fxF_point_bound tr φ R hR ω A B r y hA hB

/-- `ℓ_r` is additive on `X_{m,c}` for `r > 0`. -/
theorem fcvc_sub {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest c φ)
    (r : ℝ) (hr : 0 < r) (a b : Xmc c m) :
    ellFn tr φ r (a - b) = ellFn tr φ r a - ellFn tr φ r b := by
  unfold ellFn
  rw [← integral_sub (fcvc_integrable tr φ hφ a r hr) (fcvc_integrable tr φ hφ b r hr)]
  refine integral_congr_ae ?_
  have hk0 := (fcvKcSub : FcvKcSub) c m a b 0
  have hk1 := (fcvKcSub : FcvKcSub) c m a b 1
  have hx := xFn_sub a b
  filter_upwards [hk0, hk1, hx] with y e0 e1 e2
  unfold IIIa.flowIntegrand
  rw [e0, e1, e2]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst in
/-- **`FcvEllCont`**: `r ↦ ℓ_r(ω(r))` is continuous on `(0,∞)` (source 2819-2836, 4610-4615). -/
theorem fcvEllCont : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FcvEllCont := by
  unfold FcvEllCont
  intro ν c m _ _ tr φ hφ ω hω r0 hr0
  have hr0' : (0 : ℝ) < r0 := hr0
  obtain ⟨C, hC⟩ := (fcvEllUnif : FcvEllUnif) ν c m tr φ hφ (2 * r0)
  have hFix : Tendsto (fun r => ellFn tr φ r (ω r0)) (𝓝[Ioi 0] r0)
      (𝓝 (ellFn tr φ r0 (ω r0))) :=
    (fcvEllFixed : FcvEllFixed) ν c m tr φ hφ (ω r0) r0 hr0
  have hωc : Tendsto ω (𝓝[Ioi 0] r0) (𝓝 (ω r0)) := hω r0 hr0
  -- the increment `ω r - ω r₀` tends to zero
  have hωt : Tendsto (fun r => ‖ω r - ω r0‖) (𝓝[Ioi 0] r0) (𝓝 0) := by
    have h1 : Tendsto (fun r => ω r - ω r0) (𝓝[Ioi 0] r0) (𝓝 (ω r0 - ω r0)) :=
      hωc.sub tendsto_const_nhds
    rw [sub_self] at h1
    have h2 := h1.norm
    rwa [norm_zero] at h2
  have hbd : Tendsto (fun r => C * ‖ω r - ω r0‖) (𝓝[Ioi 0] r0) (𝓝 0) := by
    have h3 : Tendsto (fun _ : ℝ => C) (𝓝[Ioi 0] r0) (𝓝 C) := tendsto_const_nhds
    have h4 := h3.mul hωt
    rwa [mul_zero] at h4
  -- the first term tends to zero, by `fcvEllUnif` with `T = 2 r₀`
  have hdiff : Tendsto (fun r => ellFn tr φ r (ω r - ω r0)) (𝓝[Ioi 0] r0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (show r0 < 2 * r0 by linarith))]
      with r hr1 hr2
    have hr1' : (0 : ℝ) < r := hr1
    have hr2' : r < 2 * r0 := hr2
    exact hC r hr1' hr2'.le (ω r - ω r0)
  -- splitting `ℓ_r(ω r) = ℓ_r(ω r - ω r₀) + ℓ_r(ω r₀)`
  have hsplit : ∀ r : ℝ, 0 < r →
      ellFn tr φ r (ω r) = ellFn tr φ r (ω r - ω r0) + ellFn tr φ r (ω r0) := by
    intro r hr
    rw [fcvc_sub tr φ hφ r hr]
    ring
  have hlim : Tendsto (fun r => ellFn tr φ r (ω r - ω r0) + ellFn tr φ r (ω r0))
      (𝓝[Ioi 0] r0) (𝓝 (0 + ellFn tr φ r0 (ω r0))) :=
    hdiff.add hFix
  rw [zero_add] at hlim
  have hlim' : Tendsto (fun r => ellFn tr φ r (ω r)) (𝓝[Ioi 0] r0)
      (𝓝 (ellFn tr φ r0 (ω r0))) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hsplit r hr).symm
  exact hlim'
