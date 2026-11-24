import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Spine leaf 2: the Duhamel kernel is integrable (`LogKernelIntegral`)

Source of record: `the November 2 reference manuscript`, lines 1144-1145
("its integral kernel is integrable"). The Prop `UnforcedLeray.Short.Spine.LogKernelIntegral`
is defined in `Short/Spine/Sub/SP_CAN4_1.lean` and is proved here exactly as stated.

Proof. Fix `θ > 0`, write `e = exp 1` and `s = (eθ)^{1/2}`. For `v ∈ (θ, eθ]` put
`L = log v - log θ = log (v/θ)`. Then `L ≥ 1 - θ/v = (v-θ)/v ≥ (v-θ)/(eθ) > 0`, so
`L^{-1/2} ≤ ((v-θ)/(eθ))^{-1/2} = s (v-θ)^{-1/2}`. The majorant `s (v-θ)^{-1/2}` is interval
integrable with integral `2 s ((e-1)θ)^{1/2} ≤ 5θ`, because `s² + t² = (2e-1)θ < 5θ` for
`t = ((e-1)θ)^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

theorem logKernelIntegral_proof : UnforcedLeray.Short.Spine.LogKernelIntegral := by
  unfold UnforcedLeray.Short.Spine.LogKernelIntegral
  intro θ hθ
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp 1 := ⟨_, rfl⟩
  have he_gt : (2 : ℝ) < e := by
    rw [he]
    have h := Real.exp_one_gt_d9
    norm_num at h
    linarith
  have he_lt : e < 3 := by
    rw [he]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  rw [← he]
  have hpos : 0 < e * θ := mul_pos (by linarith) hθ
  have hθe : θ < e * θ := by nlinarith
  have hθe' : 0 ≤ e * θ - θ := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (e * θ) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = e * θ := by
    rw [hs, ← Real.sqrt_eq_rpow, Real.sq_sqrt hpos.le]
  have ht2 : ((e * θ - θ) ^ (1 / 2 : ℝ)) ^ 2 = e * θ - θ := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hθe']
  -- pointwise domination of the kernel on `(θ, eθ]`
  have hpt : ∀ v : ℝ, θ < v → v ≤ e * θ →
      (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ)) ≤ (v - θ) ^ (-(1 / 2 : ℝ)) * s := by
    intro v hθv hve
    have hv0 : 0 < v := lt_trans hθ hθv
    have hvθ : 0 < v - θ := by linarith
    have hL : 0 < Real.log v - Real.log θ := by
      have := Real.log_lt_log hθ hθv
      linarith
    have hlogdiv : Real.log (v / θ) = Real.log v - Real.log θ :=
      Real.log_div hv0.ne' hθ.ne'
    have h1 : 1 - (v / θ)⁻¹ ≤ Real.log (v / θ) :=
      Real.one_sub_inv_le_log_of_pos (div_pos hv0 hθ)
    have h2 : 1 - (v / θ)⁻¹ = (v - θ) / v := by
      rw [inv_div, sub_div, div_self hv0.ne']
    have h3 : (v - θ) / (e * θ) ≤ (v - θ) / v :=
      div_le_div_of_nonneg_left hvθ.le hv0 hve
    have hLb : (v - θ) / (e * θ) ≤ Real.log v - Real.log θ := by
      linarith
    have hLpow : (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ))
        ≤ ((v - θ) / (e * θ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hvθ hpos) hLb (by norm_num)
    have hid : ((v - θ) / (e * θ)) ^ (-(1 / 2 : ℝ)) = (v - θ) ^ (-(1 / 2 : ℝ)) * s := by
      rw [Real.div_rpow hvθ.le hpos.le, Real.rpow_neg hpos.le, div_inv_eq_mul, hs]
    rw [← hid]
    exact hLpow
  -- the majorant is interval integrable
  have hr : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
  have hM : IntervalIntegrable (fun v : ℝ => (v - θ) ^ (-(1 / 2 : ℝ)) * s) volume θ (e * θ) := by
    refine IntervalIntegrable.mul_const ?_ s
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume (0 : ℝ) (e * θ - θ) :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have h1 := h0.comp_sub_right θ
    rw [zero_add, sub_add_cancel] at h1
    exact h1
  -- the kernel is measurable and dominated a.e. by the majorant
  have hK_meas : Measurable (fun v : ℝ => (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ))) :=
    (Real.measurable_log.sub measurable_const).pow_const _
  have hint : IntervalIntegrable (fun v : ℝ => (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ)))
      volume θ (e * θ) := by
    refine IntervalIntegrable.mono_fun' hM hK_meas.aestronglyMeasurable ?_
    have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioc θ (e * θ))),
        ‖(Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ))‖ ≤ (v - θ) ^ (-(1 / 2 : ℝ)) * s := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro v hv
      have hθv : θ < v := hv.1
      have hve : v ≤ e * θ := hv.2
      have hL : 0 ≤ Real.log v - Real.log θ := by
        have := Real.log_lt_log hθ hθv
        linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _)]
      exact hpt v hθv hve
    rw [Set.uIoc_of_le hθe.le]
    exact hae
  refine ⟨hint, ?_⟩
  -- comparison of integrals
  have hmono : ∫ v in θ..(e * θ), (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ))
      ≤ ∫ v in θ..(e * θ), (v - θ) ^ (-(1 / 2 : ℝ)) * s := by
    apply intervalIntegral.integral_mono_on hθe.le hint hM
    intro v hv
    rcases eq_or_lt_of_le hv.1 with h | h
    · rw [← h]
      have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
      simp only [sub_self, h0, zero_mul, le_refl]
    · exact hpt v h hv.2
  -- the value of the majorant's integral
  have hJ : ∫ v in θ..(e * θ), (v - θ) ^ (-(1 / 2 : ℝ)) = 2 * (e * θ - θ) ^ (1 / 2 : ℝ) := by
    have hc : ∫ v in θ..(e * θ), (v - θ) ^ (-(1 / 2 : ℝ))
        = ∫ x in θ - θ..e * θ - θ, x ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_comp_sub_right (f := fun x : ℝ => x ^ (-(1 / 2 : ℝ))) θ
    rw [hc, sub_self, integral_rpow (Or.inl hr)]
    have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
    have h1 : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [h0, h1]
    ring
  have hIM : ∫ v in θ..(e * θ), (v - θ) ^ (-(1 / 2 : ℝ)) * s
      = 2 * (e * θ - θ) ^ (1 / 2 : ℝ) * s := by
    rw [intervalIntegral.integral_mul_const, hJ]
  -- the constant: `2 s t ≤ s² + t² = (2e - 1)θ < 5θ`
  have hbound : 2 * (e * θ - θ) ^ (1 / 2 : ℝ) * s ≤ 5 * θ := by
    nlinarith [sq_nonneg (s - (e * θ - θ) ^ (1 / 2 : ℝ)), hs2, ht2,
      mul_pos (sub_pos.mpr he_lt) hθ]
  rw [hIM] at hmono
  exact le_trans hmono hbound

end UnforcedLeray.Short.Spine
