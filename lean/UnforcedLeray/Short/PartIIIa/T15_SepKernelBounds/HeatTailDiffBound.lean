import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.T04_GaussInvIntegral
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.GaussSup
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailIterated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailStep

/-!
# Part III-a, task `PartIII-a:T15/6`: the difference `heatTail t - heatTail 0`

Proves `heatTailDiffBound : HeatTailDiffBound` (`Sub/T15.lean`; SP 3608, `K_t - K_0 =
-∫_0^t ΔK_a da`). For `m : ℕ` put `C = C0 * S`, where `C0` comes from `heatGBound m` (T14) and `S`
is the Gaussian supremum of `gaussSup` at `s = (3+m)/2`.

1. `heatTailIterated` (T15/4) at `t` and at `0` gives `D^m(heatTail t)(x) = ∫_{(t,∞)} D^m G_a(x) da`
   and `D^m(heatTail 0)(x) = ∫_{(0,∞)} D^m G_a(x) da` for `x ≠ 0`, and both functions are `C^∞` at `x`.
2. `iteratedFDeriv_sub_apply` gives `D^m(heatTail t - heatTail 0)(x)` as the difference of the two
   integrals. `integral_Ioi_sub_Ioi` and `integral_of_le` turn it into `∫_{(0,t]} D^m G_a(x) da`
   (sign by `norm_sub_rev`).
3. For `a ∈ (0,t]`, `‖D^m G_a(x)‖ ≤ C0 a^{-s} e^{-‖x‖²/(8a)} ≤ C0 S ‖x‖^{-3-m}` by `heatGBound`
   and `gaussSup`, since `-2s = -3-m`.
4. `norm_setIntegral_le_of_norm_le_const` on the set `(0,t]` of measure `t` gives the bound
   `C0 S t ‖x‖^{-3-m}`.

The integrability of `a ↦ D^m G_a(x)` on `(0,∞)` comes from `hts_integrable_gauss`
(`HeatTailStep.lean`), the Gaussian majorant `heatGBound`, and continuity in `a` from
`continuousOn_iteratedFDeriv_heatKernel` (`Lib/Kernels/GaussDeriv.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Difference of heat tails** (`PartIII-a:T15/6`; SP 3608). -/
theorem heatTailDiffBound : UnforcedLeray.Short.IIIa.HeatTailDiffBound := by
  unfold HeatTailDiffBound
  intro m
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound m
  obtain ⟨S, hS, hSb⟩ := gaussSup ((3 + (m : ℝ)) / 2) (by positivity)
  refine ⟨C0 * S, mul_nonneg hC0 hS, ?_⟩
  intro t ht x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hs0 : 1 < (3 + (m : ℝ)) / 2 := by linarith
  have e1 : (-(3 + (m : ℝ)) / 2) = -((3 + (m : ℝ)) / 2) := by ring
  have e2 : (-2 * ((3 + (m : ℝ)) / 2)) = -3 - (m : ℝ) := by ring
  -- the derivatives of the two heat tails at `x`
  have hTI : HeatTailIterated := heatTailIterated
  obtain ⟨hct, hdt⟩ := hTI t ht.le x hx
  obtain ⟨hc0, hd0⟩ := hTI 0 le_rfl x hx
  have hcm : ContDiffAt ℝ m (heatTail t) x := hct.of_le (by exact_mod_cast le_top)
  have hc0m : ContDiffAt ℝ m (heatTail 0) x := hc0.of_le (by exact_mod_cast le_top)
  -- the integrand `a ↦ D^m G_a(x)` is continuous on `(0, ∞)`
  have hcont : ContinuousOn (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) x) (Ioi 0) := by
    have e : (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) x) =
        fun a : ℝ => iteratedFDeriv ℝ m (UnforcedLeray.Heat.kernel a) x := by
      funext a
      rw [heatG_eq_heatKernel]
    rw [e]
    exact UnforcedLeray.Kernels.continuousOn_iteratedFDeriv_heatKernel m x
  -- integrability on `(0, ∞)` by the Gaussian majorant
  have hint0 : IntegrableOn (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) x) (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn (fun a : ℝ => C0 * (a ^ (-((3 + (m : ℝ)) / 2)) *
        Real.exp (-‖x‖ ^ 2 / (8 * a)))) (Ioi (0 : ℝ)) :=
      Integrable.const_mul (hts_integrable_gauss hs0 hr) C0
    refine Integrable.mono' hg (ContinuousOn.aestronglyMeasurable hcont measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    have ha0 : 0 < a := Set.mem_Ioi.1 ha
    have hb := hC0b a ha0 x
    rw [e1] at hb
    exact hb.trans_eq (mul_assoc _ _ _)
  -- the pointwise bound on `(0, t]`
  have hpt : ∀ a ∈ Ioc (0 : ℝ) t, ‖iteratedFDeriv ℝ m (heatG a) x‖ ≤
      C0 * S * ‖x‖ ^ (-3 - (m : ℝ)) := by
    intro a ha
    have ha0 : 0 < a := ha.1
    have hb := hC0b a ha0 x
    rw [e1] at hb
    have hS' := hSb a ‖x‖ ha0 hr
    rw [e2] at hS'
    calc ‖iteratedFDeriv ℝ m (heatG a) x‖
        ≤ C0 * a ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a)) := hb
      _ = C0 * (a ^ (-((3 + (m : ℝ)) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))) := mul_assoc _ _ _
      _ ≤ C0 * (S * ‖x‖ ^ (-3 - (m : ℝ))) := mul_le_mul_of_nonneg_left hS' hC0
      _ = C0 * S * ‖x‖ ^ (-3 - (m : ℝ)) := (mul_assoc _ _ _).symm
  -- the integral over `(0, ∞)` minus the integral over `(t, ∞)` is the integral over `(0, t]`
  have hsplit : (∫ a in Ioi (0 : ℝ), iteratedFDeriv ℝ m (heatG a) x) -
      (∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) x) =
      ∫ a in Ioc (0 : ℝ) t, iteratedFDeriv ℝ m (heatG a) x := by
    rw [intervalIntegral.integral_Ioi_sub_Ioi hint0 ht.le, intervalIntegral.integral_of_le ht.le]
  have hdiff : ‖iteratedFDeriv ℝ m (heatTail t) x - iteratedFDeriv ℝ m (heatTail 0) x‖ =
      ‖∫ a in Ioc (0 : ℝ) t, iteratedFDeriv ℝ m (heatG a) x‖ := by
    rw [hdt m, hd0 m, norm_sub_rev, hsplit]
  -- the `D^m` of the difference is the difference of the `D^m`
  have hsub : iteratedFDeriv ℝ m (fun y => heatTail t y - heatTail 0 y) x =
      iteratedFDeriv ℝ m (heatTail t) x - iteratedFDeriv ℝ m (heatTail 0) x := by
    show iteratedFDeriv ℝ m (heatTail t - heatTail 0) x = _
    exact iteratedFDeriv_sub_apply hcm hc0m
  rw [hsub, hdiff]
  calc ‖∫ a in Ioc (0 : ℝ) t, iteratedFDeriv ℝ m (heatG a) x‖
      ≤ (C0 * S * ‖x‖ ^ (-3 - (m : ℝ))) * volume.real (Ioc (0 : ℝ) t) :=
        norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hpt
    _ = C0 * S * t * ‖x‖ ^ (-3 - (m : ℝ)) := by
        rw [Real.volume_real_Ioc_of_le ht.le]
        ring

end UnforcedLeray.Short.IIIa
