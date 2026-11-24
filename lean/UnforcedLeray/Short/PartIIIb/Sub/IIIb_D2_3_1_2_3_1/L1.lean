import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailStep

/-!
# Part III-b, task `IIIb-D2/3/1/2/3/1/1`: differentiation under the heat-tail integral for `t > 0`

Source of record: `the November 2 reference manuscript`, lines 3598-3610
(`K_t = δ G_t + ∂∂ ∫_t^∞ G_a da`).

This is `heatTailStep` (`PartIII-a/T15_SepKernelBounds/HeatTailStep.lean`) restricted to `t > 0`
and extended to every `x`, including `x = 0`. The ball is `B(x, 1)` instead of `B(x, ‖x‖/2)`,
and the Gaussian majorant is replaced by a uniform one:

* `‖D(D^m G_a)(y)‖ = ‖D^{m+1} G_a(y)‖ ≤ C_1 a^{-(4+m)/2} e^{-‖y‖²/(8a)} ≤ C_1 a^{-(4+m)/2}`
  for all `y` and `a > 0`, and `a ↦ a^{-(4+m)/2}` is integrable on `(t,∞)` since
  `(4+m)/2 > 1` and `t > 0`.
* `‖D^m G_a(x)‖ ≤ C_0 a^{-(3+m)/2}`, integrable on `(t,∞)` for the same reason.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb

open UnforcedLeray.Short.IIIa

set_option synthInstance.maxHeartbeats 400000 in
/-- **Differentiation under the heat-tail integral for `t > 0`** (`IIIb-D2/3/1/2/3/1/1`;
SP 3598-3610). -/
theorem heatTailStepPos : ∀ t : ℝ, 0 < t → ∀ (m : ℕ) (x : Space), HasFDerivAt (fun y => ∫ a in Set.Ioi t, iteratedFDeriv ℝ m (UnforcedLeray.Short.IIIa.heatG a) y) (∫ a in Set.Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (UnforcedLeray.Short.IIIa.heatG a)) x) x := by
  intro t ht m x
  have hsub : Ioi t ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ht.le
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hs1 : 1 < (4 + (m : ℝ)) / 2 := by linarith
  have hs0 : 1 < (3 + (m : ℝ)) / 2 := by linarith
  -- each `G_a` is smooth
  have hsm : ∀ a : ℝ, ContDiff ℝ ∞ (heatG a) := fun a => by
    rw [heatG_eq_heatKernel]
    exact UnforcedLeray.Kernels.heatKernel_smooth a
  have hdiff : ∀ a : ℝ, Differentiable ℝ (fun y => iteratedFDeriv ℝ m (heatG a) y) :=
    fun a => (hsm a).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top m)
  -- continuity in the time variable on `(0,∞)`
  have hcont : ∀ (k : ℕ) (y : Space),
      ContinuousOn (fun a : ℝ => iteratedFDeriv ℝ k (heatG a) y) (Ioi 0) := by
    intro k y
    have e : (fun a : ℝ => iteratedFDeriv ℝ k (heatG a) y) =
        fun a : ℝ => iteratedFDeriv ℝ k (UnforcedLeray.Heat.kernel a) y := by
      funext a
      rw [heatG_eq_heatKernel]
    rw [e]
    exact UnforcedLeray.Kernels.continuousOn_iteratedFDeriv_heatKernel k y
  -- the derivative of `D^m G_a` is the curried `D^{m+1} G_a`
  have hF'eq : ∀ (a : ℝ) (y : Space),
      fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ)
          (iteratedFDeriv ℝ (m + 1) (heatG a) y) := by
    intro a y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  -- Gaussian majorants
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound m
  obtain ⟨C1, hC1, hC1b⟩ := heatGBound (m + 1)
  -- integrability of the value at `x`
  have hFint : Integrable (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) x)
      (volume.restrict (Ioi t)) := by
    have hg : IntegrableOn (fun a : ℝ => C0 * a ^ (-((3 + (m : ℝ)) / 2))) (Ioi t) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) ht) C0
    refine Integrable.mono' hg
      (ContinuousOn.aestronglyMeasurable ((hcont m x).mono hsub) measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    have ha0 : 0 < a := ht.trans (Set.mem_Ioi.1 ha)
    have e0 : -(3 + (m : ℝ)) / 2 = -((3 + (m : ℝ)) / 2) := neg_div _ _
    have hb := hC0b a ha0 x
    rw [e0] at hb
    have hexp : Real.exp (-‖x‖ ^ 2 / (8 * a)) ≤ 1 :=
      Real.exp_le_one_iff.2
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by linarith))
    exact hb.trans (mul_le_of_le_one_right (mul_nonneg hC0 (Real.rpow_nonneg ha0.le _)) hexp)
  -- the uniform dominating function on `(t,∞)`
  have hbound_int : IntegrableOn (fun a : ℝ => C1 * a ^ (-((4 + (m : ℝ)) / 2))) (Ioi t) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) ht) C1
  -- domination of the derivative on the ball `B(x, 1)`
  have hbd : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ y ∈ Metric.ball x 1,
      ‖fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y‖ ≤ C1 * a ^ (-((4 + (m : ℝ)) / 2)) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    intro y _
    have ha0 : 0 < a := ht.trans (Set.mem_Ioi.1 ha)
    have hb := hC1b a ha0 y
    have e1 : -(3 + ((m + 1 : ℕ) : ℝ)) / 2 = -((4 + (m : ℝ)) / 2) := by
      push_cast
      ring
    rw [e1] at hb
    have hexp : Real.exp (-‖y‖ ^ 2 / (8 * a)) ≤ 1 :=
      Real.exp_le_one_iff.2
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by linarith))
    rw [norm_fderiv_iteratedFDeriv]
    exact hb.trans (mul_le_of_le_one_right (mul_nonneg hC1 (Real.rpow_nonneg ha0.le _)) hexp)
  -- differentiability in `y` for almost every `a`
  have hdiffae : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ y ∈ Metric.ball x 1,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (heatG a) z)
        (fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y) y :=
    ae_of_all _ (fun a y _ => (hdiff a y).hasFDerivAt)
  -- measurability
  have hFmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) y)
        (volume.restrict (Ioi t)) :=
    Filter.Eventually.of_forall (fun y =>
      ContinuousOn.aestronglyMeasurable ((hcont m y).mono hsub) measurableSet_Ioi)
  have hF'meas : AEStronglyMeasurable (fun a : ℝ => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) x)
      (volume.restrict (Ioi t)) := by
    have h1 : AEStronglyMeasurable (fun a : ℝ => iteratedFDeriv ℝ (m + 1) (heatG a) x)
        (volume.restrict (Ioi t)) :=
      ContinuousOn.aestronglyMeasurable ((hcont (m + 1) x).mono hsub) measurableSet_Ioi
    have h2 := (LinearIsometryEquiv.continuous
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ)).comp_aestronglyMeasurable h1
    exact h2.congr (ae_of_all _ fun a => (hF'eq a x).symm)
  have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x one_pos
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs hFmeas hFint hF'meas hbd hbound_int
    hdiffae

end UnforcedLeray.Short.PartIIIb
