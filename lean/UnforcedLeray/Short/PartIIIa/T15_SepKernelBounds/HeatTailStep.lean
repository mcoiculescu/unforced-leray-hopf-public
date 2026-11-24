import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.T04_GaussInvIntegral

/-!
# Part III-a, task `PartIII-a:T15/3`: one step of differentiation under the heat-tail integral

Proves `heatTailStep : HeatTailStep` (`Sub/T15.lean`; SP 3604-3606). For `t ≥ 0`, `m : ℕ` and
`x ≠ 0`, the map `y ↦ ∫_{(t,∞)} D^m G_a(y) da` is Fréchet differentiable at `x` with derivative
`∫_{(t,∞)} D(D^m G_a)(x) da`.

The proof applies `hasFDerivAt_integral_of_dominated_of_fderiv_le` on the ball `B(x, ‖x‖/2)`:

1. Measurability in `a` on `(t,∞) ⊆ (0,∞)`: `continuousOn_iteratedFDeriv_heatKernel` via
   `heatG_eq_heatKernel`.
2. Domination: on `B(x, ‖x‖/2)` one has `‖y‖ ≥ ‖x‖/2`, so `‖D(D^m G_a)(y)‖ = ‖D^{m+1} G_a(y)‖`
   (`norm_fderiv_iteratedFDeriv`) is at most `C_{m+1} a^{-(4+m)/2} e^{-(‖x‖/2)²/(8a)}`
   (`heatGBound`), which is integrable on `(t,∞)` by `gaussInvIntegral`.
3. Integrability of the value at `x`: `‖D^m G_a(x)‖ ≤ C_m a^{-(3+m)/2} e^{-‖x‖²/(8a)}`.
4. `h_diff`: each `D^m G_a` is `C^∞`, hence differentiable with derivative `fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The Gaussian inverse-power integrand is integrable on `(0,∞)` for `s > 1`, `r > 0`. -/
lemma hts_integrable_gauss {s r : ℝ} (hs : 1 < s) (hr : 0 < r) :
    IntegrableOn (fun a : ℝ => a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) (Ioi (0 : ℝ)) := by
  have H : GaussInvIntegral := gaussInvIntegral
  obtain ⟨h1, h2⟩ := H s r hs hr
  have hmeas : Measurable (fun a : ℝ => a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) := by
    fun_prop
  have hnn : ∀ᵐ a ∂(volume.restrict (Ioi (0 : ℝ))),
      (0 : ℝ) ≤ a ^ (-s) * Real.exp (-r ^ 2 / (8 * a)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun a ha =>
      mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.1 ha).le _) (Real.exp_pos _).le)
  have hfin : ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) < ⊤ := by
    rw [h1]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  exact ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Differentiation under the heat-tail integral** (`PartIII-a:T15/3`; SP 3604-3606). -/
theorem heatTailStep : UnforcedLeray.Short.IIIa.HeatTailStep := by
  unfold HeatTailStep
  intro t ht m x hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hr : 0 < ‖x‖ / 2 := half_pos hxpos
  have hsub : Ioi t ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ht
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
  have hF'cont : ∀ y : Space,
      ContinuousOn (fun a : ℝ => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y) (Ioi 0) := by
    intro y
    have e : (fun a : ℝ => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y) =
        fun a : ℝ => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ)
          (iteratedFDeriv ℝ (m + 1) (heatG a) y) := by
      funext a
      exact hF'eq a y
    rw [e]
    exact (LinearIsometryEquiv.continuous _).comp_continuousOn (hcont (m + 1) y)
  -- Gaussian majorants
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound m
  obtain ⟨C1, hC1, hC1b⟩ := heatGBound (m + 1)
  -- integrability of the value at `x`
  have hFint : Integrable (fun a : ℝ => iteratedFDeriv ℝ m (heatG a) x)
      (volume.restrict (Ioi t)) := by
    have hg : IntegrableOn (fun a : ℝ => C0 * (a ^ (-((3 + (m : ℝ)) / 2)) *
        Real.exp (-‖x‖ ^ 2 / (8 * a)))) (Ioi (0 : ℝ)) :=
      Integrable.const_mul (hts_integrable_gauss hs0 hxpos) C0
    refine Integrable.mono' (IntegrableOn.mono_set hg hsub)
      (ContinuousOn.aestronglyMeasurable ((hcont m x).mono hsub) measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    have ha0 : 0 < a := Set.mem_Ioi.1 (hsub ha)
    have e0 : -(3 + (m : ℝ)) / 2 = -((3 + (m : ℝ)) / 2) := neg_div _ _
    have hb := hC0b a ha0 x
    rw [e0] at hb
    exact hb.trans_eq (mul_assoc _ _ _)
  -- the dominating function on `(t,∞)`
  have hbound_int : IntegrableOn (fun a : ℝ => C1 * (a ^ (-((4 + (m : ℝ)) / 2)) *
      Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a)))) (Ioi t) :=
    IntegrableOn.mono_set
      (Integrable.const_mul (hts_integrable_gauss hs1 hr) C1) hsub
  -- domination of the derivative on the ball `B(x, ‖x‖/2)`
  have hbd : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ y ∈ Metric.ball x (‖x‖ / 2),
      ‖fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y‖ ≤
        C1 * (a ^ (-((4 + (m : ℝ)) / 2)) * Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a))) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    intro y hy
    have ha0 : 0 < a := Set.mem_Ioi.1 (hsub ha)
    have hy' : ‖x‖ / 2 ≤ ‖y‖ := by
      have h1 : ‖y - x‖ < ‖x‖ / 2 := by
        have h := Metric.mem_ball.1 hy
        rwa [dist_eq_norm] at h
      have h2 := norm_sub_norm_le x y
      have h3 := norm_sub_rev y x
      linarith
    have hsq : (‖x‖ / 2) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hr.le hy' 2
    have hexp : -‖y‖ ^ 2 / (8 * a) ≤ -(‖x‖ / 2) ^ 2 / (8 * a) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hb := hC1b a ha0 y
    have e1 : -(3 + ((m + 1 : ℕ) : ℝ)) / 2 = -((4 + (m : ℝ)) / 2) := by
      push_cast
      ring
    rw [e1] at hb
    rw [norm_fderiv_iteratedFDeriv]
    calc ‖iteratedFDeriv ℝ (m + 1) (heatG a) y‖
        ≤ C1 * a ^ (-((4 + (m : ℝ)) / 2)) * Real.exp (-‖y‖ ^ 2 / (8 * a)) := hb
      _ ≤ C1 * a ^ (-((4 + (m : ℝ)) / 2)) * Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by positivity)
      _ = C1 * (a ^ (-((4 + (m : ℝ)) / 2)) * Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a))) :=
          mul_assoc _ _ _
  -- differentiability in `y` for almost every `a`
  have hdiffae : ∀ᵐ a ∂(volume.restrict (Ioi t)), ∀ y ∈ Metric.ball x (‖x‖ / 2),
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
  have hs : Metric.ball x (‖x‖ / 2) ∈ 𝓝 x := Metric.ball_mem_nhds x hr
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs hFmeas hFint hF'meas hbd hbound_int
    hdiffae

end UnforcedLeray.Short.IIIa
