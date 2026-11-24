import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1_2

/-!
# `PartI:C07/1/1/2/1`: proof of `AmplitudeFreeDuhamel`

Source `the November 2 reference manuscript`,
lines 1097-1101 (`-A' = θ⁻¹ℓ(Dr)`) and 1117-1119 (integrated form
`A(θ) = A(s₀) + ∫_θ^{s₀} ℓ(Dr(s))/s ds`).

Proof: for `b ≤ θ ≤ s₀`, put `k(τ) = A(τ) • e^{(log τ - log θ)D} q`.  On `(θ, s₀)` the
derivative of `k` is `-e^{(log τ - log θ)D}(f(τ) q - τ⁻¹ A(τ) D q)`, so the fundamental theorem
of calculus gives the Duhamel identity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

theorem amplitudeFreeDuhamel : UnforcedLeray.Short.PartI.AmplitudeFreeDuhamel := by
  unfold UnforcedLeray.Short.PartI.AmplitudeFreeDuhamel BwdMild
  intro q hq b hb A f hA hf hEq θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  simp only [zero_apply, zero_add]
  rcases hθs.eq_or_lt with h | h
  · subst h
    simp [B0123.expD_zero]
  have hIcc : ∀ v ∈ Icc θ s₀, 0 < v := fun v hv => hθ0.trans_le hv.1
  have hsub : Icc θ s₀ ⊆ Ici b := fun v hv => hθ.trans hv.1
  have hfq : ContinuousOn (fun σ : ℝ => f σ • q) (Icc θ s₀) :=
    (hf.mono hsub).smul continuousOn_const
  have hAd : ContinuousOn (fun σ : ℝ => (A σ / (σ : ℂ)) • B0094.D ⟨q, hq⟩) (Icc θ s₀) :=
    ((hA.mono hsub).div Complex.continuous_ofReal.continuousOn fun σ hσ =>
      Complex.ofReal_ne_zero.mpr (hIcc σ hσ).ne').smul continuousOn_const
  have hg : ContinuousOn (fun σ : ℝ => f σ • q - (A σ / (σ : ℂ)) • B0094.D ⟨q, hq⟩)
      (Icc θ s₀) :=
    hfq.sub hAd
  have hint : IntervalIntegrable (fun σ : ℝ => B0123.expD (Real.log σ - Real.log θ)
      (f σ • q - (A σ / (σ : ℂ)) • B0094.D ⟨q, hq⟩)) volume θ s₀ :=
    Short.Spine.CanonicalMild.intervalIntegrable_expD_log hθ0 hθs hg
  refine ⟨hint, ?_⟩
  -- derivative of `k(τ) = A(τ) • e^{(log τ - log θ)D} q` on `(θ, s₀)`
  have hk' : ∀ x ∈ Ioo θ s₀, HasDerivAt (fun τ => A τ • B0123.expD (Real.log τ - Real.log θ) q)
      (-(B0123.expD (Real.log x - Real.log θ) (f x • q - (A x / (x : ℂ)) • B0094.D ⟨q, hq⟩)))
      x := by
    intro x hx
    have hbx : b < x := lt_of_le_of_lt hθ hx.1
    have hfc : ContinuousAt f x := hf.continuousAt (Ici_mem_nhds hbx)
    have hfi : IntervalIntegrable f volume x s₀ :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (hf.mono fun v hv => hθ.trans (hx.1.le.trans hv.1))
    have hmeas : StronglyMeasurableAtFilter f (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hf.mono Ioi_subset_Ici_self) x hbx
    have hF : HasDerivAt (fun y => A s₀ + ∫ s in y..s₀, f s) (-f x) x :=
      (intervalIntegral.integral_hasDerivAt_left hfi hmeas hfc).const_add (A s₀)
    have hAx : HasDerivAt A (-f x) x := by
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hEq y s₀ (hθ.trans hy.1.le) hy.2.le
    have hE := hasDerivAt_expD_logSub_domain hθ0 hx.1 ⟨q, hq⟩
    have hk := hAx.smul hE
    refine hk.congr_deriv ?_
    rw [map_sub, map_smul, map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    module
  have hkc : ContinuousOn (fun τ => A τ • B0123.expD (Real.log τ - Real.log θ) q) (Icc θ s₀) :=
    (hA.mono hsub).smul (Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub (θ := θ) hIcc) continuousOn_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθs hkc
    (fun x hx => (hk' x hx).hasDerivWithinAt) hint.neg
  rw [intervalIntegral.integral_neg] at hFTC
  have key := (neg_eq_iff_eq_neg.mp hFTC).trans (neg_sub _ _)
  rw [key]
  simp only [sub_self, B0123.expD_zero, one_apply_eq_self, map_smul]
  abel

end UnforcedLeray.Short.PartI
