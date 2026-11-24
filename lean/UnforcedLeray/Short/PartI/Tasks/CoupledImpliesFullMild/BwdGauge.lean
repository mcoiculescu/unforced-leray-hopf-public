import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1_2

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

/-- **Undoing the normalization (source line 1095, leaf `BwdGauge`).** Proof by the fundamental
theorem of calculus for `G(τ) = c(τ) • h(τ)`, where `c = canonicalGauge lam κ` and
`h(τ) = E(θ,s₀)W(s₀) + ∫_τ^{s₀} E(θ,σ)(canonicalFullGen σ (W σ)) dσ`, with `E(θ,σ) = e^{(log σ - log θ)D}`.
On `[θ,s₀]` one has `h(τ) = E(θ,τ)W(τ)` by the hypothesis, so `G = E(θ,·)(c • W)` there. -/
theorem bwdGauge : UnforcedLeray.Short.PartI.BwdGauge := by
  unfold UnforcedLeray.Short.PartI.BwdGauge
  intro lam κ b hb W hW hP
  unfold BwdMild
  intro θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have hcpos : ∀ σ ∈ Icc θ s₀, 0 < σ := fun σ hσ => lt_of_lt_of_le hθ0 hσ.1
  have hWθ : ContinuousOn W (Icc θ s₀) := hW.mono fun x hx => hθ.trans hx.1
  -- continuity of the gauge and of the integrands on `[θ,s₀]`
  have hc : ContinuousOn (canonicalGauge lam κ) (Icc θ s₀) := fun σ hσ =>
    ((hasDerivAt_canonicalGauge lam κ (hcpos σ hσ)).continuousAt).continuousWithinAt
  have hcW : ContinuousOn (fun σ => canonicalGauge lam κ σ • W σ) (Icc θ s₀) := hc.smul hWθ
  have hint1 : ContinuousOn (fun σ => Planar.L0 (canonicalGauge lam κ σ • W σ)) (Icc θ s₀) :=
    Planar.L0.continuous.comp_continuousOn hcW
  have hKc : ContinuousOn (fun σ : ℝ => canonicalFullGen lam κ σ) (Icc θ s₀) := by
    have hinv : ContinuousOn (fun σ : ℝ => κ * (σ : ℂ)⁻¹) (Icc θ s₀) :=
      continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.inv₀ fun σ hσ =>
        Complex.ofReal_ne_zero.mpr (hcpos σ hσ).ne')
    unfold canonicalFullGen
    exact (continuousOn_const.sub continuousOn_const).sub (hinv.smul continuousOn_const)
  have hKW : ContinuousOn (fun σ => canonicalFullGen lam κ σ (W σ)) (Icc θ s₀) :=
    hKc.clm_apply hWθ
  have hΦc : ContinuousOn
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ)))
      (Icc θ s₀) :=
    Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub fun v hv => hθ0.trans_le hv.1) hKW
  have hi1 : IntervalIntegrable
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (Planar.L0 (canonicalGauge lam κ σ • W σ)))
      volume θ s₀ :=
    Short.Spine.CanonicalMild.intervalIntegrable_expD_log hθ0 hθs hint1
  have hi2 : IntervalIntegrable
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ)))
      volume θ s₀ :=
    Short.Spine.CanonicalMild.intervalIntegrable_expD_log hθ0 hθs hKW
  -- derivative of the primitive `h` on `(θ,s₀)`
  have hh : ∀ τ ∈ Ioo θ s₀, HasDerivAt
      (fun u => B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
        ∫ σ in u..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ)))
      (-(B0123.expD (Real.log τ - Real.log θ) (canonicalFullGen lam κ τ (W τ)))) τ := by
    intro τ hτ
    have hsub : uIcc τ s₀ ⊆ uIcc θ s₀ := by
      rw [uIcc_of_le hτ.2.le, uIcc_of_le hθs]
      exact Icc_subset_Icc hτ.1.le le_rfl
    have hτI := hi2.mono_set hsub
    have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo (hΦc.mono Ioo_subset_Icc_self) τ hτ
    have hcont : ContinuousAt
        (fun σ => B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))) τ :=
      hΦc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
    exact (intervalIntegral.integral_hasDerivAt_left hτI hmeas hcont).const_add _
  -- derivative of `G = c • h` on `(θ,s₀)`
  have hG : ∀ τ ∈ Ioo θ s₀, HasDerivWithinAt
      (fun u => canonicalGauge lam κ u •
        (B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
          ∫ σ in u..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))))
      (-(B0123.expD (Real.log τ - Real.log θ) (Planar.L0 (canonicalGauge lam κ τ • W τ))))
      (Ioi τ) τ := by
    intro τ hτ
    have hc' := hasDerivAt_canonicalGauge lam κ (hcpos τ (Ioo_subset_Icc_self hτ))
    have hG' := hc'.smul (hh τ hτ)
    refine (hG'.hasDerivWithinAt).congr_deriv ?_
    rw [← hP θ τ s₀ hθ hτ.1.le hτ.2.le]
    simp only [canonicalFullGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul, map_neg]
    module
  -- continuity of `G` on `[θ,s₀]`
  have hEW : ContinuousOn
      (fun u => B0123.expD (Real.log u - Real.log θ) (canonicalGauge lam κ u • W u))
      (Icc θ s₀) :=
    Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub fun v hv => hθ0.trans_le hv.1) hcW
  have hGc : ContinuousOn
      (fun u => canonicalGauge lam κ u •
        (B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
          ∫ σ in u..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))))
      (Icc θ s₀) := by
    refine hEW.congr ?_
    intro u hu
    dsimp only
    rw [← hP θ u s₀ hθ hu.1 hu.2, map_smul]
  -- fundamental theorem of calculus
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθs hGc
    (fun τ hτ => hG τ hτ) hi1.neg
  -- boundary values
  have hGs0 : canonicalGauge lam κ s₀ •
      (B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
        ∫ σ in s₀..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))) =
      B0123.expD (Real.log s₀ - Real.log θ) (canonicalGauge lam κ s₀ • W s₀) := by
    rw [intervalIntegral.integral_same, add_zero, map_smul]
  have hGθ : canonicalGauge lam κ θ •
      (B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
        ∫ σ in θ..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))) =
      canonicalGauge lam κ θ • W θ := by
    have hθW := hP θ θ s₀ hθ le_rfl hθs
    rw [sub_self, B0123.expD_zero, ContinuousLinearMap.one_apply] at hθW
    rw [← hθW]
  -- assemble
  rw [hGs0, hGθ, intervalIntegral.integral_neg] at hftc
  have hfin := neg_eq_iff_eq_neg.mp hftc
  refine ⟨?_, ?_⟩
  · simp only [Pi.zero_apply, add_zero]
    exact hi1
  · simp only [Pi.zero_apply, add_zero]
    rw [hfin]
    abel

end UnforcedLeray.Short.PartI
