import UnforcedLeray.Short.PartI.Sub.PartI_C08_1_3

/-!
# `PartI:C08/1/3/2`: proof of `BwdGaugeConverse`

Converse of `BwdGauge` (source lines 1094-1125).  Write `c = canonicalGauge λ κ`,
`d = canonicalGauge (-λ) (-κ)` (so `d c = 1`), `V = c W`, `E(σ) = e^{(log σ - log θ)D}`, and
`f(τ) = d(τ) E(τ) V(τ)`.  By the Duhamel form of `V` (`bwdMild_pullback`), `τ ↦ E(τ)V(τ)` is
differentiable with derivative `-E(L₀V)`; the product rule with `d' = (λ + κ/τ) d` gives
`f' = -E((L₀ - λ - κ/σ) W) = -E(canonicalFullGen W)`.  The fundamental theorem of calculus on
`[θ,s₀]` with `f(θ) = W(θ)`, `f(s₀) = E(W(s₀))` yields the backward Duhamel identity for `W`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set Filter Topology

/-- `d(τ)c(τ) = 1` for the gauge pair `(λ,κ)` and `(-λ,-κ)`. -/
theorem canonicalGauge_mul_inv_neg (lam κ : ℂ) (τ : ℝ) :
    canonicalGauge (-lam) (-κ) τ * canonicalGauge lam κ τ = 1 := by
  unfold canonicalGauge
  rw [← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  ring

/-- The gauge is continuous on `[b,∞)`, `b > 0`. -/
theorem canonicalGauge_continuousOn_Ici {b : ℝ} (hb : 0 < b) (a k : ℂ) :
    ContinuousOn (canonicalGauge a k) (Ici b) := by
  unfold canonicalGauge
  refine Complex.continuous_exp.comp_continuousOn ?_
  have hlog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Ici b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.log continuousOn_id fun x hx => (lt_of_lt_of_le hb hx).ne')
  have hid : ContinuousOn (fun x : ℝ => (x : ℂ)) (Ici b) :=
    Complex.continuous_ofReal.continuousOn
  exact ((continuousOn_const.mul hid).add (continuousOn_const.mul hlog)).neg

/-- The integrand `σ ↦ canonicalFullGen σ (W σ)` is continuous on `[θ,s₀]`, `θ > 0`. -/
theorem canonicalFullGen_continuousOn_apply (lam κ : ℂ) {θ s₀ : ℝ} (hθ : 0 < θ)
    {W : ℝ → B0010.XG} (hW : ContinuousOn W (Icc θ s₀)) :
    ContinuousOn (fun σ => canonicalFullGen lam κ σ (W σ)) (Icc θ s₀) := by
  have hinv : ContinuousOn (fun σ : ℝ => (σ : ℂ)⁻¹) (Icc θ s₀) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun σ hσ =>
      Complex.ofReal_ne_zero.mpr (hθ.trans_le hσ.1).ne'
  have h1 : ContinuousOn (fun σ => Planar.L0 (W σ)) (Icc θ s₀) :=
    Planar.L0.continuous.comp_continuousOn hW
  have h2 : ContinuousOn (fun σ : ℝ => lam • W σ) (Icc θ s₀) :=
    (continuous_const_smul lam).comp_continuousOn hW
  have h3 : ContinuousOn (fun σ : ℝ => (κ * (σ : ℂ)⁻¹) • W σ) (Icc θ s₀) :=
    (continuousOn_const.mul hinv).smul hW
  have heq : (fun σ : ℝ => canonicalFullGen lam κ σ (W σ)) =
      fun σ : ℝ => (Planar.L0 (W σ) - lam • W σ) - (κ * (σ : ℂ)⁻¹) • W σ := by
    funext σ
    simp only [canonicalFullGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
  rw [heq]
  exact (h1.sub h2).sub h3

/-- The core: a backward Duhamel form of `V = c W` (with the coefficient `L₀`) gives the backward
Duhamel form of `W` with coefficient `canonicalFullGen`. -/
theorem bwdGaugeConverse_core {lam κ : ℂ} {b : ℝ} (hb : 0 < b) {W V : ℝ → B0010.XG}
    (hWc : ContinuousOn W (Ici b))
    (hVW : ∀ τ, b ≤ τ → V τ = canonicalGauge lam κ τ • W τ)
    (hV : BwdMild b (fun _ => Planar.L0) 0 V) :
    BwdMild b (canonicalFullGen lam κ) 0 W := by
  intro θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have hIcc : Icc θ s₀ ⊆ Ici b := fun x hx => le_trans hθ hx.1
  have hW : ContinuousOn W (Icc θ s₀) := hWc.mono hIcc
  have hVc : ContinuousOn V (Icc θ s₀) :=
    ((canonicalGauge_continuousOn_Ici hb lam κ).mono hIcc |>.smul hW).congr
      fun τ hτ => hVW τ (hθ.trans hτ.1)
  have hcg' : ContinuousOn (canonicalGauge (-lam) (-κ)) (Icc θ s₀) :=
    (canonicalGauge_continuousOn_Ici hb (-lam) (-κ)).mono hIcc
  have hKW := canonicalFullGen_continuousOn_apply lam κ hθ0 hW
  have hKint : IntervalIntegrable
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ)))
      volume θ s₀ :=
    (Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub (θ := θ) (s := Icc θ s₀) fun v hv => lt_of_lt_of_le hθ0 hv.1)
      hKW).intervalIntegrable_of_Icc hθs
  -- the Duhamel form of `V` at each point `τ ∈ [θ,s₀]`, based at `θ`
  have hPdef : ∀ τ ∈ Icc θ s₀,
      B0123.expD (Real.log τ - Real.log θ) (V τ) =
        B0123.expD (Real.log s₀ - Real.log θ) (V s₀) +
          ∫ σ in τ..s₀, B0123.expD (Real.log σ - Real.log θ) (Planar.L0 (V σ)) := by
    intro τ hτ
    have h := bwdMild_pullback hb hV hθ hτ.1 hτ.2
    simpa only [Pi.zero_apply, add_zero] using h
  have hgc : ContinuousOn (fun σ => B0123.expD (Real.log σ - Real.log θ) (Planar.L0 (V σ)))
      (Icc θ s₀) :=
    Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub (θ := θ) (s := Icc θ s₀) fun v hv => lt_of_lt_of_le hθ0 hv.1)
      (Planar.L0.continuous.comp_continuousOn hVc)
  have hPcont : ContinuousOn (fun τ => B0123.expD (Real.log τ - Real.log θ) (V τ)) (Icc θ s₀) :=
    Short.Spine.CanonicalMild.continuousOn_expD_pair
      (Short.Spine.CanonicalMild.continuousOn_log_sub (θ := θ) (s := Icc θ s₀) fun v hv => lt_of_lt_of_le hθ0 hv.1) hVc
  -- derivative of the Duhamel primitive of `V`
  have hPd : ∀ x ∈ Ioo θ s₀,
      HasDerivAt (fun τ => B0123.expD (Real.log τ - Real.log θ) (V τ))
        (-(B0123.expD (Real.log x - Real.log θ) (Planar.L0 (V x)))) x := by
    intro x hx
    have hi : IntervalIntegrable
        (fun σ => B0123.expD (Real.log σ - Real.log θ) (Planar.L0 (V σ))) volume x s₀ :=
      (hgc.mono (Icc_subset_Icc hx.1.le le_rfl)).intervalIntegrable_of_Icc hx.2.le
    have hm : StronglyMeasurableAtFilter
        (fun σ => B0123.expD (Real.log σ - Real.log θ) (Planar.L0 (V σ))) (𝓝 x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hgc.mono Ioo_subset_Icc_self) x hx
    have hc := hgc.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hd := (intervalIntegral.integral_hasDerivAt_left hi hm hc).const_add
      (B0123.expD (Real.log s₀ - Real.log θ) (V s₀))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with τ hτ
    exact hPdef τ ⟨hτ.1.le, hτ.2.le⟩
  -- the product `f(τ) = d(τ) E(τ) V(τ)` and its derivative
  have hfd : ∀ x ∈ Ioo θ s₀,
      HasDerivAt (fun τ => canonicalGauge (-lam) (-κ) τ •
          B0123.expD (Real.log τ - Real.log θ) (V τ))
        (-(B0123.expD (Real.log x - Real.log θ) (canonicalFullGen lam κ x (W x)))) x := by
    intro x hx
    have hxb : b ≤ x := le_trans hθ hx.1.le
    have hx0 : 0 < x := lt_of_lt_of_le hb hxb
    have hdd := hasDerivAt_canonicalGauge (-lam) (-κ) hx0
    have hdP : canonicalGauge (-lam) (-κ) x • B0123.expD (Real.log x - Real.log θ) (V x) =
        B0123.expD (Real.log x - Real.log θ) (W x) := by
      rw [hVW x hxb, map_smul, smul_smul, canonicalGauge_mul_inv_neg, one_smul]
    have hdL : canonicalGauge (-lam) (-κ) x •
        B0123.expD (Real.log x - Real.log θ) (Planar.L0 (V x)) =
        B0123.expD (Real.log x - Real.log θ) (Planar.L0 (W x)) := by
      rw [hVW x hxb, map_smul, map_smul, smul_smul, canonicalGauge_mul_inv_neg, one_smul]
    refine ((hdd.smul (hPd x hx)).congr_deriv ?_)
    rw [mul_smul, hdP, smul_neg, hdL]
    simp only [canonicalFullGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul]
    module
  have hfcont : ContinuousOn (fun τ => canonicalGauge (-lam) (-κ) τ •
      B0123.expD (Real.log τ - Real.log θ) (V τ)) (Icc θ s₀) :=
    hcg'.smul hPcont
  have hf'int : IntervalIntegrable
      (fun x => -(B0123.expD (Real.log x - Real.log θ) (canonicalFullGen lam κ x (W x))))
      volume θ s₀ := hKint.neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθs hfcont
    (f' := fun x => -(B0123.expD (Real.log x - Real.log θ) (canonicalFullGen lam κ x (W x))))
    (fun x hx => (hfd x hx).hasDerivWithinAt) hf'int
  have hfθ : canonicalGauge (-lam) (-κ) θ • B0123.expD (Real.log θ - Real.log θ) (V θ) = W θ := by
    rw [sub_self, B0123.expD_zero, ContinuousLinearMap.one_apply, hVW θ hθ, smul_smul,
      canonicalGauge_mul_inv_neg, one_smul]
  have hfs : canonicalGauge (-lam) (-κ) s₀ • B0123.expD (Real.log s₀ - Real.log θ) (V s₀) =
      B0123.expD (Real.log s₀ - Real.log θ) (W s₀) := by
    rw [hVW s₀ (le_trans hθ hθs), map_smul, smul_smul, canonicalGauge_mul_inv_neg, one_smul]
  rw [intervalIntegral.integral_neg] at hftc
  rw [hfs, hfθ] at hftc
  simp only [Pi.zero_apply, add_zero]
  refine ⟨hKint, ?_⟩
  linear_combination (norm := module) hftc

/-- **`BwdGaugeConverse`** (lines 1094-1125): the converse of `BwdGauge`. -/
theorem bwdGaugeConverse_proof : UnforcedLeray.Short.PartI.BwdGaugeConverse := by
  intro lam κ b hb W hWc hV
  exact bwdGaugeConverse_core hb hWc (fun τ _ => rfl) hV

end UnforcedLeray.Short.PartI
