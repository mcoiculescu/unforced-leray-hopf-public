import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

/-!
# Leaf `PartII-b:T11/2/1/5` (`DualFABMeas`): measurability of `A` and `B`

* `A(σ) = ‖b(σ,·)‖_{L^r(avgμ)}`: `b` is replaced by a strongly measurable version `g`
  (`ae_eq_mk`); slice a.e. equality (`Measure.ae_ae_of_ae_prod`, `ae_withDensity_iff`) gives
  `A =ᵐ σ ↦ (∫⁻ ‖g(σ,·)‖ₑ^r dcell)^{1/r}`, measurable by Tonelli (`Measurable.lintegral_prod_right'`).
* `B(τ) = ‖∇^⊥H(τ,·)‖_{L^{r'}(avgμ)}`: for `τ > 0` the slice gradient is the
  full derivative `fderiv H (τ,p)` in the `(q,η)`-directions (chain rule, `H` smooth on
  `τ > 0`), and `fderiv ℝ H` is globally measurable (`measurable_fderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

instance abm_sfinite_avg (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-- Measurability of `σ ↦ dfA c r b σ` on `(0,∞)`, from `InHr`. -/
theorem abm_dfA (c r : ℝ) (hr : 1 < r) (b : CProf) (hb : InHr c r b) :
    AEMeasurable (dfA c r b) (volume.restrict (Ioi (0 : ℝ))) := by
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb' : AEStronglyMeasurable b (Axi.ageμ c (r / 2 - 5 / 2)) := hb.meas
  set g : Coord → CMerid := hb'.mk b with hgdef
  have hg : Measurable g := hb'.stronglyMeasurable_mk.measurable
  have hbg : b =ᵐ[Axi.ageμ c (r / 2 - 5 / 2)] g := hb'.ae_eq_mk
  -- a.e. slice equality on `(0,∞)`
  have hslice : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ p ∂(Cyl.avgμ c), b (σ, p) = g (σ, p) := by
    have h1 : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ (r / 2 - 5 / 2)))).prod (Cyl.avgμ c), b z = g z := hbg
    have h2 := Measure.ae_ae_of_ae_prod h1
    rw [ae_withDensity_iff (Axi.measurable_ofReal_rpow _)] at h2
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with σ h2σ hσ
    exact h2σ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hσ _)).ne'
  have hF : Measurable (fun z : Coord => ‖g z‖ₑ ^ r) := hg.enorm.pow_const r
  have hM : Measurable (fun σ : ℝ => ∫⁻ p, ‖g (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) :=
    hF.lintegral_prod_right'
  have hGform : ∀ σ : ℝ, eLpNorm (fun p : ℝ × ℝ => g (σ, p)) (ENNReal.ofReal r) (Cyl.avgμ c)
      = (∫⁻ p, ‖g (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) := by
    intro σ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le]
  have hGA : AEMeasurable (fun σ : ℝ => eLpNorm (fun p : ℝ × ℝ => g (σ, p))
      (ENNReal.ofReal r) (Cyl.avgμ c)) (volume.restrict (Ioi (0 : ℝ))) := by
    have hfun : (fun σ : ℝ => eLpNorm (fun p : ℝ × ℝ => g (σ, p)) (ENNReal.ofReal r)
        (Cyl.avgμ c)) = fun σ => (∫⁻ p, ‖g (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) :=
      funext hGform
    rw [hfun]
    exact (hM.pow_const _).aemeasurable
  have hAe : dfA c r b =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun σ : ℝ =>
      eLpNorm (fun p : ℝ × ℝ => g (σ, p)) (ENNReal.ofReal r) (Cyl.avgμ c) := by
    filter_upwards [hslice] with σ hσ
    exact eLpNorm_congr_ae hσ
  exact hGA.congr hAe.symm

/-- Measurability of `τ ↦ dfB c r' H τ` on `(0,∞)`, from the smoothness of `H` on `τ > 0`. -/
theorem abm_dfB (c r' : ℝ) (hr' : 0 < r') (H : Coord → ℝ)
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    AEMeasurable (dfB c r' H) (volume.restrict (Ioi (0 : ℝ))) := by
  have hD : Measurable (fderiv ℝ H) := measurable_fderiv (𝕜 := ℝ) (f := H)
  have hD1m : Measurable (fun x : Coord => fderiv ℝ H x (0, (0, 1))) :=
    hD.apply_continuousLinearMap _
  have hD2m : Measurable (fun x : Coord => fderiv ℝ H x (0, (1, 0))) :=
    hD.apply_continuousLinearMap _
  have hvec : Measurable (fun x : Coord =>
      (![fderiv ℝ H x (0, (0, 1)), -fderiv ℝ H x (0, (1, 0))] : Fin 2 → ℝ)) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    fin_cases i
    · simpa using hD1m
    · exact hD2m.neg
  have hΨ : Measurable (fun x : Coord =>
      ‖(![fderiv ℝ H x (0, (0, 1)), -fderiv ℝ H x (0, (1, 0))] : Fin 2 → ℝ)‖ₑ ^ r') :=
    hvec.enorm.pow_const r'
  have hMB : Measurable (fun τ : ℝ => ∫⁻ p, ‖(![fderiv ℝ H (τ, p) (0, (0, 1)),
      -fderiv ℝ H (τ, p) (0, (1, 0))] : Fin 2 → ℝ)‖ₑ ^ r' ∂(Cyl.avgμ c)) :=
    hΨ.lintegral_prod_right'
  -- slice derivative in terms of the full derivative, for `τ > 0`
  have hslice : ∀ τ : ℝ, 0 < τ → ∀ p v : ℝ × ℝ,
      fderiv ℝ (fun z : ℝ × ℝ => H (τ, z)) p v = fderiv ℝ H (τ, p) (0, v) := by
    intro τ hτ p v
    have hmem : (τ, p) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hτ, mem_univ _⟩
    have hdiff : DifferentiableAt ℝ H (τ, p) :=
      (hH.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
    have hin : HasFDerivAt (fun z : ℝ × ℝ => ((τ, z) : Coord))
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p :=
      (hasFDerivAt_const τ p).prodMk (hasFDerivAt_id p)
    have hcomp : HasFDerivAt (fun z : ℝ × ℝ => H (τ, z))
        ((fderiv ℝ H (τ, p)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) p :=
      hdiff.hasFDerivAt.comp p hin
    rw [hcomp.fderiv]
    simp
  have hperp : ∀ τ : ℝ, 0 < τ → ∀ p : ℝ × ℝ,
      perpGrad (fun z => H (τ, z)) p
        = ![fderiv ℝ H (τ, p) (0, (0, 1)), -fderiv ℝ H (τ, p) (0, (1, 0))] := by
    intro τ hτ p
    unfold perpGrad
    rw [hslice τ hτ p (0, 1), hslice τ hτ p (1, 0)]
  have hae : dfB c r' H =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun τ : ℝ =>
      (∫⁻ p, ‖(![fderiv ℝ H (τ, p) (0, (0, 1)), -fderiv ℝ H (τ, p) (0, (1, 0))] :
        Fin 2 → ℝ)‖ₑ ^ r' ∂(Cyl.avgμ c)) ^ (1 / r') := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    show eLpNorm (fun p => perpGrad (fun z => H (τ, z)) p) (ENNReal.ofReal r') (Cyl.avgμ c) = _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr').ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr'.le]
    simp only [hperp τ hτ]
  exact ((hMB.pow_const _).aemeasurable).congr hae.symm

/-- Leaf `T11/2/1/5`: `A` and `B` are a.e.-measurable on `(0,∞)`. -/
theorem DualFABMeas_proof : UnforcedLeray.Short.IIb.DualFABMeas := by
  intro c r ν b H hc hν hr hb hH
  exact ⟨abm_dfA c r hr b hb,
    abm_dfB c (r / (r - 1)) (div_pos (by linarith) (by linarith)) H hH.smooth⟩

end UnforcedLeray.Short.IIb
