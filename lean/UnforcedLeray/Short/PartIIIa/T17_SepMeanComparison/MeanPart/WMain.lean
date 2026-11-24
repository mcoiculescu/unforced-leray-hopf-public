import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.WEval
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split

/-!
# Mean part helper: evaluation of `fderiv sepW` for a `q`-independent source (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_src_lintegral (ε : ℝ) (hε : 0 < ε) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) (σ : ℝ) :
    ∫⁻ z : Space, srcNorm (thinSource ε (meanLift G)) σ z =
      ENNReal.ofReal (ε⁻¹) ^ 2 * ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (tensorNorm (G w.1 w.2)) := by
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (tensorNorm (G w.1 w.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have e1 : (fun z : Space => srcNorm (thinSource ε (meanLift G)) σ z) =
      fun z : Space => (fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (tensorNorm (G ((ε * w.1.1, ε * w.1.2)) w.2)))
        ((z 0, z 1), z 2) := by
    funext z; rfl
  rw [e1]
  have hK : Measurable fun w : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (tensorNorm (G ((ε * w.1.1, ε * w.1.2)) w.2)) :=
    hmeas.comp (f := fun w : (ℝ × ℝ) × ℝ => ((ε * w.1.1, ε * w.1.2), w.2)) (by fun_prop)
  rw [t17s_spaceProd.lintegral_comp hK]
  exact t17s_scale ε hε (fun w => ENNReal.ofReal (tensorNorm (G w.1 w.2))) hmeas

theorem mp_W_eval (hK : SepKernelBounds) (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hc : 0 < c)
    (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    DifferentiableAt ℝ (fun y => sepW ν μ (thinSource ε (meanLift G)) y τ) (ε⁻¹ • xo) ∧
      ∀ (v : Space) (i : Fin 3),
        (fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift G)) y τ) (ε⁻¹ • xo) v) i =
          (ε : ℂ) ^ 3 * ∫ p, mpHW ν ε μ G xo v i p ∂mpRho2 ∧
        Integrable (mpHW ν ε μ G xo v i) mpRho2 := by
  have hsrc : IsSepSource (2 * ε * c) (ρo / ε) (thinSource ε (meanLift G)) :=
    t17s_isSepSource ε c ρo hε hc _ (fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1))
      (by fun_prop)) (fun _ _ _ => rfl) (fun x' Y q h => hGs x' Y h)
  have hD : 0 < ρi / ε - ρo / ε := by
    have : 0 < ρi - ρo := by linarith
    rw [← sub_div]; positivity
  have hy : ρi / ε ≤ Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) := by
    have h2 : Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) =
        ε⁻¹ * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
      have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hε.le)]
    rw [h2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hfinN : ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (tensorNorm (G w.1 w.2)) < ⊤ :=
    hint.lintegral_lt_top
  have hfin : sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε (meanLift G))) τ
      (ε⁻¹ • xo) < ⊤ := by
    refine t17s_sepDom_lt_top (2 * μ.re + 2) (by linarith) _ hD _ τ _ ?_
    simp_rw [mp_src_lintegral ε hε G hGm]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      mul_one]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfinN
  obtain ⟨hdf, hI⟩ := mp_local hK ν hν μ (ρo / ε) (ρi / ε) (2 * ε * c) (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) _ hsrc τ (ε⁻¹ • xo) hy hfin
  refine ⟨hdf.differentiableAt, fun v i => ?_⟩
  set T := thinSource ε (meanLift G) with hT
  set Λ : (Space →L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) v) with hΛ
  have h1 : (fderiv ℝ (fun y => sepW ν μ T y τ) (ε⁻¹ • xo) v) i =
      ∫ p, Λ (fderiv ℝ (sepDiffF ν μ T τ p) (ε⁻¹ • xo)) ∂sepDiffRho := by
    rw [hdf.fderiv, Λ.integral_comp_comm hI]
    rfl
  have h2 : ∀ᵐ p ∂sepDiffRho, Λ (fderiv ℝ (sepDiffF ν μ T τ p) (ε⁻¹ • xo)) =
      (ε : ℂ) ^ 5 * mpHW ν ε μ G xo v i (Prod.map (id : ℝ → ℝ) (mpPsi ε hε) p) := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    obtain ⟨l, z⟩ := p
    have := mp_fderiv_F ν hν μ T τ l hp z (ε⁻¹ • xo) v i
    simp only [hΛ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.apply_apply]
    rw [this]
    exact mpHW_scale ν ε hν hε μ G xo v i l hp z
  have hΛint : Integrable (fun p => Λ (fderiv ℝ (sepDiffF ν μ T τ p) (ε⁻¹ • xo))) sepDiffRho :=
    Λ.integrable_comp hI
  have hc2 : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ 0 := by
    have : ENNReal.ofReal ε⁻¹ ≠ 0 := by simpa using inv_pos.2 hε
    exact pow_ne_zero _ this
  have hc2' : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hε5 : (ε : ℂ) ^ 5 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hε.ne')
  have hmapint : Integrable (mpHW ν ε μ G xo v i) mpRho2 := by
    have h3 : Integrable (fun p => mpHW ν ε μ G xo v i (Prod.map (id : ℝ → ℝ) (mpPsi ε hε) p))
        sepDiffRho := by
      have := hΛint.const_mul ((ε : ℂ) ^ 5)⁻¹
      refine this.congr ?_
      filter_upwards [h2] with p hp
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hε5, one_mul]
    have h4 := (mp_Psi_embedding ε hε).integrable_map_iff (g := mpHW ν ε μ G xo v i) (μ := sepDiffRho) |>.2 h3
    rw [mp_Psi_map ε hε, integrable_smul_measure hc2 hc2'] at h4
    exact h4
  refine ⟨?_, hmapint⟩
  rw [h1, integral_congr_ae h2, integral_const_mul]
  have h5 := (mp_Psi_embedding ε hε).integral_map (μ := sepDiffRho) (mpHW ν ε μ G xo v i)
  rw [mp_Psi_map ε hε, integral_smul_measure] at h5
  have h6 : (ENNReal.ofReal (ε⁻¹) ^ 2).toReal = (ε⁻¹) ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.2 hε.le)]
  rw [h6] at h5
  have h7 : ∫ p, mpHW ν ε μ G xo v i (Prod.map (id : ℝ → ℝ) (mpPsi ε hε) p) ∂sepDiffRho =
      ((ε⁻¹ : ℝ) : ℂ) ^ 2 * ∫ p, mpHW ν ε μ G xo v i p ∂mpRho2 := by
    rw [← h5, Complex.real_smul]
    push_cast
    ring
  rw [h7]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

end UnforcedLeray.Short.IIIa

end
