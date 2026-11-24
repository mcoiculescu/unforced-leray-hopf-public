import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Defs

/-!
# `PartIII-b:C/rep/8/1/1/1/asm`: the ray fundamental theorem of calculus (`RayFTCStmt`)

Source `shorter-proof-2026-11-02.tex` lines 4178-4184: `Psi_Z(r,z) = -int_r^inf rho Z_z d rho`, the
fields decay along the ray, so the value at `(r,0,z)` is minus the integral of the outward
derivative, and the primitive is a Tonelli integral of the derivative difference.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GeomXAsm

namespace RayFTCAux

theorem hpt_eq_lin (ρ z : ℝ) : hpt ρ z = ρ • coordinateVector 0 + z • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [hpt, coordinateVector]

theorem hasDerivAt_hpt (z t : ℝ) : HasDerivAt (fun s => hpt s z) (coordinateVector 0) t := by
  have h' : (fun s => hpt s z) = fun s : ℝ => s • (coordinateVector 0 : Space) + z • (coordinateVector 2 : Space) :=
    funext fun s => hpt_eq_lin s z
  rw [h']
  have h : HasDerivAt (fun s : ℝ => s • (coordinateVector 0 : Space) + z • (coordinateVector 2 : Space))
      ((1 : ℝ) • (coordinateVector 0 : Space)) t :=
    ((hasDerivAt_id t).smul_const (coordinateVector 0 : Space)).add_const _
  simpa using h

theorem continuous_hpt' (z : ℝ) : Continuous fun ρ : ℝ => hpt ρ z := by
  have h' : (fun ρ : ℝ => hpt ρ z) = fun ρ : ℝ => ρ • (coordinateVector 0 : Space) + z • (coordinateVector 2 : Space) :=
    funext fun ρ => hpt_eq_lin ρ z
  rw [h']
  fun_prop

theorem measurable_hpt' (z : ℝ) : Measurable fun ρ : ℝ => hpt ρ z :=
  (continuous_hpt' z).measurable

theorem norm_e (i : Fin 3) : ‖(coordinateVector i : Space)‖ = 1 := by
  rw [coordinateVector, PiLp.norm_single, norm_one]

theorem ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) :
    ENNReal.ofReal |∫ x, f x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
  have h1 : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) f
    simpa [Real.norm_eq_abs] using this
  calc ENNReal.ofReal |∫ x, f x ∂μ| ≤ ENNReal.ofReal (∫ x, |f x| ∂μ) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ x, ENNReal.ofReal |f x| ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun x => abs_nonneg _)

/-- The measurability of `ρ ↦ ‖∂Z₁ - ∂Z₂‖` along the ray. -/
theorem measurable_dDiff_ray (Z₁ Z₂ : ℝ → Space → Space) (τ z : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt t z)) := by
  have hA : Measurable fun t : ℝ => fderiv ℝ (Z₁ τ) (hpt t z) :=
    (measurable_fderiv (𝕜 := ℝ) (f := Z₁ τ)).comp (measurable_hpt' z)
  have hB : Measurable fun t : ℝ => fderiv ℝ (Z₂ τ) (hpt t z) :=
    (measurable_fderiv (𝕜 := ℝ) (f := Z₂ τ)).comp (measurable_hpt' z)
  have hG : Measurable fun t : ℝ => dDiff Z₁ Z₂ τ (hpt t z) :=
    measurable_norm.comp (hA.sub hB)
  exact ENNReal.measurable_ofReal.comp hG

/-- **Pointwise FTC bound.** For `ρ ≥ r`, `|Z₁ - Z₂|(ρ,0,z) ≤ ∫_{σ>ρ} ∂Z-difference`. -/
theorem ray_ofReal_le (Z₁ Z₂ : ℝ → Space → Space) (τ z r : ℝ)
    (hdiff : ∀ ρ : ℝ, r ≤ ρ → DifferentiableAt ℝ (Z₁ τ) (hpt ρ z) ∧ DifferentiableAt ℝ (Z₂ τ) (hpt ρ z))
    (hT : Tendsto (fun t : ℝ => Z₁ τ (hpt t z) - Z₂ τ (hpt t z)) atTop (𝓝 0)) (ρ : ℝ) (hρ : r ≤ ρ) :
    ENNReal.ofReal ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖ ≤
      ∫⁻ σ in Ioi ρ, ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) := by
  have hderiv : ∀ t : ℝ, r ≤ t → HasDerivAt (fun s => Z₁ τ (hpt s z) - Z₂ τ (hpt s z))
      ((fderiv ℝ (Z₁ τ) (hpt t z) - fderiv ℝ (Z₂ τ) (hpt t z)) (coordinateVector 0)) t := by
    intro t ht
    have h1 := ((hdiff t ht).1.hasFDerivAt).comp_hasDerivAt t (hasDerivAt_hpt z t)
    have h2 := ((hdiff t ht).2.hasFDerivAt).comp_hasDerivAt t (hasDerivAt_hpt z t)
    exact h1.sub h2
  have hA : Measurable fun t : ℝ => fderiv ℝ (Z₁ τ) (hpt t z) :=
    (measurable_fderiv (𝕜 := ℝ) (f := Z₁ τ)).comp (measurable_hpt' z)
  have hB : Measurable fun t : ℝ => fderiv ℝ (Z₂ τ) (hpt t z) :=
    (measurable_fderiv (𝕜 := ℝ) (f := Z₂ τ)).comp (measurable_hpt' z)
  have hmeasD : Measurable fun t : ℝ =>
      (fderiv ℝ (Z₁ τ) (hpt t z) - fderiv ℝ (Z₂ τ) (hpt t z)) (coordinateVector 0) :=
    (ContinuousLinearMap.apply ℝ Space (coordinateVector 0)).continuous.measurable.comp (hA.sub hB)
  have hmeasG : Measurable fun t : ℝ => dDiff Z₁ Z₂ τ (hpt t z) :=
    measurable_norm.comp (hA.sub hB)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi ρ)] fun σ => dDiff Z₁ Z₂ τ (hpt σ z) :=
    ae_of_all _ fun σ => norm_nonneg _
  by_cases hfin : ∫⁻ σ in Ioi ρ, ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) = ⊤
  · rw [hfin]; exact le_top
  have hgI : Integrable (fun σ => dDiff Z₁ Z₂ τ (hpt σ z)) (volume.restrict (Ioi ρ)) :=
    ⟨hmeasG.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hfin)⟩
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi ρ)),
      ‖(fderiv ℝ (Z₁ τ) (hpt t z) - fderiv ℝ (Z₂ τ) (hpt t z)) (coordinateVector 0)‖ ≤
        dDiff Z₁ Z₂ τ (hpt t z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := (fderiv ℝ (Z₁ τ) (hpt t z) - fderiv ℝ (Z₂ τ) (hpt t z)).le_opNorm (coordinateVector 0)
    rw [norm_e 0, mul_one] at h
    exact h
  have hDI : IntegrableOn (fun t => (fderiv ℝ (Z₁ τ) (hpt t z) - fderiv ℝ (Z₂ τ) (hpt t z))
      (coordinateVector 0)) (Ioi ρ) :=
    hgI.mono' hmeasD.aestronglyMeasurable hbound
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (a := ρ) (m := 0)
    ((hderiv ρ hρ).continuousAt.continuousWithinAt)
    (fun x hx => hderiv x (le_trans hρ (Set.mem_Ioi.1 hx).le)) hDI hT
  have hFTC' : ∫ x in Ioi ρ, (fderiv ℝ (Z₁ τ) (hpt x z) - fderiv ℝ (Z₂ τ) (hpt x z))
      (coordinateVector 0) = -(Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) := by
    have := hFTC
    simp only [zero_sub] at this
    exact this
  have key : ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖ ≤ ∫ σ in Ioi ρ, dDiff Z₁ Z₂ τ (hpt σ z) := by
    have h1 := norm_integral_le_of_norm_le hgI hbound
    rwa [hFTC', norm_neg] at h1
  calc ENNReal.ofReal ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖
      ≤ ENNReal.ofReal (∫ σ in Ioi ρ, dDiff Z₁ Z₂ τ (hpt σ z)) := ENNReal.ofReal_le_ofReal key
    _ = ∫⁻ σ in Ioi ρ, ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) :=
        ofReal_integral_eq_lintegral_ofReal hgI hnn

/-- The outward primitive is a difference of integrals: `Ψ₁ - Ψ₂ = -∫ ρ (Z₁-Z₂)_2`. -/
theorem outPrim_diff_eq (Z₁ Z₂ : ℝ → Space → Space) (τ r z : ℝ)
    (h₁ : IntegrableOn (fun ρ => ρ * Z₁ τ (hpt ρ z) 2) (Ioi r))
    (h₂ : IntegrableOn (fun ρ => ρ * Z₂ τ (hpt ρ z) 2) (Ioi r)) :
    outPrim Z₁ τ r z - outPrim Z₂ τ r z =
      -∫ ρ in Ioi r, ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2) := by
  have hO : ∀ W : ℝ → Space → Space, outPrim W τ r z = -∫ ρ in Ioi r, ρ * W τ (hpt ρ z) 2 :=
    fun W => rfl
  have hs : ∫ ρ in Ioi r, ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2) =
      (∫ ρ in Ioi r, ρ * Z₁ τ (hpt ρ z) 2) - ∫ ρ in Ioi r, ρ * Z₂ τ (hpt ρ z) 2 := by
    rw [← integral_sub h₁ h₂]
    refine integral_congr_ae (ae_of_all _ fun ρ => ?_)
    simp [PiLp.sub_apply, mul_sub]
  rw [hO Z₁, hO Z₂, hs]
  ring

end RayFTCAux

end GeomXAsm

open GeomXAsm GeomXAsm.RayFTCAux

/-- **(a2) The ray bounds** (source 4178-4184), proved from `ray_ofReal_le` and Tonelli. -/
theorem rayFTC : RayFTCStmt := by
  intro r z τ Z₁ Z₂ hr hdiff hT hP₁ hP₂
  -- (i) the value
  have hi : ENNReal.ofReal ‖Z₁ τ (hpt r z) - Z₂ τ (hpt r z)‖ ≤ rayW 0 (dDiff Z₁ Z₂ τ) r z := by
    have h := ray_ofReal_le Z₁ Z₂ τ z r hdiff hT r le_rfl
    unfold rayW
    simpa only [pow_zero, one_mul] using h
  have hGm := measurable_dDiff_ray Z₁ Z₂ τ z
  have hQ : IntegrableOn (fun ρ => ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)) (Ioi r) := by
    have := hP₁.1.sub hP₂.1
    refine this.congr_fun ?_ measurableSet_Ioi
    intro ρ _
    simp [PiLp.sub_apply, mul_sub]
  -- (ii) the outward primitive
  have hii : ENNReal.ofReal |outPrim Z₁ τ r z - outPrim Z₂ τ r z| ≤ rayW 2 (dDiff Z₁ Z₂ τ) r z := by
    rw [outPrim_diff_eq Z₁ Z₂ τ r z hP₁.1 hP₂.1, abs_neg]
    unfold rayW
    have step1 : ∀ ρ ∈ Ioi r, ENNReal.ofReal |ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)| ≤
        ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) := by
      intro ρ hρ
      have hρr : r < ρ := hρ
      have hρ0 : 0 < ρ := lt_trans hr hρr
      have hA := ray_ofReal_le Z₁ Z₂ τ z r hdiff hT ρ hρr.le
      have hc : |ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)| ≤
          ρ * ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖ := by
        rw [abs_mul, abs_of_pos hρ0]
        exact mul_le_mul_of_nonneg_left (abs_apply_le_norm _ _) hρ0.le
      calc ENNReal.ofReal |ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)|
          ≤ ENNReal.ofReal (ρ * ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖) := ENNReal.ofReal_le_ofReal hc
        _ = ENNReal.ofReal ρ * ENNReal.ofReal ‖Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)‖ :=
            ENNReal.ofReal_mul hρ0.le
        _ ≤ ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) := by
            gcongr
    set G : ℝ → ENNReal := fun σ => ENNReal.ofReal (dDiff Z₁ Z₂ τ (hpt σ z)) with hGdef
    have hGm' : Measurable G := hGm
    set F : ℝ × ℝ → ENNReal := ({q : ℝ × ℝ | r < q.1} ∩ {q : ℝ × ℝ | q.1 < q.2}).indicator
      (fun q => ENNReal.ofReal q.1 * G q.2) with hFdef
    have hFm : Measurable F := by
      apply Measurable.indicator
      · exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (hGm'.comp measurable_snd)
      · exact (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_fst measurable_snd)
    have claim2a : ∀ ρ : ℝ, (Ioi r).indicator (fun ρ => ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ) ρ
        = ∫⁻ σ, F (ρ, σ) := by
      intro ρ
      by_cases hρ : r < ρ
      · rw [Set.indicator_of_mem (show ρ ∈ Ioi r from hρ)]
        have hinner : ∀ σ, F (ρ, σ) = (Ioi ρ).indicator (fun σ => ENNReal.ofReal ρ * G σ) σ := by
          intro σ
          by_cases hσ : ρ < σ
          · simp [hFdef, Set.indicator, hρ, hσ]
          · simp [hFdef, Set.indicator, hρ, hσ]
        simp_rw [hinner]
        rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      · rw [Set.indicator_of_notMem (show ρ ∉ Ioi r from hρ)]
        have : ∀ σ, F (ρ, σ) = 0 := by
          intro σ
          simp [hFdef, hρ]
        simp [this]
    have claim2c : ∀ σ : ℝ, ∫⁻ ρ, F (ρ, σ) ≤
        (Ioi r).indicator (fun σ => ENNReal.ofReal (σ ^ 2) * G σ) σ := by
      intro σ
      by_cases hσ : r < σ
      · rw [Set.indicator_of_mem (show σ ∈ Ioi r from hσ)]
        have hF : ∀ ρ, F (ρ, σ) = (Ioo r σ).indicator (fun ρ => ENNReal.ofReal ρ * G σ) ρ := by
          intro ρ
          by_cases h1 : r < ρ
          · by_cases h2 : ρ < σ
            · simp [hFdef, Set.indicator, h1, h2]
            · simp [hFdef, Set.indicator, h1, h2]
          · simp [hFdef, Set.indicator, h1]
        simp_rw [hF]
        rw [lintegral_indicator measurableSet_Ioo]
        have hb : ∫⁻ ρ in Ioo r σ, ENNReal.ofReal ρ * G σ ≤
            ∫⁻ ρ in Ioo r σ, ENNReal.ofReal σ * G σ := by
          refine setLIntegral_mono' measurableSet_Ioo (fun ρ hρ => ?_)
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hρ.2.le) (bot_le)
        refine hb.trans ?_
        rw [setLIntegral_const, Real.volume_Ioo]
        have hsq : ENNReal.ofReal (σ ^ 2) = ENNReal.ofReal σ * ENNReal.ofReal σ := by
          rw [← ENNReal.ofReal_mul (le_of_lt (lt_trans hr hσ)), sq]
        have hlen : ENNReal.ofReal (σ - r) ≤ ENNReal.ofReal σ :=
          ENNReal.ofReal_le_ofReal (by linarith)
        rw [hsq]
        calc ENNReal.ofReal σ * G σ * ENNReal.ofReal (σ - r)
            ≤ ENNReal.ofReal σ * G σ * ENNReal.ofReal σ := mul_le_mul_of_nonneg_left hlen (bot_le)
          _ = ENNReal.ofReal σ * ENNReal.ofReal σ * G σ := by ring
      · rw [Set.indicator_of_notMem (show σ ∉ Ioi r from hσ)]
        have : ∀ ρ, F (ρ, σ) = 0 := by
          intro ρ
          by_cases h1 : r < ρ
          · have h2 : ¬ (ρ < σ) := fun h2 => hσ (lt_trans h1 h2)
            simp [hFdef, Set.indicator, h1, h2]
          · simp [hFdef, Set.indicator, h1]
        simp [this]
    have hchain : ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ ≤
        ∫⁻ σ in Ioi r, ENNReal.ofReal (σ ^ 2) * G σ := by
      calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ
          = ∫⁻ ρ, (Ioi r).indicator (fun ρ => ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ) ρ :=
            (lintegral_indicator measurableSet_Ioi _).symm
        _ = ∫⁻ ρ, ∫⁻ σ, F (ρ, σ) := lintegral_congr claim2a
        _ = ∫⁻ σ, ∫⁻ ρ, F (ρ, σ) :=
            lintegral_lintegral_swap (f := fun ρ σ => F (ρ, σ)) hFm.aemeasurable
        _ ≤ ∫⁻ σ, (Ioi r).indicator (fun σ => ENNReal.ofReal (σ ^ 2) * G σ) σ :=
            lintegral_mono claim2c
        _ = ∫⁻ σ in Ioi r, ENNReal.ofReal (σ ^ 2) * G σ := lintegral_indicator measurableSet_Ioi _
    have hstep : ∫⁻ ρ in Ioi r, ENNReal.ofReal |ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)| ≤
        ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ :=
      lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => step1 ρ hρ)
    have hfinal : ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ 2 * dDiff Z₁ Z₂ τ (hpt ρ z)) =
        ∫⁻ σ in Ioi r, ENNReal.ofReal (σ ^ 2) * G σ := by
      refine lintegral_congr fun ρ => ?_
      rw [ENNReal.ofReal_mul (sq_nonneg ρ)]
    calc ENNReal.ofReal |∫ ρ in Ioi r, ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)|
        ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal |ρ * ((Z₁ τ (hpt ρ z) - Z₂ τ (hpt ρ z)) 2)| :=
          ofReal_abs_integral_le hQ
      _ ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * ∫⁻ σ in Ioi ρ, G σ := hstep
      _ ≤ ∫⁻ σ in Ioi r, ENNReal.ofReal (σ ^ 2) * G σ := hchain
      _ = ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ 2 * dDiff Z₁ Z₂ τ (hpt ρ z)) := hfinal.symm
  -- (iii) the differentiated primitive
  have hiii : ENNReal.ofReal |primDz Z₁ τ r z - primDz Z₂ τ r z| ≤ rayW 1 (dDiff Z₁ Z₂ τ) r z := by
    have hdiffeq : primDz Z₁ τ r z - primDz Z₂ τ r z =
        ∫ ρ in Ioi r, ρ * ((fderiv ℝ (Z₁ τ) (hpt ρ z) - fderiv ℝ (Z₂ τ) (hpt ρ z))
          (coordinateVector 2)) 2 := by
      unfold primDz
      rw [← integral_sub hP₁.2.1 hP₂.2.1]
      refine integral_congr_ae (ae_of_all _ fun ρ => ?_)
      simp [mul_sub, sub_apply, PiLp.sub_apply]
    rw [hdiffeq]
    unfold rayW
    have hI2 : IntegrableOn (fun ρ => ρ * ((fderiv ℝ (Z₁ τ) (hpt ρ z) -
        fderiv ℝ (Z₂ τ) (hpt ρ z)) (coordinateVector 2)) 2) (Ioi r) := by
      refine (hP₁.2.1.sub hP₂.2.1).congr_fun ?_ measurableSet_Ioi
      intro ρ _
      simp [mul_sub, sub_apply, PiLp.sub_apply]
    refine (ofReal_abs_integral_le hI2).trans ?_
    refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => ?_)
    have hρ0 : 0 < ρ := lt_trans hr hρ
    have hL : ‖(fderiv ℝ (Z₁ τ) (hpt ρ z) - fderiv ℝ (Z₂ τ) (hpt ρ z)) (coordinateVector 2)‖ ≤
        dDiff Z₁ Z₂ τ (hpt ρ z) := by
      have h := (fderiv ℝ (Z₁ τ) (hpt ρ z) - fderiv ℝ (Z₂ τ) (hpt ρ z)).le_opNorm (coordinateVector 2)
      rw [norm_e 2, mul_one] at h
      exact h
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_pos hρ0, pow_one]
    exact mul_le_mul_of_nonneg_left ((abs_apply_le_norm _ _).trans hL) hρ0.le
  exact ⟨hi, hii, hiii⟩

end UnforcedLeray.Short.PartIIIb.Concrete
