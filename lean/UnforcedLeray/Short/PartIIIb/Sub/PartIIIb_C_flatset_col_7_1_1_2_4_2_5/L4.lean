import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# `CellWeightedL2P`: weighted Cauchy-Schwarz and Tonelli

Source `the November 2 reference manuscript`
3426-3430 (`‖∇b(s)‖² ≤ (s/(μ+1))² sup_σ ‖∇e^{ν(s-σ)Δ}G(σ)‖²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (tnorm2)

/-- Beta-type integral of the weight. -/
theorem wpow_lintegral (s μ : ℝ) (hs : 0 < s) (hμ : -1 < μ) :
    ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) = ENNReal.ofReal (s / (μ + 1)) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ μ) (Ioc 0 s) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).1
      (intervalIntegral.intervalIntegrable_rpow' hμ)
  have hiOc : IntegrableOn (fun σ : ℝ => (σ / s) ^ μ) (Ioc 0 s) volume :=
    IntegrableOn.congr_fun (Integrable.const_mul h0 ((s ^ μ)⁻¹))
      (fun σ hσ => by
        rw [Real.div_rpow hσ.1.le hs.le, div_eq_inv_mul]) measurableSet_Ioc
  rw [← ofReal_integral_eq_lintegral_ofReal hiOc]
  · congr 1
    rw [← intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_comp_div
      (fun x : ℝ => x ^ μ) hs.ne']
    rw [integral_rpow (Or.inl hμ)]
    simp only [zero_div, smul_eq_mul]
    rw [Real.zero_rpow (by linarith), div_self hs.ne', Real.one_rpow]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    exact Real.rpow_nonneg (div_nonneg hσ.1.le hs.le) _

/-- Weighted Cauchy-Schwarz in `[0,∞]`. -/
theorem weighted_cs_enn (μm : Measure ℝ) (w g : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hg : AEMeasurable g μm) :
    (∫⁻ σ, w σ * g σ ∂μm) ^ 2 ≤ (∫⁻ σ, w σ ∂μm) * ∫⁻ σ, w σ * g σ ^ 2 ∂μm := by
  have hf : AEMeasurable (fun σ => w σ ^ (1 / 2 : ℝ)) μm := (hw.pow_const _).aemeasurable
  have hg' : AEMeasurable (fun σ => w σ ^ (1 / 2 : ℝ) * g σ) μm := hf.mul hg
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μm Real.HolderConjugate.two_two hf hg'
  have e1 : ∀ σ, ((fun σ => w σ ^ (1 / 2 : ℝ)) * fun σ => w σ ^ (1 / 2 : ℝ) * g σ) σ
      = w σ * g σ := by
    intro σ
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ σ, (w σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w σ := by
    intro σ
    rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ σ, (w σ ^ (1 / 2 : ℝ) * g σ) ^ (2 : ℝ) = w σ * g σ ^ 2 := by
    intro σ
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
  have h' : ∫⁻ σ, w σ * g σ ∂μm ≤ (∫⁻ σ, w σ ∂μm) ^ (1 / 2 : ℝ) *
      (∫⁻ σ, w σ * g σ ^ 2 ∂μm) ^ (1 / 2 : ℝ) := by
    calc ∫⁻ σ, w σ * g σ ∂μm
        = ∫⁻ σ, ((fun σ => w σ ^ (1 / 2 : ℝ)) * fun σ => w σ ^ (1 / 2 : ℝ) * g σ) σ ∂μm :=
          lintegral_congr (fun σ => (e1 σ).symm)
      _ ≤ _ := h
      _ = _ := by simp_rw [e2, e3]
  calc (∫⁻ σ, w σ * g σ ∂μm) ^ 2
      ≤ ((∫⁻ σ, w σ ∂μm) ^ (1 / 2 : ℝ) * (∫⁻ σ, w σ * g σ ^ 2 ∂μm) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem ofReal_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    ENNReal.ofReal (tnorm2 T ^ 2) = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ₑ ^ 2 := by
  have h : tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    unfold tnorm2
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [h, ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The pointwise step: Bochner integral against the weight is bounded by weighted
Cauchy-Schwarz. -/
theorem weighted_point (s μ : ℝ) (hs : 0 < s) (hμ : -1 < μ) (g : ℝ → ℂ)
    (hg : AEMeasurable (fun σ => ‖g σ‖ₑ) (volume.restrict (Ioc 0 s))) :
    ‖∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * g σ‖ₑ ^ 2 ≤
      ENNReal.ofReal (s / (μ + 1)) *
        ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * ‖g σ‖ₑ ^ 2 := by
  rw [intervalIntegral.integral_of_le hs.le]
  have hw : Measurable fun σ : ℝ => ENNReal.ofReal ((σ / s) ^ μ) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.div_const s).pow_const μ)
  have h1 : ‖∫ σ in Ioc 0 s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * g σ‖ₑ ≤
      ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * ‖g σ‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    have hc : ∀ x : ℝ, ‖(x : ℂ)‖ₑ = ‖x‖ₑ := fun x => by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
    rw [enorm_mul, ← Complex.ofReal_cpow (div_nonneg hσ.1.le hs.le), hc,
      Real.enorm_of_nonneg (Real.rpow_nonneg (div_nonneg hσ.1.le hs.le) _)]
  have h2 := weighted_cs_enn (volume.restrict (Ioc 0 s)) _ _ hw hg
  rw [wpow_lintegral s μ hs hμ] at h2
  exact (pow_le_pow_left' h1 2).trans h2

theorem sum_lintegral_le_lintegral_sum {ι : Type*} (A : Finset ι) (f : ι → ℝ → ℝ≥0∞)
    (μm : Measure ℝ) :
    ∑ i ∈ A, ∫⁻ σ, f i σ ∂μm ≤ ∫⁻ σ, ∑ i ∈ A, f i σ ∂μm := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add (f a) (fun σ => ∑ i ∈ A, f i σ))

theorem cellWeightedL2 : CellWeightedL2P := by
  intro s μ K G S hs hμ hS hmeas hbound
  set W : ℝ≥0∞ := ENNReal.ofReal (s / (μ + 1)) with hW
  have hW_ne : W ≠ ⊤ := ENNReal.ofReal_ne_top
  have hw : Measurable fun σ : ℝ => ENNReal.ofReal ((σ / s) ^ μ) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.div_const s).pow_const μ)
  set Φ : ℝ → ℝ × ℝ → ℝ≥0∞ := fun σ x => ENNReal.ofReal (tnorm2 (G σ x) ^ 2) with hΦdef
  have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioc 0 s ×ˢ S) =
      (volume.restrict (Ioc 0 s)).prod (volume.restrict S) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hprod] at hmeas
  have hcomp : ∀ i j, AEMeasurable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2 i j)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict S)) := fun i j =>
    aemeasurable_pi_iff.1 (aemeasurable_pi_iff.1 hmeas i) j
  have hΦ : AEMeasurable (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict S)) := by
    simp_rw [hΦdef, ofReal_tnorm2_sq]
    exact Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      ((hcomp i j).enorm).pow_const 2
  have hx : ∀ᵐ x ∂(volume.restrict S), ∀ i j,
      AEMeasurable (fun σ => ‖G σ x i j‖ₑ) (volume.restrict (Ioc 0 s)) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    filter_upwards [(hcomp i j).aestronglyMeasurable.prodMk_right] with x hx
    exact hx.aemeasurable.enorm
  have hpt : ∀ᵐ x ∂(volume.restrict S),
      ENNReal.ofReal (tnorm2 (fun i j => ∫ σ in (0 : ℝ)..s,
        ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * G σ x i j) ^ 2) ≤
      W * ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x := by
    filter_upwards [hx] with x hx
    rw [ofReal_tnorm2_sq]
    calc ∑ i : Fin 2, ∑ j : Fin 2, ‖∫ σ in (0 : ℝ)..s,
            ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * G σ x i j‖ₑ ^ 2
        ≤ ∑ i : Fin 2, ∑ j : Fin 2, W * ∫⁻ σ in Ioc 0 s,
            ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            weighted_point s μ hs hμ (fun σ => G σ x i j) (hx i j)
      _ = W * ∑ i : Fin 2, ∑ j : Fin 2, ∫⁻ σ in Ioc 0 s,
            ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2 := by
          simp_rw [Finset.mul_sum]
      _ ≤ W * ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x := by
          gcongr
          calc ∑ i : Fin 2, ∑ j : Fin 2, ∫⁻ σ in Ioc 0 s,
                ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2
              ≤ ∑ i : Fin 2, ∫⁻ σ in Ioc 0 s, ∑ j : Fin 2,
                ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2 :=
                Finset.sum_le_sum fun i _ => sum_lintegral_le_lintegral_sum _
                  (fun j σ => ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2) _
            _ ≤ ∫⁻ σ in Ioc 0 s, ∑ i : Fin 2, ∑ j : Fin 2,
                ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2 :=
                sum_lintegral_le_lintegral_sum _
                  (fun i σ => ∑ j : Fin 2, ENNReal.ofReal ((σ / s) ^ μ) * ‖G σ x i j‖ₑ ^ 2) _
            _ = _ := by
                refine lintegral_congr fun σ => ?_
                simp only [hΦdef, ofReal_tnorm2_sq, Finset.mul_sum]
  have hF : AEMeasurable (Function.uncurry fun (x : ℝ × ℝ) (σ : ℝ) =>
      ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x)
      ((volume.restrict S).prod (volume.restrict (Ioc 0 s))) :=
    AEMeasurable.prod_swap (f := fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal ((p.1 / s) ^ μ) * Φ p.1 p.2)
      ((hw.comp measurable_fst).aemeasurable.mul hΦ)
  calc ∫⁻ x in S, ENNReal.ofReal (tnorm2 (fun i j => ∫ σ in (0 : ℝ)..s,
        ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * G σ x i j) ^ 2)
      ≤ ∫⁻ x in S, W * ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x :=
        lintegral_mono_ae hpt
    _ = W * ∫⁻ x in S, ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x :=
        lintegral_const_mul' _ _ hW_ne
    _ = W * ∫⁻ σ in Ioc 0 s, ∫⁻ x in S, ENNReal.ofReal ((σ / s) ^ μ) * Φ σ x := by
        rw [lintegral_lintegral_swap hF]
    _ ≤ W * ∫⁻ σ in Ioc 0 s, ENNReal.ofReal ((σ / s) ^ μ) * ENNReal.ofReal K := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [hbound] with σ hσ
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl hσ
    _ = W * (W * ENNReal.ofReal K) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, wpow_lintegral s μ hs hμ]
    _ = ENNReal.ofReal ((s / (μ + 1)) ^ 2 * K) := by
        have h0 : 0 ≤ s / (μ + 1) := div_nonneg hs.le (by linarith)
        rw [hW, ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h0]
        congr 1
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
