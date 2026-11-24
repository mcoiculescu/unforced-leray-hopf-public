import UnforcedLeray.Analysis.Pressure.Young
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Absolutely integrable convolution pairings

For a kernel and test function in conjugate Lᵖ spaces, translation invariance
makes the Hölder bound uniform in the forcing variable. An actual L¹ forcing
therefore makes the full product integrable on R³ × R³. Fubini then identifies
the literal Bochner convolution pairing. No integral-exchange hypothesis is
assumed in the final identity.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace UnforcedLeray.PressureAnalysis

/-- Hölder proves integrability of every translated kernel-test product. -/
theorem kernel_test_product_integrable {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume) (y : Space) :
    Integrable (fun x => K (x - y) * ψ x) volume :=
  memLp_one_iff_integrable.mp
    (hψ.mul' (hK.comp_measurePreserving (measurePreserving_sub_right volume y)))

/-- The absolute kernel-test pairing has a bound independent of translation. -/
theorem kernel_test_integral_norm_le {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume) (y : Space) :
    (∫ x, ‖K (x - y) * ψ x‖) ≤
      (eLpNorm K p volume).toReal * (eLpNorm ψ q volume).toReal := by
  have hshift := hK.comp_measurePreserving (measurePreserving_sub_right volume y)
  have he : eLpNorm (fun x => K (x - y)) p volume = eLpNorm K p volume :=
    eLpNorm_comp_measurePreserving hK.1 (measurePreserving_sub_right volume y)
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 1) hψ.1 hshift.1
  have hn := ENNReal.toReal_mono (ENNReal.mul_ne_top hshift.2.ne hψ.2.ne) hh
  rw [ENNReal.toReal_mul] at hn
  change (eLpNorm (fun x => K (x - y) * ψ x) 1 volume).toReal ≤
    (eLpNorm (fun x => K (x - y)) p volume).toReal * (eLpNorm ψ q volume).toReal at hn
  rw [he] at hn
  have hm := kernel_test_product_integrable hK hψ y
  calc
    _ = (eLpNorm (fun x => K (x - y) * ψ x) 1 volume).toReal := by
      rw [toReal_eLpNorm hm.1, lpNorm_one_eq_integral_norm hm.1]
    _ ≤ _ := hn

/-- Joint measurability of the actual three-factor pairing integrand. -/
theorem convolution_test_aestronglyMeasurable {K f ψ : Space → ℝ}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume)
    (hψ : AEStronglyMeasurable ψ volume) :
    AEStronglyMeasurable (fun z : Space × Space => K (z.1 - z.2) * f z.2 * ψ z.1)
      ((volume : Measure Space).prod volume) :=
  ((hK.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).mul
    hf.comp_snd).mul hψ.comp_fst

/-- The full kernel-forcing-test product is absolutely integrable. -/
theorem convolution_test_integrable {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K f ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume)
    (hf : Integrable f volume) :
    Integrable (fun z : Space × Space => K (z.1 - z.2) * f z.2 * ψ z.1)
      ((volume : Measure Space).prod volume) := by
  have hm := convolution_test_aestronglyMeasurable hK.1 hf.1 hψ.1
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact Eventually.of_forall fun y =>
      ((kernel_test_product_integrable hK hψ y).mul_const (f y)).congr
        (Eventually.of_forall fun x => by ring)
  · have hnormmeas : AEStronglyMeasurable
        (fun y => ∫ x, ‖K (x - y) * f y * ψ x‖) volume :=
      hm.norm.prod_swap.integral_prod_right'
    apply (hf.norm.mul_const
      ((eLpNorm K p volume).toReal * (eLpNorm ψ q volume).toReal)).mono' hnormmeas
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    have he : (∫ x, ‖K (x - y) * f y * ψ x‖) =
        (∫ x, ‖K (x - y) * ψ x‖) * ‖f y‖ := by
      calc
        _ = ∫ x, ‖K (x - y) * ψ x‖ * ‖f y‖ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by simp only [norm_mul]; ring
        _ = _ := integral_mul_const _ _
    rw [he]
    exact (mul_le_mul_of_nonneg_right (kernel_test_integral_norm_le hK hψ y)
      (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The convolution-test pairing itself is genuinely integrable. -/
theorem convolution_mul_test_integrable {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K f ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume)
    (hf : Integrable f volume) :
    Integrable (fun x => (∫ y, K (x - y) * f y) * ψ x) volume := by
  simpa only [integral_mul_const] using
    (convolution_test_integrable hK hψ hf).integral_prod_left

/-- The outer translated pairing is genuinely integrable as well. -/
theorem forcing_mul_kernel_test_integrable {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K f ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume)
    (hf : Integrable f volume) :
    Integrable (fun y => f y * (∫ x, K (x - y) * ψ x)) volume := by
  have hi := (convolution_test_integrable hK hψ hf).integral_prod_right
  apply hi.congr
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring

/-- Fubini identifies the literal convolution with the translated test pairing. -/
theorem integral_convolution_mul_eq {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {K f ψ : Space → ℝ} (hK : MemLp K p volume) (hψ : MemLp ψ q volume)
    (hf : Integrable f volume) :
    (∫ x, (∫ y, K (x - y) * f y) * ψ x) =
      ∫ y, f y * (∫ x, K (x - y) * ψ x) := by
  calc
    _ = ∫ x, ∫ y, K (x - y) * f y * ψ x := by simp only [integral_mul_const]
    _ = ∫ y, ∫ x, K (x - y) * f y * ψ x :=
      integral_integral_swap (convolution_test_integrable hK hψ hf)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring

end UnforcedLeray.PressureAnalysis
