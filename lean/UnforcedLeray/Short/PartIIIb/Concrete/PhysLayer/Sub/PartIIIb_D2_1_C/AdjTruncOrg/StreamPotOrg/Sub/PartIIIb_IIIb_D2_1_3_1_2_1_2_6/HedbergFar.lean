import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Radial profile of the squared Biot-Savart kernel on the far region `t ≥ R`. -/
def farProf (R : ℝ) (t : ℝ) : ℝ :=
  (Ici R).indicator (fun t : ℝ => ((4 * Real.pi)⁻¹ * (t ^ 2)⁻¹) ^ 2) t

lemma finrank_space_three : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

lemma farProf_key {y : ℝ} (hy : 0 < y) :
    y ^ 2 * ((4 * Real.pi)⁻¹ * (y ^ 2)⁻¹) ^ 2 = ((4 * Real.pi)⁻¹) ^ 2 * y ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hy.le, Real.rpow_two]
  have hy0 : y ≠ 0 := hy.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

lemma farProf_integrable {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • farProf R y) (Ioi 0) := by
  have hfd : Module.finrank ℝ Space - 1 = 2 := by rw [finrank_space_three]
  simp only [hfd, smul_eq_mul]
  have h1 : IntegrableOn (fun t : ℝ => ((4 * Real.pi)⁻¹) ^ 2 * t ^ (-2 : ℝ)) (Ici R) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hR).const_mul _
  have h2 : Integrable ((Ici R).indicator (fun t : ℝ => ((4 * Real.pi)⁻¹) ^ 2 * t ^ (-2 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ici).mpr h1
  refine h2.integrableOn.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  by_cases hyR : y ∈ Ici R
  · rw [farProf, Set.indicator_of_mem hyR, Set.indicator_of_mem hyR]
    exact (farProf_key hy').symm
  · simp [farProf, Set.indicator_apply, hyR]

lemma farProf_integral {R : ℝ} (hR : 0 < R) :
    ∫ y in Ioi (0 : ℝ), y ^ 2 * farProf R y = ((4 * Real.pi)⁻¹) ^ 2 * R⁻¹ := by
  have hEq : ∫ y in Ioi (0 : ℝ), y ^ 2 * farProf R y
      = ∫ y in Ioi (0 : ℝ),
          (Ici R).indicator (fun t : ℝ => ((4 * Real.pi)⁻¹) ^ 2 * t ^ (-2 : ℝ)) y := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy' : 0 < y := hy
    by_cases hyR : y ∈ Ici R
    · rw [farProf, Set.indicator_of_mem hyR, Set.indicator_of_mem hyR]
      exact farProf_key hy'
    · simp [farProf, Set.indicator_apply, hyR]
  rw [hEq, setIntegral_indicator measurableSet_Ici]
  have hI : Ioi (0 : ℝ) ∩ Ici R = Ici R := inter_eq_right.mpr (Ici_subset_Ioi.mpr hR)
  rw [hI, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) hR]
  norm_num [Real.rpow_neg_one]

lemma farProf_lintegral_eq {R : ℝ} (hR : 0 < R) :
    ∫ w : Space, farProf R ‖w‖ = (4 * Real.pi * R)⁻¹ := by
  have hfd : Module.finrank ℝ Space - 1 = 2 := by rw [finrank_space_three]
  have hb : volume.real (ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal zero_le_one,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [integral_fun_norm_addHaar volume (farProf R), hfd, finrank_space_three, hb]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [farProf_integral hR]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hR0 : R ≠ 0 := hR.ne'
  push_cast
  field_simp

lemma farProf_integrable_norm {R : ℝ} (hR : 0 < R) :
    Integrable (fun w : Space => farProf R ‖w‖) volume :=
  (integrable_fun_norm_addHaar volume (f := farProf R)).mpr (farProf_integrable hR)

lemma mem_ball_iff_norm_lt (y z : Space) (R : ℝ) : z ∈ ball y R ↔ ‖y - z‖ < R := by
  rw [mem_ball, dist_eq_norm, norm_sub_rev]

lemma farSq_eq (y : Space) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in (ball y R)ᶜ, bsK2 (y - z) ^ 2 = ENNReal.ofReal (4 * Real.pi * R)⁻¹ := by
  have hS : MeasurableSet (ball y R)ᶜ := measurableSet_ball.compl
  have hpt : ∀ z : Space, (ball y R)ᶜ.indicator (fun z => bsK2 (y - z) ^ 2) z
      = ENNReal.ofReal (farProf R ‖y - z‖) := by
    intro z
    by_cases hlt : ‖y - z‖ < R
    · have hz : z ∈ ball y R := (mem_ball_iff_norm_lt y z R).mpr hlt
      have hnotIci : ‖y - z‖ ∉ Ici R := fun h => absurd (mem_Ici.mp h) (not_le.mpr hlt)
      simp [Set.indicator_apply, farProf, hz, hnotIci]
    · have hz : z ∉ ball y R := fun h => hlt ((mem_ball_iff_norm_lt y z R).mp h)
      have hmem : ‖y - z‖ ∈ Ici R := mem_Ici.mpr (not_lt.mp hlt)
      rw [Set.indicator_of_mem (mem_compl hz), farProf, Set.indicator_of_mem hmem]
      unfold bsK2
      rw [← ENNReal.ofReal_pow (p := (4 * Real.pi)⁻¹ * (‖y - z‖ ^ 2)⁻¹) (by positivity) 2]
  have hint : Integrable (fun w : Space => farProf R ‖w‖) volume := farProf_integrable_norm hR
  have hnn : 0 ≤ᵐ[volume] (fun w : Space => farProf R ‖w‖) :=
    Eventually.of_forall (fun w => by
      unfold farProf
      exact Set.indicator_nonneg (fun t _ => by positivity) _)
  calc ∫⁻ z in (ball y R)ᶜ, bsK2 (y - z) ^ 2
      = ∫⁻ z, (ball y R)ᶜ.indicator (fun z => bsK2 (y - z) ^ 2) z := (lintegral_indicator hS _).symm
    _ = ∫⁻ z, ENNReal.ofReal (farProf R ‖y - z‖) := lintegral_congr hpt
    _ = ∫⁻ z, ENNReal.ofReal (farProf R ‖z‖) := by
        have h3 := lintegral_sub_left_eq_self (μ := volume)
          (fun w : Space => ENNReal.ofReal (farProf R ‖w‖)) y
        simpa using h3
    _ = ENNReal.ofReal (∫ w : Space, farProf R ‖w‖) := (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (4 * Real.pi * R)⁻¹ := by rw [farProf_lintegral_eq hR]

theorem hedbergFar : HedbergFar := by
  intro G hG y R hR
  have hS : MeasurableSet (ball y R)ᶜ := measurableSet_ball.compl
  have hk : Measurable (fun z : Space => bsK2 (y - z)) := by
    unfold bsK2
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have e1 : ∫⁻ z in (ball y R)ᶜ, G z * bsK2 (y - z)
      = ∫⁻ z, (ball y R)ᶜ.indicator G z * (ball y R)ᶜ.indicator (fun z => bsK2 (y - z)) z := by
    rw [← lintegral_indicator hS]
    refine lintegral_congr (fun z => ?_)
    by_cases hz : z ∈ (ball y R)ᶜ <;> simp [Set.indicator_apply, hz]
  have hG1 : Measurable ((ball y R)ᶜ.indicator G) := hG.indicator hS
  have hk1 : Measurable ((ball y R)ᶜ.indicator (fun z => bsK2 (y - z))) := hk.indicator hS
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume (p := 2) (q := 2)
    Real.HolderConjugate.two_two hG1.aemeasurable hk1.aemeasurable
  simp only [ENNReal.rpow_two, Pi.mul_apply] at hH
  have hA : ∫⁻ z, ((ball y R)ᶜ.indicator G z) ^ 2 ≤ ∫⁻ z, G z ^ 2 :=
    lintegral_mono (fun z => by
      by_cases hz : z ∈ (ball y R)ᶜ <;> simp [Set.indicator_apply, hz])
  have hB : ∫⁻ z, ((ball y R)ᶜ.indicator (fun z => bsK2 (y - z)) z) ^ 2
      ≤ ENNReal.ofReal (4 * Real.pi * R)⁻¹ := by
    have hpt2 : ∀ z, ((ball y R)ᶜ.indicator (fun z => bsK2 (y - z)) z) ^ 2
        = (ball y R)ᶜ.indicator (fun z => bsK2 (y - z) ^ 2) z := by
      intro z
      by_cases hz : z ∈ (ball y R)ᶜ <;> simp [Set.indicator_apply, hz]
    rw [lintegral_congr hpt2, lintegral_indicator hS, farSq_eq y hR]
  have hpow : ∀ x w : ℝ≥0∞, x ≤ w → x ^ (1 / 2 : ℝ) ≤ w ^ (1 / 2 : ℝ) :=
    fun x w h => ENNReal.rpow_le_rpow h (by norm_num)
  have hC : ENNReal.ofReal (4 * Real.pi * R)⁻¹ ^ (1 / 2 : ℝ)
      = ENNReal.ofReal ((4 * Real.pi * R) ^ (-(1 / 2 : ℝ))) := by
    have hx : (0 : ℝ) ≤ 4 * Real.pi * R := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.inv_rpow hx,
      ← Real.rpow_neg hx]
  rw [e1]
  refine le_trans hH ?_
  refine le_trans (mul_le_mul' (hpow _ _ hA) (hpow _ _ hB)) ?_
  exact le_of_eq (by rw [hC])

end UnforcedLeray.Short.PartIIIb.Concrete
