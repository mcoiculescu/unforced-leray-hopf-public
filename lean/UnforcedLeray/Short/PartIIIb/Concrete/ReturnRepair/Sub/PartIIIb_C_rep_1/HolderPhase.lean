import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf `HolderPhase`** (source 5175, `19/22 = 4/11 + 1/2`): Hölder at one phase. -/
theorem holderPhase : HolderPhase := by
  intro a b f ha hb hf
  have hbgp : UnforcedLeray.Short.IIb.bgp = 11 / 4 := by
    unfold UnforcedLeray.Short.IIb.bgp; norm_num
  have hr0 : (0 : ℝ) < 22 / 19 := by norm_num
  have hpq : (22 / 19 : ℝ) < 11 / 4 := by norm_num
  have hpqr : 1 / (22 / 19 : ℝ) = 1 / (11 / 4 : ℝ) + 1 / (2 : ℝ) := by norm_num
  have hAm : AEMeasurable (fun y : Space => ENNReal.ofReal ‖a y‖) volume :=
    ha.norm.aemeasurable.ennreal_ofReal
  have hBm : AEMeasurable (fun y : Space => ENNReal.ofReal ‖b y‖) volume :=
    hb.norm.aemeasurable.ennreal_ofReal
  -- pointwise domination
  have hI : (∫⁻ y, ENNReal.ofReal (f y) ^ (22 / 19 : ℝ)) ≤
      ENNReal.ofReal 2 ^ (22 / 19 : ℝ) *
        ∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hf] with y hy
    calc ENNReal.ofReal (f y) ^ (22 / 19 : ℝ)
        ≤ (ENNReal.ofReal 2 * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖)) ^ (22 / 19 : ℝ) := by
          apply ENNReal.rpow_le_rpow _ hr0.le
          calc ENNReal.ofReal (f y) ≤ ENNReal.ofReal (2 * ‖a y‖ * ‖b y‖) :=
                ENNReal.ofReal_le_ofReal hy
            _ = ENNReal.ofReal 2 * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
                  mul_assoc]
      _ = ENNReal.ofReal 2 ^ (22 / 19 : ℝ) * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖)
            ^ (22 / 19 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ hr0.le
  -- generalized Hölder with 19/22 = 4/11 + 1/2
  have hH := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr (μ := volume) hr0 hpq hpqr hAm hBm
  have hX : eLpNorm a (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume =
      (∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rw [hbgp]; norm_num)
      (by rw [hbgp]; simp), hbgp, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11 / 4)]
    congr 1
    refine lintegral_congr fun y => ?_
    simp
  have hY2 : ((∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 =
      ∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hB2 : (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ 2) = ∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ) :=
    lintegral_congr fun y => (ENNReal.rpow_two _).symm
  have hC : (ENNReal.ofReal 2 ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) = ENNReal.ofReal 2 ^ 2 := by
    rw [← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hJ : (∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) =
      ((∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ)) ^ (1 / (22 / 19 : ℝ))) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  rw [hX, hB2]
  calc (∫⁻ y, ENNReal.ofReal (f y) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))
      ≤ (ENNReal.ofReal 2 ^ (22 / 19 : ℝ) *
          ∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) :=
        ENNReal.rpow_le_rpow hI (by positivity)
    _ = ENNReal.ofReal 2 ^ 2 * (∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hC]
    _ = ENNReal.ofReal 2 ^ 2 * ((∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (22 / 19 : ℝ)) ^ (1 / (22 / 19 : ℝ))) ^ 2 := by
        rw [hJ]
    _ ≤ ENNReal.ofReal 2 ^ 2 * ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) *
          (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
        exact hH
    _ = ENNReal.ofReal 2 ^ 2 * ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))) ^ 2 *
          ((∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := by
        rw [mul_pow]; ring
    _ = ENNReal.ofReal 2 ^ 2 * ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))) ^ 2 *
          ∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (2 : ℝ) := by
        rw [hY2]

end UnforcedLeray.Short.PartIIIb.Concrete
