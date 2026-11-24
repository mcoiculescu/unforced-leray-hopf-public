import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Defs


set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(iii), one phase** (source 5175; `1/2 = 4/11 + 3/22`): Hölder with the triple
`(p, q, r) = (2, 11/4, 22/3)` in `ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr`, squared. -/
theorem RecvConvOrg.recvHolderPhase : RecvConvOrg.RecvHolderPhase := by
  intro a b f ha hb hf
  have hbgp : UnforcedLeray.Short.IIb.bgp = 11 / 4 := by
    unfold UnforcedLeray.Short.IIb.bgp; norm_num
  have hp0 : (0 : ℝ) < 2 := by norm_num
  have hpq : (2 : ℝ) < 11 / 4 := by norm_num
  have hpqr : 1 / (2 : ℝ) = 1 / (11 / 4 : ℝ) + 1 / (22 / 3 : ℝ) := by norm_num
  have hAm : AEMeasurable (fun y : Space => ENNReal.ofReal ‖a y‖) volume :=
    ha.norm.aemeasurable.ennreal_ofReal
  have hBm : AEMeasurable (fun y : Space => ENNReal.ofReal ‖b y‖) volume :=
    hb.norm.aemeasurable.ennreal_ofReal
  -- pointwise domination
  have hpt : ∀ᵐ y ∂(volume : Measure Space),
      ENNReal.ofReal (f y) ^ (2 : ℝ) ≤
        ENNReal.ofReal 2 ^ (2 : ℝ) * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ) := by
    filter_upwards [hf] with y hy
    have h1 : ENNReal.ofReal (f y) ≤
        ENNReal.ofReal 2 * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) := by
      calc ENNReal.ofReal (f y) ≤ ENNReal.ofReal (2 * ‖a y‖ * ‖b y‖) :=
            ENNReal.ofReal_le_ofReal hy
        _ = ENNReal.ofReal 2 * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
              mul_assoc]
    calc ENNReal.ofReal (f y) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal 2 * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal 2 ^ (2 : ℝ) * (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hI0 : (∫⁻ y, ENNReal.ofReal (f y) ^ (2 : ℝ)) ≤
      ENNReal.ofReal 2 ^ (2 : ℝ) *
        ∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)]
    exact lintegral_mono_ae hpt
  -- generalized Hölder with 1/2 = 4/11 + 3/22
  have hH : (∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
      (∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) *
        (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ)) :=
    ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0 hpq hpqr volume hAm hBm
  have hsq : (∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ)) =
      ((∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hI : (∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ)) ≤
      ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) *
        (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ))) ^ 2 := by
    rw [hsq]
    gcongr
  -- the norms in the statement
  have hX : eLpNorm a (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume =
      (∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rw [hbgp]; norm_num)
      (by rw [hbgp]; simp), hbgp, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11 / 4)]
    congr 1
    refine lintegral_congr fun y => ?_
    simp
  have hBe : (∫⁻ y, ‖b y‖ₑ ^ (22 / 3 : ℝ)) = ∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ) :=
    lintegral_congr fun y => by
      congr 1
      exact (ofReal_norm (b y)).symm
  have hJ : (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (2 / (22 / 3 : ℝ)) =
      ((∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ))) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have h2 : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hX, hBe, hJ, h2, ENNReal.rpow_one]
  calc ∫⁻ y, ENNReal.ofReal (f y) ^ (2 : ℝ)
      ≤ ENNReal.ofReal 2 ^ (2 : ℝ) *
          ∫⁻ y, (ENNReal.ofReal ‖a y‖ * ENNReal.ofReal ‖b y‖) ^ (2 : ℝ) := hI0
    _ ≤ ENNReal.ofReal 2 ^ (2 : ℝ) *
          ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) *
            (∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ))) ^ 2 := by
        gcongr
    _ = ENNReal.ofReal 2 ^ 2 * ((∫⁻ y, ENNReal.ofReal ‖a y‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))) ^ 2 *
          ((∫⁻ y, ENNReal.ofReal ‖b y‖ ^ (22 / 3 : ℝ)) ^ (1 / (22 / 3 : ℝ))) ^ 2 := by
        rw [ENNReal.rpow_two, mul_pow]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
