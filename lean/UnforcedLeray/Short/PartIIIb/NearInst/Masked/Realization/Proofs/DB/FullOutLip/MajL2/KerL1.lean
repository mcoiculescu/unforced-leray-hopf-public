import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.GradKL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Lin.Basic

/-!
# `L¹` norm of the radial kernel `fmKer` (source 3604-3610, 4001)

For `t = ν(1-l²) > 0` the radial kernel `t^{-2}(1+|w|/√t)^{-4}` has `L¹` norm
`t^{-1/2} ∫(1+|u|)^{-4} du` (the substitution `w = √t u`, `dw = t^{3/2} du`). The model integral
`∫(1+|u|)^{-4} du` is finite (as in `gk1_lintegral_lt_top`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Exact `L¹` scaling of the radial kernel `t^{-2}(1+|w|/√t)^{-4}` for `t > 0`. -/
private lemma fkl1_integral (t : ℝ) (ht : 0 < t) :
    ∫⁻ v : UnforcedLeray.Space,
      ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖v‖ / Real.sqrt t) ^ (-4 : ℝ))
    = ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
      ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs0 : Real.sqrt t ≠ 0 := hs.ne'
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  -- measurability of the scaled profile `v ↦ G(√t • v)`
  have hF : Measurable (fun v : UnforcedLeray.Space =>
      ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖Real.sqrt t • v‖ / Real.sqrt t) ^ (-4 : ℝ))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.add
      ((measurable_const_smul (Real.sqrt t)).norm.div_const _)).pow_const _)
  -- the scaled profile equals the model profile
  have hJ : ∀ v : UnforcedLeray.Space,
      ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖Real.sqrt t • v‖ / Real.sqrt t) ^ (-4 : ℝ)) =
        ENNReal.ofReal (t ^ (-2 : ℝ)) * ENNReal.ofReal (((1 + ‖v‖) ^ 4)⁻¹) := by
    intro v
    have hn : ‖Real.sqrt t • v‖ / Real.sqrt t = ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs.le, mul_div_cancel_left₀ _ hs0]
    rw [hn, gk1_rpow_neg_four (1 + ‖v‖) (by positivity),
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  -- substitution `w = (√t)⁻¹ • u` in the original integral
  have hsub := gk1_lintegral_comp_smul (Real.sqrt t)⁻¹ (inv_pos.2 hs) _ hF
  have key : ∫⁻ w : UnforcedLeray.Space,
        ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖w‖ / Real.sqrt t) ^ (-4 : ℝ)) =
      ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) * ∫⁻ v : UnforcedLeray.Space,
        ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖Real.sqrt t • v‖ / Real.sqrt t) ^ (-4 : ℝ)) := by
    calc ∫⁻ w : UnforcedLeray.Space,
          ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖w‖ / Real.sqrt t) ^ (-4 : ℝ))
        = ∫⁻ w : UnforcedLeray.Space,
          ENNReal.ofReal (t ^ (-2 : ℝ) *
            (1 + ‖Real.sqrt t • ((Real.sqrt t)⁻¹ • w)‖ / Real.sqrt t) ^ (-4 : ℝ)) := by
          refine lintegral_congr fun w => ?_
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = _ := hsub
  have hint2 : ∫⁻ v : UnforcedLeray.Space,
        ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖Real.sqrt t • v‖ / Real.sqrt t) ^ (-4 : ℝ))
      = ENNReal.ofReal (t ^ (-2 : ℝ)) *
        ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹) := by
    rw [lintegral_congr hJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the constant: `(√t)^3 · t^{-2} = t^{-1/2}`
  have h4 : t ^ 2 = Real.sqrt t ^ 4 := by
    nth_rw 1 [← hsq]
    ring
  have hneg2 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hpow : ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) * ENNReal.ofReal (t ^ (-2 : ℝ)) =
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
    rw [← ENNReal.ofReal_mul (p := ((Real.sqrt t)⁻¹ ^ 3)⁻¹) (by positivity),
      gk1_rpow_half t ht, hneg2, h4]
    congr 1
    rw [inv_pow, inv_inv]
    field_simp
  calc ∫⁻ w : UnforcedLeray.Space,
        ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖w‖ / Real.sqrt t) ^ (-4 : ℝ))
      = ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) * ∫⁻ v : UnforcedLeray.Space,
        ENNReal.ofReal (t ^ (-2 : ℝ) * (1 + ‖Real.sqrt t • v‖ / Real.sqrt t) ^ (-4 : ℝ)) := key
    _ = ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) * (ENNReal.ofReal (t ^ (-2 : ℝ)) *
        ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹)) := by rw [hint2]
    _ = (ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) * ENNReal.ofReal (t ^ (-2 : ℝ))) *
        ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹) := by rw [mul_assoc]
    _ = ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
        ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹) := by rw [hpow]

/-- **`L¹` norm of the radial kernel** (source 3604-3610, 4001): `∫ fmKer ν l ≤ C t^{-1/2}`. -/
theorem fmKerL1 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmKerL1 := by
  have hint : Integrable (fun u : UnforcedLeray.Space => ((1 + ‖u‖) ^ 4)⁻¹) := by
    refine (integrable_one_add_norm (μ := volume) (r := 4) ?_).congr
      (Filter.Eventually.of_forall fun u => ?_)
    · rw [finrank_euclideanSpace_fin]; norm_num
    · show (1 + ‖u‖) ^ (-4 : ℝ) = _
      rw [gk1_rpow_neg_four (1 + ‖u‖) (by positivity)]
  have hI : ∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹) < ⊤ :=
    hint.lintegral_lt_top
  refine ⟨(∫⁻ u : UnforcedLeray.Space, ENNReal.ofReal (((1 + ‖u‖) ^ 4)⁻¹)).toReal,
    ENNReal.toReal_nonneg, fun ν hν l hl => ?_⟩
  have h1l : 0 < 1 - l ^ 2 := by nlinarith [hl.1, hl.2]
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν h1l
  have hfeq : ∀ w : UnforcedLeray.Space, fmKer ν l w =
      ENNReal.ofReal ((ν * (1 - l ^ 2)) ^ (-2 : ℝ) *
        (1 + ‖w‖ / Real.sqrt (ν * (1 - l ^ 2))) ^ (-4 : ℝ)) := by
    intro w
    unfold fmKer
    rw [if_pos hl]
  rw [lintegral_congr hfeq, fkl1_integral _ ht, ENNReal.ofReal_toReal hI.ne]
  exact le_of_eq (mul_comm _ _)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
