import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Gain
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.ChiOMultYoung

/-!
# `VelBinGainLe`: the bin norm is bounded by the gain-normed `L²` norm (source 3875, 5117)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise: `π ≤ e^{2|γ|/ν} · π g⁻²` for `ν > 0`. -/
theorem ginv_sq_mul_exp_ge (γ ν : ℝ) (hν : 0 < ν) (p : Chart) :
    1 ≤ (Real.exp (|γ| / ν)) ^ 2 * ginv γ ν p ^ 2 := by
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have hx := UnforcedLeray.Short.IIIa.gainG_exponent_abs_le (γ := γ) (ν := ν)
    (s := max p.1 0) hν hs
  have hg : ginv γ ν p = Real.exp (-(γ * max p.1 0 / (1 + ν * max p.1 0))) := by
    unfold ginv UnforcedLeray.Short.IIIa.gainG
    rw [Real.exp_neg]
  have h1 : 1 ≤ Real.exp (|γ| / ν) * ginv γ ν p := by
    rw [hg, ← Real.exp_add]
    apply Real.one_le_exp
    have := le_abs_self (γ * max p.1 0 / (1 + ν * max p.1 0))
    linarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Real.exp (|γ| / ν) * ginv γ ν p) ^ 2 := pow_le_pow_left₀ zero_le_one h1 2
    _ = (Real.exp (|γ| / ν)) ^ 2 * ginv γ ν p ^ 2 := mul_pow _ _ _

theorem velBinGainLe : VelBinGainLe := by
  intro c γ ν s₀ s₁ hν v
  have hE : ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hd : AEMeasurable (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2))
      (ageμ c (-3 / 2)) :=
    (measurable_const.mul ((cmo_ginv_meas γ ν).pow_const 2)).ennreal_ofReal.aemeasurable
  have hdpos : ∀ᵐ p ∂(ageμ c (-3 / 2)),
      ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) ≠ 0 := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact (ENNReal.ofReal_pos.2
      (mul_pos Real.pi_pos (pow_pos (cmo_ginv_pos γ ν p) 2))).ne'
  have hFb : AEMeasurable (fun p : Chart => ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ))
      (bodyMeasure c γ ν) :=
    (AEStronglyMeasurable.enorm (Lp.aestronglyMeasurable v)).pow_const (2 : ℝ)
  have hF : AEMeasurable (fun p : Chart => ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ))
      (ageμ c (-3 / 2)) :=
    hFb.mono_ac (withDensity_absolutelyContinuous' hd hdpos)
  have hsrc : ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(srcMeasure c) =
      ENNReal.ofReal Real.pi * ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) := by
    rw [srcMeasure, lintegral_smul_measure, smul_eq_mul]
  have hbody : ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(bodyMeasure c γ ν) =
      ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) :=
    lintegral_withDensity_eq_lintegral_mul₀ hd hF
  have hI_src : ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(srcMeasure c) ≤
      ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
        ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(bodyMeasure c γ ν) := by
    rw [hsrc, hbody]
    calc ENNReal.ofReal Real.pi * ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        = ∫⁻ p, ENNReal.ofReal Real.pi * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
            (ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ))
            ∂(ageμ c (-3 / 2)) := by
          refine lintegral_mono fun p => ?_
          have hp : ENNReal.ofReal Real.pi ≤
              ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
                ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
            rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have key := ginv_sq_mul_exp_ge γ ν hν p
            calc Real.pi = Real.pi * 1 := (mul_one _).symm
              _ ≤ Real.pi * ((Real.exp (|γ| / ν)) ^ 2 * ginv γ ν p ^ 2) :=
                  mul_le_mul_of_nonneg_left key Real.pi_pos.le
              _ = (Real.exp (|γ| / ν)) ^ 2 * (Real.pi * ginv γ ν p ^ 2) := by ring
          calc ENNReal.ofReal Real.pi * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)
              ≤ (ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
                  ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) :=
                mul_le_mul' hp le_rfl
            _ = ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
                  (ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)) :=
                mul_assoc _ _ _
      _ = ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
            ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)
              ∂(ageμ c (-3 / 2)) :=
          lintegral_const_mul' _ _ hE
  have hE12 : (ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.exp (|γ| / ν)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hnorm : ENNReal.ofReal ‖v‖ = (∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)
      ∂(bodyMeasure c γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  unfold velBin
  calc (∫⁻ p in {p : Chart | s₀ < p.1 ∧ p.1 ≤ s₁}, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)
        ∂(srcMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(srcMeasure c)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)
    _ ≤ (ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2 *
          ∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(bodyMeasure c γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI_src (by norm_num)
    _ = (ENNReal.ofReal (Real.exp (|γ| / ν)) ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ p, ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂(bodyMeasure c γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal (Real.exp (|γ| / ν)) * ENNReal.ofReal ‖v‖ := by
        rw [hE12, hnorm]

end UnforcedLeray.Short.PartIIIb.Concrete
