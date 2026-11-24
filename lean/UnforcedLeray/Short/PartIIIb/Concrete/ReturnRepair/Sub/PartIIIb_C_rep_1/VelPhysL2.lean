import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.SrcPairing.Lift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.MeasureCmp
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# Leaf `VelPhysL2` (`PartIII-b:C/rep/1/5`, source 2683-2689, 5118, 5173-5176)

`P⁻¹∫₀ᴾ∫|𝒩_v w|² = π R² ∫|w|² s^{-3/2} dς ≤ R² e^{2γ/ν} ‖w‖²_{VelG}` for `γ ≥ 0`
(`g⁻¹ ≥ e^{-γ/ν}`), with `C₁ = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem velPhysL2_aux (c γ ν ε : ℝ) (hγ : 0 ≤ γ) (hν : 0 < ν) (w : VelG c γ ν) :
    ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) *
        ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) ≤
      ENNReal.ofReal ((1 * ε⁻¹ * Real.exp (γ / ν) * ‖w‖) ^ 2) := by
  have hmeas : Measurable (w : Chart → Merid) := (Lp.stronglyMeasurable w).measurable
  have hgm : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    (((NearInst.ginv_measurable' γ ν).pow_const 2).const_mul Real.pi).ennreal_ofReal
  have hwm : Measurable fun p : Chart => ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) :=
    hmeas.enorm.pow_const _
  have hI : ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν =
      ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ)
        ∂ageμ c (-3 / 2) := by
    unfold bodyMeasure
    exact lintegral_withDensity_eq_lintegral_mul _ hgm hwm
  have hlow : ENNReal.ofReal (Real.pi * Real.exp (-(γ / ν)) ^ 2) *
      ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) ≤
      ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν := by
    rw [hI, ← lintegral_const_mul _ hwm]
    refine lintegral_mono fun p => ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have := ginv_ge_exp γ ν hν p
    rw [abs_of_nonneg hγ] at this
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le this 2) Real.pi_pos.le
  have hnorm : ENNReal.ofReal ‖w‖ = eLpNorm (w : Chart → Merid) 2 (bodyMeasure c γ ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp w).eLpNorm_lt_top.ne]
  have hE : eLpNorm (w : Chart → Merid) 2 (bodyMeasure c γ ν) ^ 2 =
      ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hrhs : ENNReal.ofReal ((1 * ε⁻¹ * Real.exp (γ / ν) * ‖w‖) ^ 2) =
      ENNReal.ofReal (ε⁻¹ ^ 2 * Real.exp (γ / ν) ^ 2) *
        ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν := by
    rw [← hE, ← hnorm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hrhs]
  have hexp : Real.exp (γ / ν) * Real.exp (-(γ / ν)) = 1 := by rw [← Real.exp_add]; simp
  have hcoef : ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) =
      ENNReal.ofReal (ε⁻¹ ^ 2 * Real.exp (γ / ν) ^ 2) *
        ENNReal.ofReal (Real.pi * Real.exp (-(γ / ν)) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc Real.pi * ε⁻¹ ^ 2
        = ε⁻¹ ^ 2 * Real.pi * (Real.exp (γ / ν) * Real.exp (-(γ / ν))) ^ 2 := by rw [hexp]; ring
      _ = _ := by ring
  rw [hcoef, mul_assoc]
  exact mul_le_mul' le_rfl hlow

theorem velPhysL2 : VelPhysL2 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Pl hγ L w
  have hc := cOf_pos L.ν_pos
  have hε := L.ε_pos
  have h1 := SrcPairing.sp_lintegral_velPhys hc hε (Lp.stronglyMeasurable w).measurable
  have e1 : ∀ (t : ℝ) (y : Space),
      ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 =
        ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ₑ ^ (2 : ℝ) := fun t y => by
    rw [ofReal_norm, ENNReal.rpow_two]
  simp only [e1]
  rw [h1]
  exact velPhysL2_aux (cOf L.ν) (gRate Pl) L.ν L.ε hγ L.ν_pos w

end UnforcedLeray.Short.PartIIIb.Concrete
