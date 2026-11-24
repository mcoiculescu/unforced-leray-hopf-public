import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# `GainMeasureLower` (source 2694-2700, 3875)

The gain measures dominate `s^{-1/2} dς`: `g⁻² ≥ e^{-2|γ|/ν}` on the chart (since
`|γ s/(1+νs)| ≤ |γ|/ν` for `s ≥ 0`), `W² ≥ 1` for `m_Z ≥ 0`, and the density `ρ_b⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The gain factor is bounded below: `g⁻² ≥ e^{-2|γ|/ν}` on the chart, `ν > 0`. -/
theorem l8_ginv_sq_ge (γ ν : ℝ) (hν : 0 < ν) (p : Chart) :
    Real.exp (-(2 * |γ| / ν)) ≤ ginv γ ν p ^ 2 := by
  have ht : 0 ≤ max p.1 0 := le_max_right _ _
  have heq : ginv γ ν p ^ 2 = Real.exp (-(2 * (γ * max p.1 0 / (1 + ν * max p.1 0)))) := by
    unfold ginv UnforcedLeray.Short.IIIa.gainG
    rw [← Real.exp_neg, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hd : 0 < 1 + ν * max p.1 0 := by nlinarith [mul_nonneg hν.le ht]
  have hx : γ * max p.1 0 / (1 + ν * max p.1 0) ≤ |γ| / ν := by
    rw [div_le_div_iff₀ hd hν]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self γ)) (mul_nonneg ht hν.le), abs_nonneg γ]
  rw [heq]
  apply Real.exp_le_exp.2
  have h2 : 2 * (γ * max p.1 0 / (1 + ν * max p.1 0)) ≤ 2 * |γ| / ν := by
    have e : 2 * |γ| / ν = 2 * (|γ| / ν) := by ring
    rw [e]
    linarith
  linarith

/-- The transverse weight is at least one for `m_Z ≥ 0`. -/
theorem l8_transWeight_sq_ge (mZ : ℝ) (hm : 0 ≤ mZ) (p : Chart) :
    1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 := by
  have hT : 1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    exact Real.one_le_rpow (by nlinarith [sq_nonneg (p.2.2 / Real.sqrt (1 + p.1))]) (by linarith)
  exact one_le_pow₀ hT

/-- **The gain measures dominate `s^{-1/2}dς`** (source 2694-2700, 3875): for `ρ_b > 0`,
`m_Z ≥ 0`, `ν > 0` there is `κ > 0` with `κ ∫ f d(s^{-1/2}dς) ≤ ∫ f dgainZ1Measure` and
`≤ ∫ f dgainHTMeasure` for measurable `f ≥ 0`. -/
theorem gainMeasureLower : GainMeasureLower := by
  intro c mZ ρb γ ν hρ hm hν
  have hκpos : 0 < min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν)) :=
    mul_pos (lt_min one_pos (inv_pos.2 hρ)) (Real.exp_pos _)
  refine ⟨min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν)), hκpos, fun f hf => ?_⟩
  have hG : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ((NearInst.ginv_measurable' γ ν).pow_const 2).ennreal_ofReal
  have hW : Measurable (fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) :=
    (((NearInst.transWeight_measurable mZ).pow_const 2)).ennreal_ofReal
  have hκE : min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν)) ≤ Real.exp (-(2 * |γ| / ν)) :=
    mul_le_of_le_one_left (Real.exp_pos _).le (min_le_left _ _)
  constructor
  · -- the measure `gainZ1Measure = W² g⁻² s^{-1/2}dς`
    unfold gainZ1Measure z1Measure
    rw [lintegral_withDensity_eq_lintegral_mul _ hG hf,
      lintegral_withDensity_eq_lintegral_mul _ hW (hG.mul hf)]
    rw [← lintegral_const_mul _ hf]
    refine lintegral_mono fun p => ?_
    simp only [Pi.mul_apply]
    have h1 := l8_ginv_sq_ge γ ν hν p
    have h2 := l8_transWeight_sq_ge mZ hm p
    have hZ : min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν))
        ≤ ginv γ ν p ^ 2 * UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 :=
      (hκE.trans h1).trans (le_mul_of_one_le_right (sq_nonneg _) h2)
    calc ENNReal.ofReal (min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν))) * f p
        ≤ ENNReal.ofReal (ginv γ ν p ^ 2 * UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) * f p :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hZ) zero_le
      _ = ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
            (ENNReal.ofReal (ginv γ ν p ^ 2) * f p) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
          ring
  · -- the measure `gainHTMeasure = ρ_b⁻¹ g⁻² s^{-1/2}dς`
    unfold gainHTMeasure htRhoMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ hG hf, lintegral_smul_measure, smul_eq_mul]
    rw [← lintegral_const_mul _ hf, ← lintegral_const_mul _ (hG.mul hf)]
    refine lintegral_mono fun p => ?_
    simp only [Pi.mul_apply]
    have hκ2 : min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν)) ≤ ρb⁻¹ * ginv γ ν p ^ 2 :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left (l8_ginv_sq_ge γ ν hν p) (inv_nonneg.2 hρ.le))
    calc ENNReal.ofReal (min 1 ρb⁻¹ * Real.exp (-(2 * |γ| / ν))) * f p
        ≤ ENNReal.ofReal (ρb⁻¹ * ginv γ ν p ^ 2) * f p :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hκ2) zero_le
      _ = ENNReal.ofReal ρb⁻¹ * (ENNReal.ofReal (ginv γ ν p ^ 2) * f p) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hρ.le)]
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
