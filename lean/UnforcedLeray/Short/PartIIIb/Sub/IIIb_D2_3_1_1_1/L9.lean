import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L8

/-!
# `StrChartL2` (source 2694-2700, 5609)

The gain norm controls the chart `L²` moment of `T₁ + T₂`: each component has finite
`∫ ‖·‖² dgainZ1Measure` (resp. `dgainHTMeasure`) by `Lp` membership, and `GainMeasureLower`
transfers this to `ageμ c (-1/2)`; the sum is bounded by `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Measurability of the canonical representative of an `L²` class. -/
lemma l9_lp_meas {μ : Measure Chart} (F : Lp (α := Chart) Ten3 2 μ) :
    Measurable (F : Chart → Ten3) :=
  (MeasureTheory.Lp.stronglyMeasurable F).measurable

/-- The `L²` norm of an `Lp` class is finite as a lintegral of `‖·‖ₑ ^ 2`. -/
lemma l9_lp_lint {μ : Measure Chart} (F : Lp (α := Chart) Ten3 2 μ) :
    ∫⁻ p, ‖(F : Chart → Ten3) p‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.Lp.memLp F)
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top] at h
  simpa [ENNReal.rpow_two] using h

/-- `‖a + b‖ₑ ^ 2 ≤ 2 ‖a‖ₑ ^ 2 + 2 ‖b‖ₑ ^ 2` in `ℝ≥0∞`. -/
lemma l9_add_sq_le (a b : Ten3) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h1 : ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := enorm_add_le a b
  have h2 : ‖a + b‖ₑ ^ (2 : ℝ) ≤ (‖a‖ₑ + ‖b‖ₑ) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow h1 (by norm_num)
  have h3 : (‖a‖ₑ + ‖b‖ₑ) ^ (2 : ℝ) ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) * (‖a‖ₑ ^ (2 : ℝ) + ‖b‖ₑ ^ (2 : ℝ)) := by
    have := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖ₑ ‖b‖ₑ (p := 2) (by norm_num)
    rwa [show (2 : ℝ) - 1 = 1 by norm_num] at this
  calc ‖a + b‖ₑ ^ 2 = ‖a + b‖ₑ ^ (2 : ℝ) := (ENNReal.rpow_two _).symm
    _ ≤ (‖a‖ₑ + ‖b‖ₑ) ^ (2 : ℝ) := h2
    _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) * (‖a‖ₑ ^ (2 : ℝ) + ‖b‖ₑ ^ (2 : ℝ)) := h3
    _ = 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
      simp only [ENNReal.rpow_one, ENNReal.rpow_two, mul_add]

/-- A positive finite multiple `ofReal κ` of `I` being finite forces `I < ⊤`. -/
lemma l9_lt_top_of_ofReal_mul {κ : ℝ} (hκ : 0 < κ) {I : ℝ≥0∞}
    (h : ENNReal.ofReal κ * I < ⊤) : I < ⊤ := by
  have hk : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  have hkt : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have e : I = (ENNReal.ofReal κ)⁻¹ * (ENNReal.ofReal κ * I) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hk hkt, one_mul]
  rw [e]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hκ)) h

/-- **The gain norm controls the `H_T` norm of `T₁ + T₂`** (source 2694-2700, 5609; from
`GainMeasureLower` and the `L²` membership of both components). -/
theorem strChartL2 : StrChartL2 := by
  intro c mZ ρb γ ν hρ hm hν T
  have hL : GainMeasureLower := gainMeasureLower
  obtain ⟨κ, hκ, hG⟩ := hL c mZ ρb γ ν hρ hm hν
  -- finiteness of the age moments of each component
  have hAz : ∫⁻ p, ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2
      ∂(ageμ c (-1 / 2)) < ⊤ := by
    have hmeas : Measurable fun p : Chart =>
        ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2 :=
      ((l9_lp_meas (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).enorm).pow_const 2
    refine l9_lt_top_of_ofReal_mul hκ ?_
    exact lt_of_le_of_lt ((hG _ hmeas).1)
      (l9_lp_lint (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)))
  have hAh : ∫⁻ p, ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p‖ₑ ^ 2
      ∂(ageμ c (-1 / 2)) < ⊤ := by
    have hmeas : Measurable fun p : Chart =>
        ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p‖ₑ ^ 2 :=
      ((l9_lp_meas (T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).enorm).pow_const 2
    refine l9_lt_top_of_ofReal_mul hκ ?_
    exact lt_of_le_of_lt ((hG _ hmeas).2)
      (l9_lp_lint (T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)))
  -- pointwise and integral bound
  have hm1 : Measurable fun p : Chart =>
      2 * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2 :=
    ((l9_lp_meas (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).enorm.pow_const 2).const_mul 2
  have hpt : ∀ p : Chart, ‖strSum T p‖ₑ ^ 2 ≤
      2 * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2 +
        2 * ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p‖ₑ ^ 2 := by
    intro p
    exact l9_add_sq_le ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p)
      ((T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p)
  calc ∫⁻ p, ‖strSum T p‖ₑ ^ 2 ∂(ageμ c (-1 / 2))
      ≤ ∫⁻ p, (2 * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2 +
        2 * ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p‖ₑ ^ 2)
          ∂(ageμ c (-1 / 2)) := lintegral_mono hpt
    _ = ∫⁻ p, 2 * ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) p‖ₑ ^ 2
          ∂(ageμ c (-1 / 2)) +
        ∫⁻ p, 2 * ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) p‖ₑ ^ 2
          ∂(ageμ c (-1 / 2)) := lintegral_add_left hm1 _
    _ < ⊤ := by
      rw [lintegral_const_mul _ ((l9_lp_meas (T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))).enorm.pow_const 2)]
      rw [lintegral_const_mul _ ((l9_lp_meas (T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).enorm.pow_const 2)]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hAz,
        ENNReal.mul_lt_top (by norm_num) hAh⟩

end UnforcedLeray.Short.PartIIIb.Concrete
