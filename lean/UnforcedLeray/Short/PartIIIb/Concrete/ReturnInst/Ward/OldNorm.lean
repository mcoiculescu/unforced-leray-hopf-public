import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs

/-!
# The gain norm controls the old source: `WardOldNormLe` (source 2694-2700, 4155-4156, 5609)

Source of record: `the November 2 reference manuscript` (73 pages).

`GainMeasureLower` (`Sub/IIIb-D2_3_1_1_1.lean`, queued `PartIII-b:IIIb-D2/3/1/1/1/8`) gives
`κ • s^{-1/2}dς ≤ gainZ1Measure` and `≤ gainHTMeasure`; hence
`‖G_T‖_{L²(s^{-1/2}dς)} ≤ κ^{-1/2}(‖(χ_oT)₁‖ + ‖(χ_oT)₂‖) = κ^{-1/2}‖χ_oT‖ ≤ κ^{-1/2}‖χ_o‖‖T‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A lower bound of integrals of nonnegative measurable functions is a lower bound of measures. -/
theorem wo_smul_le_of_lintegral {m m' : Measure Chart} {a : ℝ≥0∞}
    (h : ∀ f : Chart → ℝ≥0∞, Measurable f → a * ∫⁻ p, f p ∂m ≤ ∫⁻ p, f p ∂m') :
    a • m ≤ m' := by
  refine Measure.le_iff.2 fun s hs => ?_
  have h1 := h (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h1
  simpa [Measure.smul_apply, smul_eq_mul] using h1

/-- `a • m ≤ m'` with `0 < a < ∞` gives `‖f‖_{L²(m)} ≤ a^{-1/2}‖f‖_{L²(m')}`. -/
theorem wo_eLpNorm_le_of_smul_le {m m' : Measure Chart} {a : ℝ≥0∞} (ha0 : a ≠ 0)
    (hat : a ≠ ⊤) (h : a • m ≤ m') (f : Chart → Ten3) :
    eLpNorm f 2 m ≤ (a ^ (1 / (2 : ℝ≥0∞)).toReal)⁻¹ * eLpNorm f 2 m' := by
  have h1 := eLpNorm_mono_measure (p := (2 : ℝ≥0∞)) f h
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f a, smul_eq_mul] at h1
  have hpos : a ^ (1 / (2 : ℝ≥0∞)).toReal ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hat).ne'
  have htop : a ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hat
  exact (ENNReal.mul_le_iff_le_inv hpos htop).1 h1

/-- **`WardOldNormLe` from `GainMeasureLower`** (source 2694-2700, 4155-4156, 5609). -/
theorem wardOldNormLe_of (hG : GainMeasureLower) : WardOldNormLe := by
  intro c mZ ρb γ ν hρ hm hν χo hχo
  obtain ⟨κ, hκ, hκle⟩ := hG c mZ ρb γ ν hρ hm hν
  have ha0 : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  have hat : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle1 : ENNReal.ofReal κ • ageμ c (-1 / 2) ≤ gainZ1Measure c mZ γ ν :=
    wo_smul_le_of_lintegral fun f hf => (hκle f hf).1
  have hle2 : ENNReal.ofReal κ • ageμ c (-1 / 2) ≤ gainHTMeasure c ρb γ ν :=
    wo_smul_le_of_lintegral fun f hf => (hκle f hf).2
  set b : ℝ≥0∞ := (ENNReal.ofReal κ ^ (1 / (2 : ℝ≥0∞)).toReal)⁻¹ with hb
  have hbt : b ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hat).ne'
  refine ⟨b.toReal * ‖chiOStr c mZ ρb γ ν hχo‖, fun T => ?_⟩
  set S := chiOStr c mZ ρb γ ν hχo T with hS
  have hf1 : AEStronglyMeasurable (S.fst : Chart → Ten3) (ageμ c (-1 / 2)) :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  have hf2 : AEStronglyMeasurable (S.snd : Chart → Ten3) (ageμ c (-1 / 2)) :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  calc eLpNorm (strSum S) 2 (ageμ c (-1 / 2))
      = eLpNorm ((S.fst : Chart → Ten3) + (S.snd : Chart → Ten3)) 2 (ageμ c (-1 / 2)) := rfl
    _ ≤ eLpNorm (S.fst : Chart → Ten3) 2 (ageμ c (-1 / 2)) +
          eLpNorm (S.snd : Chart → Ten3) 2 (ageμ c (-1 / 2)) :=
        eLpNorm_add_le hf1 hf2 one_le_two
    _ ≤ b * eLpNorm (S.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν) +
          b * eLpNorm (S.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν) :=
        add_le_add (wo_eLpNorm_le_of_smul_le ha0 hat hle1 _)
          (wo_eLpNorm_le_of_smul_le ha0 hat hle2 _)
    _ = b * ENNReal.ofReal ‖S‖ := by
        rw [← mul_add, WithLp.prod_norm_eq_of_L1,
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm,
          ofReal_norm, Lp.enorm_def, Lp.enorm_def]
    _ ≤ b * ENNReal.ofReal (‖chiOStr c mZ ρb γ ν hχo‖ * ‖T‖) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ((chiOStr c mZ ρb γ ν hχo).le_opNorm T))
    _ = ENNReal.ofReal (b.toReal * ‖chiOStr c mZ ρb γ ν hχo‖ * ‖T‖) := by
        rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hbt]

end UnforcedLeray.Short.PartIIIb.Concrete
