import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Lin.Helpers

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/4` (`StrPairBd`): the stress pairing is bounded by `C ‖T‖`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

`StrChartBound` bounds the value by the `L²(region)` norm of `strSum T`; `StrMeasureCmp` dominates
`ageμ c (-1/2)` on the region by both gain measures, so Minkowski and `eLpNorm_le_of_measure_le_smul`
give a bound by `‖T₁‖_{Z₁} + ‖T₂‖_{H_T}`, which is `‖T‖` in `WithLp 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem strPairBd_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrPairBd := by
  intro c mZ ρb γ ν ε hc hν hε hρ Φ hΦ
  obtain ⟨Y, K0, hK0, hB⟩ := strChartBound_proved c ε hc hε Φ hΦ
  obtain ⟨K, hKtop, -, h1, h2, -⟩ := strMeasureCmp_proved c mZ ρb γ ν hν hρ Y
  refine ⟨K0 * (K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal, fun T => ?_⟩
  -- the region norm of `strSum T` is the `L²` norm (the chart bound's right-hand side)
  have hB' := (hB (strSum T) (strSum_measurable_lin T)
    (lintegral_rpow_two_lt_top_lin (memLp_region_strSum_lin hν hρ Y T))).2
  have hEq : (∫⁻ p in StrRegion Y, ‖strSum T p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) =
      eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hval : ‖strPairVal c mZ ρb γ ν ε Φ T‖ ≤
      K0 * (eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y))).toReal := by
    unfold strPairVal
    rw [hEq] at hB'
    exact hB'
  -- pointwise `L²` bounds on the region
  have hf1 : eLpNorm (T.fst : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) ≤
      K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν) := by
    have a1 := eLpNorm_le_of_measure_le_smul h1 (f := (T.fst : Chart → Ten3)) (p := 2)
    have a2 := eLpNorm_mono_measure (T.fst : Chart → Ten3) (p := 2)
      (Measure.restrict_le_self (μ := gainZ1Measure c mZ γ ν) (s := StrRegion Y))
    exact a1.trans (by rw [smul_eq_mul]; gcongr)
  have hf2 : eLpNorm (T.snd : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) ≤
      K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν) := by
    have b1 := eLpNorm_mono_measure (T.snd : Chart → Ten3) (p := 2)
      (Measure.restrict_le_self (μ := ageμ c (-1 / 2)) (s := StrRegion Y))
    have b2 := eLpNorm_le_of_measure_le_smul h2 (f := (T.snd : Chart → Ten3)) (p := 2)
    exact b1.trans (b2.trans_eq (smul_eq_mul _ _))
  have hmink : eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) ≤
      eLpNorm (T.fst : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) +
        eLpNorm (T.snd : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) := by
    have e : strSum T = (T.fst : Chart → Ten3) + (T.snd : Chart → Ten3) := rfl
    rw [e]
    exact eLpNorm_add_le (Lp.stronglyMeasurable T.fst).aestronglyMeasurable
      (Lp.stronglyMeasurable T.snd).aestronglyMeasurable (by norm_num)
  have hE : eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) ≤
      K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν) +
        K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν) :=
    hmink.trans (add_le_add hf1 hf2)
  have hs_top : K ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hKtop
  have he1 : eLpNorm (T.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν) ≠ ⊤ :=
    (Lp.memLp T.fst).eLpNorm_lt_top.ne
  have he2 : eLpNorm (T.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν) ≠ ⊤ :=
    (Lp.memLp T.snd).eLpNorm_lt_top.ne
  have hRne : K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν) +
      K ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (T.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hs_top he1, ENNReal.mul_ne_top hs_top he2⟩
  have hR := ENNReal.toReal_mono hRne hE
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hs_top he1) (ENNReal.mul_ne_top hs_top he2),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at hR
  have hn1 : ‖(T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))‖ =
      (eLpNorm (T.fst : Chart → Ten3) 2 (gainZ1Measure c mZ γ ν)).toReal := Lp.norm_def _
  have hn2 : ‖(T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))‖ =
      (eLpNorm (T.snd : Chart → Ten3) 2 (gainHTMeasure c ρb γ ν)).toReal := Lp.norm_def _
  have hT : (eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y))).toReal ≤
      (K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖T‖ := by
    rw [strG_norm_lin, hn1, hn2, mul_add]
    exact hR
  calc ‖strPairVal c mZ ρb γ ν ε Φ T‖
      ≤ K0 * (eLpNorm (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y))).toReal := hval
    _ ≤ K0 * ((K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖T‖) :=
        mul_le_mul_of_nonneg_left hT hK0
    _ = (K0 * (K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal) * ‖T‖ := by ring
