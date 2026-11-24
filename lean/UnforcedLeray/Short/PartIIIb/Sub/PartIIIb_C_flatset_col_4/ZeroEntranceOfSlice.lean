import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

theorem zeroEntranceOfSlice : ZeroEntranceOfSlice := by
  unfold ZeroEntranceOfSlice
  intro c b G n C hc hb hG hK hn
  unfold KcSliceBound at hK
  obtain ⟨K, hK⟩ := hK
  have hbm : Measurable b := measurable_pi_lambda _ hb
  have hvc : Continuous (fun a : Fin 2 → ℂ => vnorm2 a) := by
    unfold vnorm2
    fun_prop
  have hvn : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) :=
    hvc.measurable.comp hbm
  have hF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hvn.pow_const 2)
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hIF : Measurable ((Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
      fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) := hF.indicator hS
  have hq : qCell c = B0579.cell c := by
    simp only [qCell, B0579.cell, neg_div]
  have step1 : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))))
      = ∫⁻ p, (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) p ∂(ageμ c (-3 / 2)) :=
    (lintegral_indicator hS _).symm
  rw [step1, lintegral_ageμ hc (-3 / 2) hIF, hq]
  -- Tonelli on the product of restricted measures
  have hΦm : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) *
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
        (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) p) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const _))).mul hIF
  have hsplit : ∀ f : ℝ × (ℝ × ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, f p
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in B0579.cell c, f (s, x) := by
    intro f hf
    have e : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)
        = (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) :=
      (Measure.prod_restrict _ _).symm
    rw [e, lintegral_prod _ hf.aemeasurable]
  rw [hsplit _ hΦm]
  -- pointwise bound in the age variable
  have hbound : ∀ s ∈ Ioi (0 : ℝ),
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (c⁻¹ * (s, x).1 ^ (-3 / 2 : ℝ)) *
        (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) (s, x)
      ≤ (Ioo (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (c⁻¹ * (|K| * C ^ 2))) s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases h1 : s < 1
    · have hmem : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, h1⟩
      rw [Set.indicator_of_mem hmem]
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hin : ∫⁻ x in B0579.cell c,
          (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
            (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) (s, x)
          ≤ ENNReal.ofReal (|K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2)) := by
        have hpt : ∀ x : ℝ × ℝ, (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
            (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) (s, x)
            ≤ ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) := by
          intro x
          have hx : (s, x) ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ)) :=
            Set.mk_mem_prod hmem (Set.mem_univ x)
          rw [Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))
        have hn2 : n s ^ 2 ≤ C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2 := by
          have h := hn s ⟨hs0, h1.le⟩
          nlinarith [sq_abs (n s), abs_nonneg (n s)]
        have hKb : K * n s ^ 2 ≤ |K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2) :=
          calc K * n s ^ 2 ≤ |K| * n s ^ 2 :=
                mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
            _ ≤ |K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2) :=
                mul_le_mul_of_nonneg_left hn2 (abs_nonneg K)
        calc _ ≤ ∫⁻ x in B0579.cell c,
              ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) :=
                lintegral_mono hpt
          _ ≤ ENNReal.ofReal (K * n s ^ 2) := hK s hs0
          _ ≤ ENNReal.ofReal (|K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2)) :=
                ENNReal.ofReal_le_ofReal hKb
      have hX : s ^ (-3 / 2 : ℝ) * (s ^ (5 / 2 : ℝ)) ^ 2 ≤ 1 := by
        have h1' : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ (5 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
          norm_num
        rw [h1', ← Real.rpow_add hs0]
        exact Real.rpow_le_one hs0.le h1.le (by norm_num)
      have hw : 0 ≤ c⁻¹ * s ^ (-3 / 2 : ℝ) :=
        mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs0.le _)
      have hK0 : 0 ≤ c⁻¹ * (|K| * C ^ 2) :=
        mul_nonneg (inv_nonneg.2 hc.le) (mul_nonneg (abs_nonneg K) (sq_nonneg C))
      calc _ ≤ ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) *
              ENNReal.ofReal (|K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2)) := by
              gcongr
        _ = ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ) *
              (|K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2))) :=
              (ENNReal.ofReal_mul hw).symm
        _ ≤ ENNReal.ofReal (c⁻¹ * (|K| * C ^ 2)) := by
              apply ENNReal.ofReal_le_ofReal
              have e2 : c⁻¹ * s ^ (-3 / 2 : ℝ) * (|K| * (C ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2))
                  = (c⁻¹ * (|K| * C ^ 2)) * (s ^ (-3 / 2 : ℝ) * (s ^ (5 / 2 : ℝ)) ^ 2) := by
                ring
              rw [e2]
              calc (c⁻¹ * (|K| * C ^ 2)) * (s ^ (-3 / 2 : ℝ) * (s ^ (5 / 2 : ℝ)) ^ 2)
                  ≤ (c⁻¹ * (|K| * C ^ 2)) * 1 := mul_le_mul_of_nonneg_left hX hK0
                _ = c⁻¹ * (|K| * C ^ 2) := mul_one _
    · have hz : ∀ x : ℝ × ℝ, (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2)) (s, x) = 0 := by
        intro x
        apply Set.indicator_of_notMem
        intro h
        exact h1 h.1.2
      rw [Set.indicator_of_notMem (fun h => h1 h.2)]
      simp only [hz, mul_zero, lintegral_zero, le_refl]
  calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal (c⁻¹ * (|K| * C ^ 2))) s :=
        setLIntegral_mono' measurableSet_Ioi hbound
    _ ≤ ∫⁻ s, (Ioo (0 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal (c⁻¹ * (|K| * C ^ 2))) s :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (c⁻¹ * (|K| * C ^ 2)) * volume (Ioo (0 : ℝ) 1) :=
        lintegral_indicator_const measurableSet_Ioo _
    _ < ⊤ := by
        rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
        exact ENNReal.ofReal_lt_top

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
