import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_3

/-!
# `SFCEnergyV`: the velocity half of the strip energy
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4`, item `sfcEnergyV`)

Source `the November 2 reference manuscript` 1684-1689.  The representative `b`
equals `velC (R₀ g)` `ageμ(-3/2)`-a.e., and `R₀ g ∈ Hsp c`, so the weighted `L²` integral
`∫ |b|² ds ds` is finite.  On a strip `Icc s₁ s₂ ×ˢ cell` with `0 < s₁ < s₂` the weight
`s^(-3/2)` is bounded below by `s₂^(-3/2) > 0`, so the unweighted strip integral is bounded by a
constant times the `ageμ`-integral over the strip.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- The cell of `B0579` is the cell of `Axi` (`Ico (-(c/2)) (c/2)` versus `Ico (-c/2) (c/2)`). -/
theorem sfcV_cell_eq (c : ℝ) : B0579.cell c = qCell c := by
  unfold B0579.cell qCell
  rw [neg_div]

/-- Density comparison on a strip: on `Icc s₁ s₂ ×ˢ cell` (with `0 < s₁`), the Lebesgue integral is
at most `(ofReal (c⁻¹ s₂^a))⁻¹` times the `ageμ c a`-integral, for `a ≤ 0`. The constant
`M = ofReal (c⁻¹ s₂^a)` satisfies `M * ∫_S G dvol ≤ ∫_S G dageμ`. -/
theorem sfcV_density_le {c : ℝ} (hc : 0 < c) (a s₁ s₂ : ℝ) (ha : a ≤ 0) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {G : Chart → ℝ≥0∞} (hG : Measurable G) :
    ENNReal.ofReal (c⁻¹ * s₂ ^ a) * ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, G p
      ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, G p ∂(ageμ c a) := by
  set S : Set Chart := Icc s₁ s₂ ×ˢ B0579.cell c with hSdef
  set T : Set Chart := Ioi (0 : ℝ) ×ˢ qCell c with hTdef
  set I : Chart → ℝ≥0∞ := S.indicator G with hIdef
  have hS_meas : MeasurableSet S :=
    measurableSet_Icc.prod ((measurableSet_Ico).prod MeasurableSet.univ)
  have hT_meas : MeasurableSet T := measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hI : Measurable I := hG.indicator hS_meas
  have hST : S ⊆ T := by
    rintro ⟨s, q⟩ ⟨hs, hq⟩
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le hs₁ hs.1
    · rw [sfcV_cell_eq] at hq
      exact hq
  have hw : Measurable fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ a) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul ((measurable_id.comp measurable_fst).pow_const a))
  -- pointwise comparison of the two densities on the strip
  have hpt : ∀ p : Chart, ENNReal.ofReal (c⁻¹ * s₂ ^ a) * I p ≤
      T.indicator (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ a) * I p) p := by
    intro p
    by_cases hp : p ∈ S
    · have hpT : p ∈ T := hST hp
      rw [indicator_of_mem hpT]
      have hI' : I p = G p := indicator_of_mem hp G
      rw [hI']
      have hp1 : 0 < p.1 := lt_of_lt_of_le hs₁ hp.1.1
      have hle : s₂ ^ a ≤ p.1 ^ a := Real.rpow_le_rpow_of_nonpos hp1 hp.1.2 ha
      have hM : ENNReal.ofReal (c⁻¹ * s₂ ^ a) ≤ ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hc.le))
      exact mul_le_mul_left hM (G p)
    · have hI0 : I p = 0 := indicator_of_notMem hp G
      rw [hI0, mul_zero]
      exact zero_le
  calc ENNReal.ofReal (c⁻¹ * s₂ ^ a) * ∫⁻ p in S, G p
      = ∫⁻ p, ENNReal.ofReal (c⁻¹ * s₂ ^ a) * I p := by
        rw [lintegral_const_mul _ hI, hIdef, lintegral_indicator hS_meas]
    _ ≤ ∫⁻ p, T.indicator (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ a) * I p) p :=
        lintegral_mono hpt
    _ = ∫⁻ p in T, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * I p :=
        lintegral_indicator hT_meas _
    _ = ∫⁻ p, I p ∂(ageμ c a) := by
        rw [lintegral_ageμ hc a hI, hTdef]
    _ = ∫⁻ p in S, G p ∂(ageμ c a) := lintegral_indicator hS_meas G

/-- **Velocity half** (source 1684-1689): `b =ᵐ velC (R₀ g) ∈ Hsp`, so the strip integral of
`|b|²` is finite. -/
theorem sfcEnergyV : SFCEnergyV := by
  intro c ν μ hc R0 g _hctx b hb hbe s₁ s₂ h1 h12
  set S : Set Chart := Icc s₁ s₂ ×ˢ B0579.cell c with hSdef
  set G : Chart → ℝ≥0∞ := fun p => ENNReal.ofReal (vnorm2 (b p) ^ 2) with hGdef
  have hG : Measurable G := by
    have : ∀ i, Measurable fun p : Chart => b p i := hb.1
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.pow_const ?_ 2
    unfold vnorm2
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (this i).norm.pow_const 2
  -- the two integrands agree `ageμ`-a.e., hence on the restricted measure
  have hae : (fun p => G p) =ᵐ[(ageμ c (-3 / 2)).restrict S]
      (fun p => ENNReal.ofReal (vnorm2 (NearInst.velC (R0 g) p) ^ 2)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hbe] with p hp
    simp only [hGdef]
    rw [hp]
  have hfin : ∫⁻ p in S, G p ∂(ageμ c (-3 / 2)) < ⊤ := by
    rw [lintegral_congr_ae hae]
    refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
    rw [lintegral_velC_hsp c (R0 g)]
    exact ENNReal.ofReal_lt_top
  have hdens := sfcV_density_le hc (-3 / 2) s₁ s₂ (by norm_num) h1 h12
    (G := G) (by exact hG)
  have hM : ENNReal.ofReal (c⁻¹ * s₂ ^ (-3 / 2 : ℝ)) ≠ 0 := by
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    exact mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos (lt_trans h1 h12) _)
  have hMX : ENNReal.ofReal (c⁻¹ * s₂ ^ (-3 / 2 : ℝ)) *
      ∫⁻ p in S, G p < ⊤ := lt_of_le_of_lt hdens hfin
  have hsv := ENNReal.lt_top_of_mul_ne_top_right hMX.ne hM
  exact hsv

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
