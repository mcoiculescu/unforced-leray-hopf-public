import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Tail of the regularised approximate identity (`RhoTail`)

Source `the November 2 reference manuscript` 1676.  On `cellC c ∩ {δ ≤ ‖y‖}` the
denominator `D = cosh(aη) - cos(aq)` is bounded below (`D ≥ (2a²/π²) δ²` when `|η| ≤ 1`, and
`D ≥ θ cosh(aη)` when `|η| ≥ 1`), so `0 ≤ ρ_ε ≤ ε · C · (cosh aη)⁻¹`, an integrable majorant on
the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `1 + x²/2 ≤ cosh x`. -/
lemma cosh_lower_bd (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h2 : Real.cosh x = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := by
    rw [← Real.cosh_two_mul]
    congr 1
    ring
  have h3 : Real.cosh (x / 2) ^ 2 = Real.sinh (x / 2) ^ 2 + 1 := Real.cosh_sq _
  have habs : |x / 2| ≤ |Real.sinh (x / 2)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.2 (abs_nonneg _)
  have hsq : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := sq_le_sq.2 habs
  nlinarith

lemma cosh_gt_one_bd (a : ℝ) (ha : 0 < a) : 1 < Real.cosh a := by
  have := cosh_lower_bd a
  have : 0 < a ^ 2 := by positivity
  linarith

/-- The denominator lower bound on the centred cell. -/
lemma den_lower_bd (c : ℝ) (hc : 0 < c) (y : ℝ × ℝ) (hy : |y.1| ≤ c / 2) :
    2 * cylFreq c ^ 2 / Real.pi ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ≤ cylDen c y := by
  unfold cylDen
  have ha : 0 < cylFreq c := by unfold cylFreq; positivity
  have hay : |cylFreq c * y.1| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos ha]
    have hpi : cylFreq c * (c / 2) = Real.pi := by
      unfold cylFreq
      field_simp
    nlinarith [abs_nonneg y.1]
  have h1 := cosh_lower_bd (cylFreq c * y.2)
  have h2 := Real.cos_le_one_sub_mul_cos_sq hay
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ2 : 2 / Real.pi ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have key : 2 * cylFreq c ^ 2 / Real.pi ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ≤
      (cylFreq c * y.2) ^ 2 / 2 + 2 / Real.pi ^ 2 * (cylFreq c * y.1) ^ 2 := by
    have e : (cylFreq c * y.2) ^ 2 / 2 + 2 / Real.pi ^ 2 * (cylFreq c * y.1) ^ 2 -
        2 * cylFreq c ^ 2 / Real.pi ^ 2 * (y.1 ^ 2 + y.2 ^ 2) =
        (cylFreq c * y.2) ^ 2 * (1 / 2 - 2 / Real.pi ^ 2) := by ring
    have := mul_nonneg (sq_nonneg (cylFreq c * y.2)) (sub_nonneg.2 hπ2)
    linarith
  linarith

/-- The majorant constant `A'` on the tail. -/
def rhoConst (c δ : ℝ) : ℝ :=
  2 / (1 - (Real.cosh (cylFreq c))⁻¹) ^ 2 +
    2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 *
      Real.cosh (cylFreq c)

/-- Pointwise bound of `ρ_ε` on the tail. -/
lemma rho_pointwise (c δ ε : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hε : 0 < ε) (y : ℝ × ℝ)
    (hy : y ∈ cellC c) (hyδ : δ ≤ ‖y‖) :
    cylRho c ε y ≤ ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ) *
      (Real.cosh (cylFreq c * y.2))⁻¹ := by
  have ha : 0 < cylFreq c := by unfold cylFreq; positivity
  simp only [cellC, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true] at hy
  have hy1 : |y.1| ≤ c / 2 := abs_le.2 ⟨by linarith [hy.1], hy.2⟩
  have hD := den_lower_bd c hc y hy1
  have hH1 := Real.one_le_cosh (cylFreq c * y.2)
  have hC1 := Real.cos_le_one (cylFreq c * y.1)
  have hθ0 := cosh_gt_one_bd (cylFreq c) ha
  have hcpos : 0 < Real.cosh (cylFreq c) := Real.cosh_pos _
  have hθpos : 0 < 1 - (Real.cosh (cylFreq c))⁻¹ := by
    have : (Real.cosh (cylFreq c))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      exact hθ0
    linarith
  -- δ ≤ ‖y‖ gives δ² ≤ r²
  have hr : δ ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hyδ
    rcases le_max_iff.1 hyδ with h | h
    · nlinarith [sq_abs y.1, abs_nonneg y.1, sq_nonneg y.2]
    · nlinarith [sq_abs y.2, abs_nonneg y.2, sq_nonneg y.1]
  have hκpos : 0 < 2 * cylFreq c ^ 2 / Real.pi ^ 2 := by positivity
  have hDδ : 2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2 ≤ cylDen c y := by
    have := mul_le_mul_of_nonneg_left hr hκpos.le
    linarith
  have hHpos : 0 < Real.cosh (cylFreq c * y.2) := Real.cosh_pos _
  have hX : (Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) /
      (cylDen c y + ε) ^ 2 ≤ rhoConst c δ / Real.cosh (cylFreq c * y.2) := by
    unfold rhoConst
    rcases le_or_gt 1 |y.2| with h1 | h1
    · have hHa : Real.cosh (cylFreq c) ≤ Real.cosh (cylFreq c * y.2) := by
        rw [Real.cosh_le_cosh, abs_mul, abs_of_pos ha]
        nlinarith
      have hinvH : 1 ≤ (Real.cosh (cylFreq c))⁻¹ * Real.cosh (cylFreq c * y.2) := by
        have := mul_le_mul_of_nonneg_left hHa (inv_nonneg.2 hcpos.le)
        rwa [inv_mul_cancel₀ hcpos.ne'] at this
      have hθH : (1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2) ≤ cylDen c y := by
        unfold cylDen
        nlinarith
      have hθHpos : 0 < (1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2) :=
        mul_pos hθpos hHpos
      have hsq1 : ((1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2)) ^ 2 ≤
          (cylDen c y + ε) ^ 2 :=
        pow_le_pow_left₀ hθHpos.le (by linarith) 2
      have hmain : (Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) /
          (cylDen c y + ε) ^ 2 ≤
          2 * Real.cosh (cylFreq c * y.2) /
            ((1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2)) ^ 2 := by
        have hDε : 0 < cylDen c y + ε := by linarith
        rw [div_le_div_iff₀ (pow_pos hDε 2) (pow_pos hθHpos 2)]
        calc (Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) *
              ((1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2)) ^ 2
            ≤ (2 * Real.cosh (cylFreq c * y.2)) *
              ((1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2)) ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
          _ ≤ (2 * Real.cosh (cylFreq c * y.2)) * (cylDen c y + ε) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq1 (by positivity)
      have hsimp : 2 * Real.cosh (cylFreq c * y.2) /
          ((1 - (Real.cosh (cylFreq c))⁻¹) * Real.cosh (cylFreq c * y.2)) ^ 2 =
          (2 / (1 - (Real.cosh (cylFreq c))⁻¹) ^ 2) / Real.cosh (cylFreq c * y.2) := by
        field_simp
      have hnn : 0 ≤ 2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 *
          Real.cosh (cylFreq c) := by positivity
      have hfirst : 0 ≤ 2 / (1 - (Real.cosh (cylFreq c))⁻¹) ^ 2 := by positivity
      rw [hsimp] at hmain
      refine hmain.trans ?_
      exact div_le_div_of_nonneg_right (by linarith) hHpos.le
    · have hHa : Real.cosh (cylFreq c * y.2) ≤ Real.cosh (cylFreq c) := by
        rw [Real.cosh_le_cosh, abs_mul, abs_of_pos ha]
        nlinarith [abs_nonneg y.2]
      have hBpos : 0 ≤ 2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 := by
        positivity
      have hdenle : 2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2 ≤ cylDen c y + ε := by
        linarith
      have hsq2 : (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 ≤ (cylDen c y + ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdenle 2
      have hM : Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1) ≤
          2 * Real.cosh (cylFreq c) := by linarith
      have hB : (Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) /
          (cylDen c y + ε) ^ 2 ≤
          2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 :=
        div_le_div₀ (by positivity) hM (by positivity) hsq2
      have hfirst : 0 ≤ 2 / (1 - (Real.cosh (cylFreq c))⁻¹) ^ 2 := by positivity
      have hXB : 2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 ≤
          (2 / (1 - (Real.cosh (cylFreq c))⁻¹) ^ 2 +
            2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 *
              Real.cosh (cylFreq c)) / Real.cosh (cylFreq c * y.2) := by
        rw [le_div_iff₀ hHpos]
        nlinarith [mul_le_mul_of_nonneg_left hHa hBpos]
      exact hB.trans hXB
  calc cylRho c ε y
      = (cylFreq c ^ 2 * ε / (4 * Real.pi)) *
          ((Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) /
            (cylDen c y + ε) ^ 2) := by
        unfold cylRho
        ring
    _ ≤ (cylFreq c ^ 2 * ε / (4 * Real.pi)) *
          (rhoConst c δ / Real.cosh (cylFreq c * y.2)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ) *
          (Real.cosh (cylFreq c * y.2))⁻¹ := by
        ring

/-- `(cosh (a η))⁻¹` is integrable on `ℝ` for `a > 0`. -/
lemma inv_cosh_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun η : ℝ => (Real.cosh (a * η))⁻¹) := by
  have hlam : 0 < min 1 (a ^ 2 / 2) := lt_min one_pos (by positivity)
  have hbd : ∀ η : ℝ, (Real.cosh (a * η))⁻¹ ≤ (min 1 (a ^ 2 / 2))⁻¹ * (1 + η ^ 2)⁻¹ := by
    intro η
    have h1 := cosh_lower_bd (a * η)
    have hm1 : min 1 (a ^ 2 / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (a ^ 2 / 2) ≤ a ^ 2 / 2 := min_le_right _ _
    have h2 : min 1 (a ^ 2 / 2) * (1 + η ^ 2) ≤ Real.cosh (a * η) := by
      nlinarith [mul_le_mul_of_nonneg_right hm2 (sq_nonneg η)]
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hlam (by positivity)) h2
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (min 1 (a ^ 2 / 2))⁻¹)
    ?_ (ae_of_all _ (fun η => ?_))
  · exact (Measurable.inv (Real.measurable_cosh.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.cosh_pos _).le)]
    exact hbd η

/-- The `η`-majorant lifted to the centred cell. -/
lemma integrableOn_snd_cell (c : ℝ) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun y : ℝ × ℝ => g y.2) (cellC c) := by
  unfold cellC
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (-(c / 2)) (c / 2))) :=
    ⟨by simp⟩
  exact hg.comp_snd _

lemma cylRho_nonneg (c ε : ℝ) (hε : 0 < ε) (y : ℝ × ℝ) : 0 ≤ cylRho c ε y := by
  unfold cylRho
  have hsum : 0 ≤ Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1) := by
    linarith [Real.one_le_cosh (cylFreq c * y.2), Real.neg_one_le_cos (cylFreq c * y.1)]
  have hden : 0 ≤ cylDen c y + ε := by
    have := Real.one_le_cosh (cylFreq c * y.2)
    have := Real.cos_le_one (cylFreq c * y.1)
    unfold cylDen
    linarith
  exact div_nonneg (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hε.le)
    (by positivity)) hsum) (sq_nonneg _)

/-- **Tail of `ρ_ε`**: `∫_{cell ∩ {δ ≤ ‖y‖}} ρ_ε ≤ C ε`. -/
theorem rhoTail : RhoTail := by
  intro c δ hc hδ
  have ha : 0 < cylFreq c := by unfold cylFreq; positivity
  have hgI : IntegrableOn (fun y : ℝ × ℝ => (Real.cosh (cylFreq c * y.2))⁻¹) (cellC c) :=
    integrableOn_snd_cell c (fun η => (Real.cosh (cylFreq c * η))⁻¹) (inv_cosh_integrable _ ha)
  refine ⟨cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ *
    ∫ y in cellC c, (Real.cosh (cylFreq c * y.2))⁻¹, fun ε hε => ?_⟩
  have hSmeas : MeasurableSet (cellC c ∩ {y : ℝ × ℝ | δ ≤ ‖y‖}) := by
    apply MeasurableSet.inter
    · unfold cellC
      exact measurableSet_Ioc.prod MeasurableSet.univ
    · exact measurableSet_le measurable_const measurable_norm
  have h1 : ∫ y in cellC c ∩ {y : ℝ × ℝ | δ ≤ ‖y‖}, cylRho c ε y ≤
      ∫ y in cellC c ∩ {y : ℝ × ℝ | δ ≤ ‖y‖},
        (ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ)) * (Real.cosh (cylFreq c * y.2))⁻¹ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun y => cylRho_nonneg c ε hε y)
    · exact (hgI.mono_set Set.inter_subset_left).const_mul _
    · rw [EventuallyLE, ae_restrict_iff' hSmeas]
      exact ae_of_all _ (fun y hy => rho_pointwise c δ ε hc hδ hε y hy.1 hy.2)
  have h2 : ∫ y in cellC c ∩ {y : ℝ × ℝ | δ ≤ ‖y‖},
        (ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ)) * (Real.cosh (cylFreq c * y.2))⁻¹ ≤
      ∫ y in cellC c,
        (ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ)) * (Real.cosh (cylFreq c * y.2))⁻¹ := by
    apply setIntegral_mono_set (hgI.const_mul _)
    · exact ae_of_all _ (fun y => by
        have : 0 < Real.cosh (cylFreq c * y.2) := Real.cosh_pos _
        have hK : 0 ≤ cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ := by
          unfold rhoConst
          have := cosh_gt_one_bd (cylFreq c) ha
          have hθ : 0 < 1 - (Real.cosh (cylFreq c))⁻¹ := by
            have : (Real.cosh (cylFreq c))⁻¹ < 1 := by
              rw [inv_lt_one_iff₀]
              right
              exact this
            linarith
          have : 0 < Real.cosh (cylFreq c) := Real.cosh_pos _
          have : 0 ≤ 2 * Real.cosh (cylFreq c) / (2 * cylFreq c ^ 2 / Real.pi ^ 2 * δ ^ 2) ^ 2 *
              Real.cosh (cylFreq c) := by positivity
          positivity
        exact mul_nonneg (mul_nonneg hε.le hK) (inv_nonneg.2 this.le))
    · exact ae_of_all _ (fun y => fun hy => hy.1)
  have h3 : ∫ y in cellC c,
        (ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ)) * (Real.cosh (cylFreq c * y.2))⁻¹ =
      (ε * (cylFreq c ^ 2 / (4 * Real.pi) * rhoConst c δ)) *
        ∫ y in cellC c, (Real.cosh (cylFreq c * y.2))⁻¹ :=
    integral_const_mul _ _
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
