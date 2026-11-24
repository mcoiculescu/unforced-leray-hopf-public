import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerAsym
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRhoTail
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# `CylKerWindow` (source 1676: `K = ∇Γ` is `O(1/|y|)` at `0`, bounded at infinity)

On the strip `|q| ≤ c/2`: `|K_i(y)| ≤ C₀ + C₁ ‖y‖⁻¹`.  For `|η| ≥ 1` this is `CylKerAsym`; for
`|η| ≤ 1` it follows from `D ≥ (2a²/π²) ‖y‖²` and `|sin|, |sinh| ≤ a ‖y‖ e^a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

lemma cylKW_sinh_le (t : ℝ) (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.exp t := by
  have h1 := Real.add_one_le_exp (-(2 * t))
  have h2 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos t
  have h5 := Real.exp_pos (-t)
  rw [Real.sinh_eq]
  nlinarith [mul_pos h4 h5]

lemma cylKW_abs_sinh_le (x : ℝ) (b : ℝ) (hx : |x| ≤ b) : |Real.sinh x| ≤ |x| * Real.exp b := by
  rw [Real.abs_sinh]
  calc Real.sinh |x| ≤ |x| * Real.exp |x| := cylKW_sinh_le _ (abs_nonneg _)
    _ ≤ |x| * Real.exp b := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hx) (abs_nonneg _)

lemma cylKW_pointwise (c : ℝ) (hc : 0 < c) : ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
    ∀ (i : Fin 2) (y : ℝ × ℝ), |y.1| ≤ c / 2 → |cylKer c i y| ≤ C₀ + C₁ * ‖y‖⁻¹ := by
  have ha : 0 < cylFreq c := by unfold cylFreq; positivity
  obtain ⟨Ca, hCa⟩ := cylKerAsym c hc
  have hpos4 : 0 < cylFreq c / (4 * Real.pi) := div_pos ha (by positivity)
  have hpi := Real.pi_pos
  set a := cylFreq c with ha_def
  set m : ℝ := 2 * a ^ 2 / Real.pi ^ 2 with hm_def
  have hm : 0 < m := by positivity
  have hea : 1 ≤ Real.exp a := Real.one_le_exp ha.le
  refine ⟨max Ca 0 + a / (4 * Real.pi), a / (4 * Real.pi) * (a * Real.exp a) / m, by positivity,
    by positivity, fun i y hy1 => ?_⟩
  by_cases hA : 1 ≤ |y.2|
  · have hex : Real.exp (-(a * |y.2|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg y.2]
    have hex0 := Real.exp_pos (-(a * |y.2|))
    obtain ⟨h0, h1⟩ := hCa y hA
    have hC : Ca * Real.exp (-(a * |y.2|)) ≤ max Ca 0 := by
      calc Ca * Real.exp (-(a * |y.2|)) ≤ max Ca 0 * Real.exp (-(a * |y.2|)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hex0.le
        _ ≤ max Ca 0 * 1 := mul_le_mul_of_nonneg_left hex (le_max_right _ _)
        _ = max Ca 0 := by ring
    have hnn : 0 ≤ a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ := by positivity
    have hsg : |Real.sign y.2| ≤ 1 := by
      rcases lt_trichotomy y.2 0 with h | h | h
      · simp [Real.sign_of_neg h]
      · simp [h]
      · simp [Real.sign_of_pos h]
    fin_cases i
    · simp only [Fin.zero_eta] at *
      linarith [le_trans h0 hC, le_max_right Ca 0]
    · simp only [Fin.mk_one] at *
      have e1 : |cylKer c 1 y| ≤ |cylKer c 1 y - a / (4 * Real.pi) * Real.sign y.2| +
          |a / (4 * Real.pi) * Real.sign y.2| := by
        have := abs_add_le (cylKer c 1 y - a / (4 * Real.pi) * Real.sign y.2)
          (a / (4 * Real.pi) * Real.sign y.2)
        simpa using this
      have e2 : |a / (4 * Real.pi) * Real.sign y.2| ≤ a / (4 * Real.pi) := by
        rw [abs_mul, abs_of_pos hpos4]
        calc a / (4 * Real.pi) * |Real.sign y.2| ≤ a / (4 * Real.pi) * 1 :=
              mul_le_mul_of_nonneg_left hsg hpos4.le
          _ = _ := by ring
      linarith [le_trans h1 hC, le_max_right Ca 0]
  · push_neg at hA
    by_cases hn : ‖y‖ = 0
    · have : y = 0 := norm_eq_zero.1 hn
      subst this
      fin_cases i <;> simp [cylKer, cylNum]
      <;> positivity
    · have hnpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      have hy1n : |y.1| ≤ ‖y‖ := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
      have hy2n : |y.2| ≤ ‖y‖ := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
      have hsq : ‖y‖ ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
        rcases max_choice |y.1| |y.2| with h | h <;> rw [h] <;> simp [sq_abs] <;> nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      have hD := den_lower_bd c hc y hy1
      have hDn : m * ‖y‖ ^ 2 ≤ cylDen c y := by
        have : m * ‖y‖ ^ 2 ≤ m * (y.1 ^ 2 + y.2 ^ 2) := mul_le_mul_of_nonneg_left hsq hm.le
        have e : 2 * a ^ 2 / Real.pi ^ 2 * (y.1 ^ 2 + y.2 ^ 2) = m * (y.1 ^ 2 + y.2 ^ 2) := rfl
        linarith
      have hDpos : 0 < cylDen c y := lt_of_lt_of_le (by positivity) hDn
      have hnum : |cylNum c i y| ≤ a * Real.exp a * ‖y‖ := by
        fin_cases i
        · simp only [cylNum, Fin.zero_eta, Matrix.cons_val_zero]
          calc |Real.sin (a * y.1)| ≤ |a * y.1| := Real.abs_sin_le_abs
            _ = a * |y.1| := by rw [abs_mul, abs_of_pos ha]
            _ ≤ a * ‖y‖ := mul_le_mul_of_nonneg_left hy1n ha.le
            _ ≤ a * Real.exp a * ‖y‖ := by nlinarith [norm_nonneg y, mul_nonneg ha.le (norm_nonneg y)]
        · simp only [cylNum, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          have hb : |a * y.2| ≤ a := by
            rw [abs_mul, abs_of_pos ha]; nlinarith
          calc |Real.sinh (a * y.2)| ≤ |a * y.2| * Real.exp a := cylKW_abs_sinh_le _ _ hb
            _ = a * |y.2| * Real.exp a := by rw [abs_mul, abs_of_pos ha]
            _ ≤ a * ‖y‖ * Real.exp a := by gcongr
            _ = a * Real.exp a * ‖y‖ := by ring
      have hK : |cylKer c i y| = a / (4 * Real.pi) * |cylNum c i y| / cylDen c y := by
        unfold cylKer
        rw [abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
      rw [hK, div_le_iff₀ hDpos]
      have hnn : 0 ≤ max Ca 0 + a / (4 * Real.pi) := by positivity
      have key : a / (4 * Real.pi) * |cylNum c i y| ≤
          a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ * (m * ‖y‖ ^ 2) := by
        have : a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ * (m * ‖y‖ ^ 2) =
            a / (4 * Real.pi) * (a * Real.exp a * ‖y‖) := by
          field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_left hnum hpos4.le |>.trans (by rw [mul_assoc])
      have hC1 : 0 ≤ a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ := by positivity
      calc a / (4 * Real.pi) * |cylNum c i y|
          ≤ a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ * (m * ‖y‖ ^ 2) := key
        _ ≤ a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹ * cylDen c y :=
            mul_le_mul_of_nonneg_left hDn hC1
        _ ≤ (max Ca 0 + a / (4 * Real.pi) + a / (4 * Real.pi) * (a * Real.exp a) / m * ‖y‖⁻¹) *
            cylDen c y := by
            apply mul_le_mul_of_nonneg_right _ hDpos.le
            linarith [le_max_right Ca 0]


lemma cylKW_meas (c : ℝ) (i : Fin 2) : Measurable (cylKer c i) := by
  unfold cylKer
  have h1 : Measurable (cylNum c i) := by
    fin_cases i
    · have : cylNum c 0 = fun y => Real.sin (cylFreq c * y.1) := by funext y; simp [cylNum]
      show Measurable (cylNum c 0)
      rw [this]; fun_prop
    · have : cylNum c 1 = fun y => Real.sinh (cylFreq c * y.2) := by funext y; simp [cylNum]
      show Measurable (cylNum c 1)
      rw [this]; fun_prop
  have h2 : Measurable (cylDen c) := by unfold cylDen; fun_prop
  exact (h1.const_mul _).div h2

lemma cylKW_inv_int : IntegrableOn (fun y : ℝ × ℝ => ‖y‖⁻¹) (Metric.ball 0 1) := by
  have hd : (1 : ℝ) < (Module.finrank ℝ (ℝ × ℝ) : ℝ) := by
    simp [Module.finrank_prod]
  have := integrableOn_ball_of_norm_le_rpow (μ := volume) (E := ℝ × ℝ) (F := ℝ)
    (f := fun y : ℝ × ℝ => ‖y‖⁻¹) (C := 1) (α := 1) (r := 1)
    (by simp [Module.finrank_prod]) hd
    (Filter.Eventually.of_forall fun x => by
      simp [Real.rpow_neg_one]) (by fun_prop)
  exact this

theorem cylKerWindow : CylKerWindow := by
  intro c hc L
  obtain ⟨C₀, C₁, h0, h1, hpt⟩ := cylKW_pointwise c hc
  set J : ℝ := ∫ y in Metric.ball (0 : ℝ × ℝ) 1, ‖y‖⁻¹ with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg Metric.isOpen_ball.measurableSet (fun y _ => by positivity)
  refine ⟨(C₀ + C₁) * (c * (2 * |L|)) + C₁ * J, fun i t => ?_⟩
  set W : Set (ℝ × ℝ) := Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L) with hW
  have hWm : MeasurableSet W := measurableSet_Ioc.prod measurableSet_Icc
  have hvol : volume W = ENNReal.ofReal c * ENNReal.ofReal (2 * L) := by
    rw [hW, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
    congr 2 <;> ring_nf
  have hvolfin : volume W < ⊤ := by rw [hvol]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hvr : volume.real W ≤ c * (2 * |L|) := by
    rw [Measure.real, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    apply mul_le_mul_of_nonneg_left _ hc.le
    calc (ENNReal.ofReal (2 * L)).toReal = max (2 * L) 0 := ENNReal.toReal_ofReal' 
      _ ≤ 2 * |L| := max_le (by nlinarith [le_abs_self L]) (by positivity)
  -- majorant
  set G : ℝ × ℝ → ℝ := fun y => (C₀ + C₁) +
    C₁ * (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun y => ‖y‖⁻¹) y with hG
  have hbound : ∀ y ∈ W, |cylKer c i y| ≤ G y := by
    intro y hy
    have hy1 : |y.1| ≤ c / 2 := abs_le.2 ⟨by linarith [hy.1.1], hy.1.2⟩
    refine (hpt i y hy1).trans ?_
    by_cases hb : y ∈ Metric.ball (0 : ℝ × ℝ) 1
    · simp only [hG, Set.indicator_of_mem hb]; nlinarith
    · simp only [hG, Set.indicator_of_notMem hb]
      have : 1 ≤ ‖y‖ := by simpa using hb
      have : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      nlinarith
  have hind : Integrable (fun y : ℝ × ℝ => (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun y => ‖y‖⁻¹) y) := by
    rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    exact cylKW_inv_int
  have hconst : IntegrableOn (fun _ : ℝ × ℝ => C₀ + C₁) W := integrableOn_const hvolfin.ne
  have hGint : IntegrableOn G W := by
    apply Integrable.add
    · exact hconst
    · exact (hind.const_mul C₁).integrableOn
  have hKint : IntegrableOn (cylKer c i) W := by
    refine Integrable.mono' hGint (cylKW_meas c i).aestronglyMeasurable ?_
    have : ∀ᵐ y ∂volume.restrict W, ‖cylKer c i y‖ ≤ G y :=
      (ae_restrict_iff' hWm).2 (Filter.Eventually.of_forall fun y hy => by
        simpa using hbound y hy)
    exact this
  refine ⟨hKint, ?_⟩
  have hnorm : ∫ y in W, |cylKer c i y| ≤ ∫ y in W, G y := by
    refine setIntegral_mono_on hKint.abs hGint hWm hbound
  refine hnorm.trans ?_
  have hsplit : ∫ y in W, G y = volume.real W • (C₀ + C₁) +
      C₁ * ∫ y in W, (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun y => ‖y‖⁻¹) y := by
    rw [hG, integral_add hconst (hind.const_mul C₁).integrableOn,
      setIntegral_const, integral_const_mul]
  rw [hsplit]
  have hI : ∫ y in W, (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun y => ‖y‖⁻¹) y ≤ J := by
    calc _ ≤ ∫ y, (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun y => ‖y‖⁻¹) y :=
          setIntegral_le_integral hind (Filter.Eventually.of_forall fun y => by
            apply Set.indicator_nonneg; intro z _; positivity)
      _ = J := integral_indicator Metric.isOpen_ball.measurableSet
  have : volume.real W • (C₀ + C₁) ≤ (C₀ + C₁) * (c * (2 * |L|)) := by
    rw [smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hvr (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hI h1]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
