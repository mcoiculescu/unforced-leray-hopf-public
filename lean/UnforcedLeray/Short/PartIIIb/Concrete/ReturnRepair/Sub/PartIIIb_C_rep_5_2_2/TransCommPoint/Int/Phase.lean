import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Dil

/-!
# Periodic dilation sum for an arbitrary period (source 3838-3845)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∫_0^1 l^c G(τ + 2 log l) dl ≤ ½ (1 - e^{-κP})⁻¹ P ‖G‖` for `P`-periodic `G`, `c > -1`,
`κ = (c+1)/2`, every `P > 0` and every phase `τ`. -/
theorem tcd_dilSum {c P : ℝ} (hc : -1 < c) (hP : 0 < P) {G : ℝ → ℝ≥0∞} (hGm : Measurable G)
    (hper : ∀ s, G (s + P) = G s) (τ : ℝ) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l) ≤
      ENNReal.ofReal (1 / 2) * ((1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹ *
        (ENNReal.ofReal P * IIIa.ltauAt P G)) := by
  have hκ : 0 < (c + 1) / 2 := by linarith
  have hpt : ∀ l ∈ Ioo (0:ℝ) 1,
      ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have habs : |(-2 * l⁻¹)| = 2 * l⁻¹ := by
      rw [show (-2 * l⁻¹) = -(2 * l⁻¹) by ring, abs_neg,
        abs_of_pos (mul_pos two_pos (inv_pos.mpr hl0))]
    have e1 : Real.exp (-((c + 1) / 2) * (-2 * Real.log l)) = l ^ c * l := by
      rw [← Real.rpow_add_one hl0.ne' c, Real.rpow_def_of_pos hl0]
      congr 1
      ring
    have e2 : τ - (-2 * Real.log l) = τ + 2 * Real.log l := by ring
    have hL : ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
    have hR : ENNReal.ofReal (2 * l⁻¹) * (ENNReal.ofReal (l ^ c * l) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.mpr hl0.le))]
      have hal : 2 * l⁻¹ * (l ^ c * l) = 2 * l ^ c := by
        field_simp
      rw [hal]
    rw [habs, e1, e2, hL, hR]
  have hJ1 : ∫⁻ l in Ioo (0:ℝ) 1,
        ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
      = ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) :=
    setLIntegral_congr_fun measurableSet_Ioo fun l hl => hpt l hl
  have hf' : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun l : ℝ => -2 * Real.log l) (-2 * x⁻¹) (Ioo (0:ℝ) 1) x := by
    intro x hx
    exact ((Real.hasDerivAt_log hx.1.ne').const_mul (-2)).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => -2 * Real.log l) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    have h1 : Real.log a = Real.log b := by
      have hab' : -2 * Real.log a = -2 * Real.log b := hab
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hb.1) h1
  have hJ2 := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hf' hinj
    (fun x => ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x))
  have hsub : (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1 ⊆ Ioi 0 := by
    rintro _ ⟨l, hl, rfl⟩
    have := Real.log_neg hl.1 hl.2
    show 0 < -2 * Real.log l
    linarith
  have hmono : ∫⁻ x in (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1,
        ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x)
      ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) :=
    lintegral_mono_set hsub
  have hL : ENNReal.ofReal 2 * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      ≤ (1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹ *
        (ENNReal.ofReal P * IIIa.ltauAt P G) := by
    calc ENNReal.ofReal 2 * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
        = ∫⁻ l in Ioo (0:ℝ) 1,
            ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) := hJ1
      _ = ∫⁻ x in (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1,
            ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) := hJ2.symm
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) := hmono
      _ ≤ (1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹ * (∫⁻ u in Ioc 0 P, G u) :=
          pds_sum hκ hP hGm hper τ
      _ ≤ (1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹
            * (ENNReal.ofReal P * IIIa.ltauAt P G) :=
          mul_le_mul' le_rfl (pds_cs hP hGm)
  have hhalf : ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
    norm_num
  calc ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal 2
          * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) := by
        rw [← mul_assoc, hhalf, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hL

end UnforcedLeray.Short.PartIIIb.Concrete

end
