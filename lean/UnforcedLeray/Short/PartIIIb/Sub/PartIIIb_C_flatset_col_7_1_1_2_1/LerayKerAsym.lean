import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `CylKerAsym` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/leray/10`)

Source 1676 (asymptotics of `∇Γ`).  With `a = 2π/c`, `D = cosh(aη) - cos(aq)` and `|η| ≥ 1`:
`D ≥ κ e^{a|η|}` for `κ = (1 - (cosh a)⁻¹)/2 > 0`, so `1/D ≤ κ⁻¹ e^{-a|η|}`.  Then
`K₀ = (a/4π) sin(aq)/D` and, using `sinh(aη) - D = cos(aq) - e^{-aη}` (for `η > 0`) and
`sinh(aη) + D = e^{aη} - cos(aq)` (for `η < 0`), both `K₀` and `K₁ - (a/4π) sign η` are bounded by
`C e^{-a|η|}` with `C = (a/4π) · 2 · κ⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `κ = (1 - (cosh a)⁻¹)/2 > 0` for `a > 0`. -/
theorem cylKA_kappa_pos {a : ℝ} (ha : 0 < a) : 0 < (1 - (Real.cosh a)⁻¹) / 2 := by
  have hcosh_a : 1 < Real.cosh a := Real.one_lt_cosh.mpr ha.ne'
  have hu1 : (Real.cosh a)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by linarith)]
    exact hcosh_a
  linarith

/-- The gap estimate `D ≥ κ e^{a|η|}` for `|η| ≥ 1`. -/
theorem cylKA_cosh_gap {a : ℝ} (ha : 0 < a) (q η : ℝ) (hη : 1 ≤ |η|) :
    (1 - (Real.cosh a)⁻¹) / 2 * Real.exp (a * |η|) ≤ Real.cosh (a * η) - Real.cos (a * q) := by
  have hcosh_a : 1 < Real.cosh a := Real.one_lt_cosh.mpr ha.ne'
  have hcos : Real.cos (a * q) ≤ 1 := Real.cos_le_one _
  have hcosh_eq : Real.cosh (a * η) = Real.cosh (a * |η|) := by
    rw [← Real.cosh_abs (a * η), abs_mul, abs_of_pos ha]
  have ht_a : a ≤ a * |η| := le_mul_of_one_le_right ha.le hη
  have hcm : Real.cosh a ≤ Real.cosh (a * |η|) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_pos ha, abs_of_pos (by linarith)]
    exact ht_a
  have hexp : Real.exp (a * |η|) ≤ 2 * Real.cosh (a * |η|) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(a * |η|))]
  have hu : 1 ≤ (Real.cosh a)⁻¹ * Real.cosh (a * |η|) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
    linarith
  have hu1 : (Real.cosh a)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by linarith)]
    exact hcosh_a
  have hκ : 0 ≤ 1 - (Real.cosh a)⁻¹ := by linarith
  have hD1 : (1 - (Real.cosh a)⁻¹) * Real.cosh (a * |η|) ≤ Real.cosh (a * |η|) - 1 := by
    have h : (1 - (Real.cosh a)⁻¹) * Real.cosh (a * |η|) =
        Real.cosh (a * |η|) - (Real.cosh a)⁻¹ * Real.cosh (a * |η|) := by ring
    linarith
  have hD2 : (1 - (Real.cosh a)⁻¹) * (Real.exp (a * |η|) / 2) ≤
      (1 - (Real.cosh a)⁻¹) * Real.cosh (a * |η|) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ
  have hsplit : (1 - (Real.cosh a)⁻¹) / 2 * Real.exp (a * |η|) =
      (1 - (Real.cosh a)⁻¹) * (Real.exp (a * |η|) / 2) := by ring
  rw [hcosh_eq, hsplit]
  linarith

/-- `1/D ≤ κ⁻¹ e^{-a|η|}` for `|η| ≥ 1`. -/
theorem cylKA_inv_den {a : ℝ} (ha : 0 < a) (q η : ℝ) (hη : 1 ≤ |η|) :
    1 / (Real.cosh (a * η) - Real.cos (a * q)) ≤
      1 / ((1 - (Real.cosh a)⁻¹) / 2) * Real.exp (-(a * |η|)) := by
  have hg := cylKA_cosh_gap ha q η hη
  have hκ := cylKA_kappa_pos ha
  have hpos : 0 < (1 - (Real.cosh a)⁻¹) / 2 * Real.exp (a * |η|) :=
    mul_pos hκ (Real.exp_pos _)
  calc 1 / (Real.cosh (a * η) - Real.cos (a * q))
      ≤ 1 / ((1 - (Real.cosh a)⁻¹) / 2 * Real.exp (a * |η|)) :=
        one_div_le_one_div_of_le hpos hg
    _ = 1 / ((1 - (Real.cosh a)⁻¹) / 2) * Real.exp (-(a * |η|)) := by
        rw [Real.exp_neg]
        generalize (1 - (Real.cosh a)⁻¹) / 2 = k
        ring

/-- **Asymptotics of `K`** (source 1676). -/
theorem cylKerAsym : CylKerAsym := by
  intro c hc
  have ha : 0 < cylFreq c := by
    unfold cylFreq
    positivity
  have hκ := cylKA_kappa_pos ha
  have hpos4 : 0 < cylFreq c / (4 * Real.pi) := div_pos ha (by positivity)
  refine ⟨cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2)),
    fun y hy => ?_⟩
  have hK0 : cylKer c 0 y = cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) / cylDen c y := by
    simp [cylKer, cylNum]
  have hK1 : cylKer c 1 y = cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y := by
    simp [cylKer, cylNum]
  have hgap : (1 - (Real.cosh (cylFreq c))⁻¹) / 2 * Real.exp (cylFreq c * |y.2|) ≤ cylDen c y :=
    cylKA_cosh_gap ha y.1 y.2 hy
  have hDpos : 0 < cylDen c y := lt_of_lt_of_le (mul_pos hκ (Real.exp_pos _)) hgap
  have hinv : 1 / cylDen c y ≤
      1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) * Real.exp (-(cylFreq c * |y.2|)) :=
    cylKA_inv_den ha y.1 y.2 hy
  have hy0 : y.2 ≠ 0 := by
    rintro h
    rw [h, abs_zero] at hy
    norm_num at hy
  constructor
  · -- the `q`-component `K₀`
    rw [hK0, abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
    have hsin : |Real.sin (cylFreq c * y.1)| ≤ 1 := Real.abs_sin_le_one _
    have h1 : cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)| ≤ cylFreq c / (4 * Real.pi) := by
      calc cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)|
          ≤ cylFreq c / (4 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hsin hpos4.le
        _ = cylFreq c / (4 * Real.pi) := mul_one _
    have h2 := div_le_div_of_nonneg_right h1 hDpos.le
    have hE : 0 ≤ Real.exp (-(cylFreq c * |y.2|)) := (Real.exp_pos _).le
    have hXY : 0 ≤ cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
        Real.exp (-(cylFreq c * |y.2|))) :=
      mul_nonneg hpos4.le (mul_nonneg (div_nonneg zero_le_one hκ.le) hE)
    calc cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)| / cylDen c y
        ≤ cylFreq c / (4 * Real.pi) / cylDen c y := h2
      _ = cylFreq c / (4 * Real.pi) * (1 / cylDen c y) := by ring
      _ ≤ cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
            Real.exp (-(cylFreq c * |y.2|))) := mul_le_mul_of_nonneg_left hinv hpos4.le
      _ ≤ 2 * (cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
            Real.exp (-(cylFreq c * |y.2|)))) := by linarith
      _ = cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2)) *
            Real.exp (-(cylFreq c * |y.2|)) := by ring
  · -- the `η`-component `K₁ - (a/4π) sign η`
    rcases lt_or_gt_of_ne hy0 with hneg | hposy
    · -- `η < 0`: `sinh(aη) + D = e^{aη} - cos(aq)`
      have hx : cylFreq c * y.2 < 0 := mul_neg_of_pos_of_neg ha hneg
      have hs2 : Real.sinh (cylFreq c * y.2) = Real.exp (cylFreq c * y.2) - Real.cosh (cylFreq c * y.2) := by
        linarith [Real.cosh_add_sinh (cylFreq c * y.2)]
      have hDne : Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) ≠ 0 := hDpos.ne'
      have hkey : cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y -
          cylFreq c / (4 * Real.pi) * -1 =
          cylFreq c / (4 * Real.pi) * (Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)) /
            cylDen c y := by
        unfold cylDen
        rw [hs2]
        field_simp
        ring
      have hexp1 : Real.exp (cylFreq c * y.2) ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have hb : |Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)| ≤ 2 := by
        rw [abs_le]
        constructor
        · linarith [Real.cos_le_one (cylFreq c * y.1), Real.exp_pos (cylFreq c * y.2)]
        · linarith [Real.neg_one_le_cos (cylFreq c * y.1), hexp1]
      rw [hK1, Real.sign_of_neg hneg, hkey, abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
      have hXY : 0 ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
          Real.exp (-(cylFreq c * |y.2|))) := by
        apply mul_nonneg (mul_nonneg hpos4.le zero_le_two)
        exact mul_nonneg (div_nonneg zero_le_one hκ.le) (Real.exp_pos _).le
      calc cylFreq c / (4 * Real.pi) * |Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)| /
            cylDen c y
          ≤ cylFreq c / (4 * Real.pi) * 2 / cylDen c y :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hpos4.le) hDpos.le
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / cylDen c y) := by ring
        _ ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
              Real.exp (-(cylFreq c * |y.2|))) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg hpos4.le zero_le_two)
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2)) *
              Real.exp (-(cylFreq c * |y.2|)) := by ring
    · -- `η > 0`: `sinh(aη) - D = cos(aq) - e^{-aη}`
      have hx : 0 < cylFreq c * y.2 := mul_pos ha hposy
      have hs1 : Real.sinh (cylFreq c * y.2) = Real.cosh (cylFreq c * y.2) - Real.exp (-(cylFreq c * y.2)) := by
        linarith [Real.cosh_sub_sinh (cylFreq c * y.2)]
      have hDne : Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) ≠ 0 := hDpos.ne'
      have hkey : cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y -
          cylFreq c / (4 * Real.pi) * 1 =
          cylFreq c / (4 * Real.pi) * (Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))) /
            cylDen c y := by
        unfold cylDen
        rw [hs1]
        field_simp
        ring
      have hexp1 : Real.exp (-(cylFreq c * y.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hb : |Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))| ≤ 2 := by
        rw [abs_le]
        constructor
        · linarith [Real.neg_one_le_cos (cylFreq c * y.1), hexp1]
        · linarith [Real.cos_le_one (cylFreq c * y.1), Real.exp_pos (-(cylFreq c * y.2))]
      rw [hK1, Real.sign_of_pos hposy, hkey, abs_div, abs_mul, abs_of_pos hpos4,
        abs_of_pos hDpos]
      have hXY : 0 ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
          Real.exp (-(cylFreq c * |y.2|))) := by
        apply mul_nonneg (mul_nonneg hpos4.le zero_le_two)
        exact mul_nonneg (div_nonneg zero_le_one hκ.le) (Real.exp_pos _).le
      calc cylFreq c / (4 * Real.pi) * |Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))| /
            cylDen c y
          ≤ cylFreq c / (4 * Real.pi) * 2 / cylDen c y :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hpos4.le) hDpos.le
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / cylDen c y) := by ring
        _ ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
              Real.exp (-(cylFreq c * |y.2|))) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg hpos4.le zero_le_two)
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2)) *
              Real.exp (-(cylFreq c * |y.2|)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
