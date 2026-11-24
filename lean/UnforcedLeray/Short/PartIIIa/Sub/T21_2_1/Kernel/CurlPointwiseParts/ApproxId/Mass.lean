import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2
import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0592.Kernel

/-!
# `KerLapMass`: unit mass of the regularised Laplacian on the cell (SP 2081-2084, 3121)

With `θ = 2πq/d`, `φ = 2πη/d`, `C = cosh φ`, `c = cos θ`, `D = C - c + ε`:
`lapForm = P1 + P2` where `P1 = ∂_q G1` and `P2 = ∂_η G2` for the closed forms
`G1 = sin θ/(2dD)`, `G2 = sinh φ/(2dD)` of the first derivatives of `kerReg`.
`∫_cell P1 = 0` (Fubini, FTC in `q`, periodicity of `sin`), and `∫_η P2 = 1/d` for each `q`
(improper FTC, `G2 → ±1/(2d)`), so `∫_cell P2 = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

def kLM_G1 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sin (2 * Real.pi * z.1 / d) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε))

def kLM_G2 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sinh (2 * Real.pi * z.2 / d) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε))

def kLM_P1 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * Real.pi / d * (Real.cos (2 * Real.pi * z.1 / d) * (Real.cosh (2 * Real.pi * z.2 / d) + ε) - 1) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) ^ 2)

def kLM_P2 (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * Real.pi / d * (1 + Real.cosh (2 * Real.pi * z.2 / d) * (ε - Real.cos (2 * Real.pi * z.1 / d))) /
    (2 * d * (Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε) ^ 2)

def kLM_K (d ε : ℝ) : ℝ :=
  2 * Real.pi / d * (ε + 2) / (2 * d * (min ε 1) ^ 2 * (min 1 (8 / d ^ 2)))

def kLM_g (k φ : ℝ) : ℝ :=
  (1 - Real.exp (-φ) ^ 2) / (1 + Real.exp (-φ) ^ 2 - 2 * k * Real.exp (-φ))

lemma kLM_D_pos {d ε : ℝ} (hε : 0 < ε) (z : ℝ × ℝ) :
    0 < Real.cosh (2 * Real.pi * z.2 / d) - Real.cos (2 * Real.pi * z.1 / d) + ε := by
  linarith [Real.one_le_cosh (2 * Real.pi * z.2 / d), Real.cos_le_one (2 * Real.pi * z.1 / d)]

lemma kLM_cosh_lower {d : ℝ} (hd : 0 < d) (η : ℝ) :
    1 + 8 * η ^ 2 / d ^ 2 ≤ Real.cosh (2 * Real.pi * η / d) := by
  have h2 : 2 * Real.pi * η / d = 2 * (Real.pi * η / d) := by ring
  rw [h2, Real.cosh_two_mul]
  have hc := Real.cosh_sq (Real.pi * η / d)
  have hs := UnforcedLeray.B0592.sinh_sq_lower hd η
  have h8 : 8 * η ^ 2 / d ^ 2 ≤ 2 * Real.sinh (Real.pi * η / d) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hs]
  nlinarith [hc, h8]

lemma kLM_cosh_kappa {d ε : ℝ} (hd : 0 < d) (η : ℝ) :
    min 1 (8 / d ^ 2) * (1 + η ^ 2) ≤ Real.cosh (2 * Real.pi * η / d) := by
  have hκ2 : min 1 (8 / d ^ 2) ≤ 8 / d ^ 2 := min_le_right _ _
  have h1 : min 1 (8 / d ^ 2) * η ^ 2 ≤ 8 / d ^ 2 * η ^ 2 :=
    mul_le_mul_of_nonneg_right hκ2 (sq_nonneg _)
  have e : 8 / d ^ 2 * η ^ 2 = 8 * η ^ 2 / d ^ 2 := by ring
  have hκ1 : min 1 (8 / d ^ 2) ≤ 1 := min_le_left _ _
  nlinarith [h1, e, kLM_cosh_lower hd η]

/-- Abstract bound `|N/(2dD²)| ≤ B/(2dm²κ)·(1+η²)⁻¹`. -/
lemma kLM_abs {N B C D m κ d η : ℝ} (hd : 0 < d) (hB : 0 ≤ B) (hm : 0 < m) (hκ : 0 < κ)
    (hC1 : 1 ≤ C) (hN : |N| ≤ B * C) (hD : m * C ≤ D) (hCκ : κ * (1 + η ^ 2) ≤ C) :
    |N / (2 * d * D ^ 2)| ≤ B / (2 * d * m ^ 2 * κ) * (1 + η ^ 2)⁻¹ := by
  have hCpos : 0 < C := by linarith
  have hmC : 0 < m * C := mul_pos hm hCpos
  have hDpos : 0 < D := lt_of_lt_of_le hmC hD
  have hdpos : 0 < 2 * d := by linarith
  have hpos1 : 0 < 2 * d * D ^ 2 := mul_pos hdpos (pow_pos hDpos 2)
  have hpos2 : 0 < 2 * d * (m * C) ^ 2 := mul_pos hdpos (pow_pos hmC 2)
  have s1 : |N| / (2 * d * D ^ 2) ≤ |N| / (2 * d * (m * C) ^ 2) :=
    div_le_div_of_nonneg_left (abs_nonneg N) hpos2
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmC.le hD 2) hdpos.le)
  have s2 : |N| / (2 * d * (m * C) ^ 2) ≤ B * C / (2 * d * (m * C) ^ 2) :=
    div_le_div_of_nonneg_right hN hpos2.le
  have s3 : B * C / (2 * d * (m * C) ^ 2) = B / (2 * d * m ^ 2) * (1 / C) := by
    field_simp <;> ring
  have hpos : 0 < κ * (1 + η ^ 2) := mul_pos hκ (by positivity)
  have hinv : 1 / C ≤ κ⁻¹ * (1 + η ^ 2)⁻¹ := by
    calc 1 / C ≤ 1 / (κ * (1 + η ^ 2)) := one_div_le_one_div_of_le hpos hCκ
      _ = κ⁻¹ * (1 + η ^ 2)⁻¹ := by rw [one_div, mul_inv]
  have hK0 : 0 ≤ B / (2 * d * m ^ 2) := div_nonneg hB (by positivity)
  have s4 : B / (2 * d * m ^ 2) * (1 / C) ≤ B / (2 * d * m ^ 2) * (κ⁻¹ * (1 + η ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hK0
  have s5 : B / (2 * d * m ^ 2) * (κ⁻¹ * (1 + η ^ 2)⁻¹) = B / (2 * d * m ^ 2 * κ) * (1 + η ^ 2)⁻¹ := by
    field_simp <;> ring
  rw [abs_div, abs_of_pos hpos1]
  linarith [s1, s2, s3, s4, s5]

lemma kLM_mC {ε C c : ℝ} (hε : 0 < ε) (hC1 : 1 ≤ C) (hc : c ≤ 1) :
    min ε 1 * C ≤ C - c + ε := by
  have h1 : min ε 1 ≤ ε := min_le_left _ _
  have h2 : min ε 1 ≤ 1 := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.2 hC1) (sub_nonneg.2 h2)]

lemma kLM_P1_bound {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    |kLM_P1 d ε z| ≤ kLM_K d ε * (1 + z.2 ^ 2)⁻¹ := by
  have hD := kLM_D_pos (d := d) hε z
  have hC1 : 1 ≤ Real.cosh (2 * Real.pi * z.2 / d) := Real.one_le_cosh _
  have hc1 : Real.cos (2 * Real.pi * z.1 / d) ≤ 1 := Real.cos_le_one _
  have hc2 : -1 ≤ Real.cos (2 * Real.pi * z.1 / d) := Real.neg_one_le_cos _
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hκ : 0 < min 1 (8 / d ^ 2) := lt_min one_pos (by positivity)
  have hB : 0 ≤ 2 * Real.pi / d * (ε + 2) :=
    mul_nonneg (div_nonneg (by positivity) hd.le) (by linarith)
  have hpi : 0 ≤ 2 * Real.pi / d := div_nonneg (by positivity) hd.le
  have key : |Real.cos (2 * Real.pi * z.1 / d) * (Real.cosh (2 * Real.pi * z.2 / d) + ε) - 1| ≤
      (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.cos (2 * Real.pi * z.1 / d) + 1)
        (by linarith : (0:ℝ) ≤ Real.cosh (2 * Real.pi * z.2 / d) + ε),
        mul_nonneg hε.le (sub_nonneg.2 hC1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hc1) (by linarith : (0:ℝ) ≤ Real.cosh (2 * Real.pi * z.2 / d) + ε),
        mul_nonneg hε.le (sub_nonneg.2 hC1)]
  have hN : |2 * Real.pi / d * (Real.cos (2 * Real.pi * z.1 / d) *
      (Real.cosh (2 * Real.pi * z.2 / d) + ε) - 1)| ≤
      2 * Real.pi / d * (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by
    rw [abs_mul, abs_of_nonneg hpi]
    calc 2 * Real.pi / d * |Real.cos (2 * Real.pi * z.1 / d) *
          (Real.cosh (2 * Real.pi * z.2 / d) + ε) - 1|
        ≤ 2 * Real.pi / d * ((ε + 2) * Real.cosh (2 * Real.pi * z.2 / d)) :=
          mul_le_mul_of_nonneg_left key hpi
      _ = 2 * Real.pi / d * (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by ring
  have hmain := kLM_abs hd hB hm hκ hC1 hN (kLM_mC hε hC1 hc1) (kLM_cosh_kappa (ε := ε) hd z.2)
  unfold kLM_P1 kLM_K
  exact hmain

lemma kLM_P2_bound {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    |kLM_P2 d ε z| ≤ kLM_K d ε * (1 + z.2 ^ 2)⁻¹ := by
  have hD := kLM_D_pos (d := d) hε z
  have hC1 : 1 ≤ Real.cosh (2 * Real.pi * z.2 / d) := Real.one_le_cosh _
  have hc1 : Real.cos (2 * Real.pi * z.1 / d) ≤ 1 := Real.cos_le_one _
  have hc2 : -1 ≤ Real.cos (2 * Real.pi * z.1 / d) := Real.neg_one_le_cos _
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hκ : 0 < min 1 (8 / d ^ 2) := lt_min one_pos (by positivity)
  have hB : 0 ≤ 2 * Real.pi / d * (ε + 2) :=
    mul_nonneg (div_nonneg (by positivity) hd.le) (by linarith)
  have hpi : 0 ≤ 2 * Real.pi / d := div_nonneg (by positivity) hd.le
  have key : |1 + Real.cosh (2 * Real.pi * z.2 / d) * (ε - Real.cos (2 * Real.pi * z.1 / d))| ≤
      (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by
    have hC0 : 0 ≤ Real.cosh (2 * Real.pi * z.2 / d) := by linarith
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hC0 (by linarith : (0:ℝ) ≤ Real.cos (2 * Real.pi * z.1 / d) + 1),
        mul_nonneg hε.le hC0]
    · nlinarith [mul_nonneg hC0 (by linarith : (0:ℝ) ≤ 1 - Real.cos (2 * Real.pi * z.1 / d)),
        mul_nonneg hε.le hC0]
  have hN : |2 * Real.pi / d * (1 + Real.cosh (2 * Real.pi * z.2 / d) *
      (ε - Real.cos (2 * Real.pi * z.1 / d)))| ≤
      2 * Real.pi / d * (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by
    rw [abs_mul, abs_of_nonneg hpi]
    calc 2 * Real.pi / d * |1 + Real.cosh (2 * Real.pi * z.2 / d) *
          (ε - Real.cos (2 * Real.pi * z.1 / d))|
        ≤ 2 * Real.pi / d * ((ε + 2) * Real.cosh (2 * Real.pi * z.2 / d)) :=
          mul_le_mul_of_nonneg_left key hpi
      _ = 2 * Real.pi / d * (ε + 2) * Real.cosh (2 * Real.pi * z.2 / d) := by ring
  have hmain := kLM_abs hd hB hm hκ hC1 hN (kLM_mC hε hC1 hc1) (kLM_cosh_kappa (ε := ε) hd z.2)
  unfold kLM_P2 kLM_K
  exact hmain

lemma kLM_lap_eq {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.lapForm d ε z = kLM_P1 d ε z + kLM_P2 d ε z := by
  have hD := (kLM_D_pos (d := d) hε z).ne'
  unfold lapForm kLM_P1 kLM_P2 UnforcedLeray.B0592.den
  field_simp
  ring

lemma kLM_P1_cont {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    Continuous (fun z : ℝ × ℝ => kLM_P1 d ε z) := by
  unfold kLM_P1
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (pow_ne_zero 2 (kLM_D_pos hε z).ne')

lemma kLM_P2_cont {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    Continuous (fun z : ℝ × ℝ => kLM_P2 d ε z) := by
  unfold kLM_P2
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (pow_ne_zero 2 (kLM_D_pos hε z).ne')

lemma kLM_hasDeriv1 {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q η : ℝ) :
    HasDerivAt (fun t : ℝ => kLM_G1 d ε (t, η)) (kLM_P1 d ε (q, η)) q := by
  have hDq : Real.cosh (2 * Real.pi * η / d) - Real.cos (2 * Real.pi * q / d) + ε ≠ 0 :=
    (kLM_D_pos (d := d) hε (q, η)).ne'
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) q :=
    ((hasDerivAt_id' q).const_mul (2 * Real.pi)).div_const d
  have hnum : HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t / d))
      (Real.cos (2 * Real.pi * q / d) * (2 * Real.pi * 1 / d)) q := hθ.sin
  have hden := ((hθ.cos).const_sub (Real.cosh (2 * Real.pi * η / d))).add_const ε
  have hDd := hden.const_mul (2 * d)
  have hq := hnum.div hDd (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDq)
  refine hq.congr_deriv ?_
  unfold kLM_P1
  dsimp only
  rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDq))
    (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (pow_ne_zero 2 hDq))]
  linear_combination (-4 * d ^ 2 * (2 * Real.pi / d) *
      (Real.cosh (2 * Real.pi * η / d) - Real.cos (2 * Real.pi * q / d) + ε) ^ 2) *
    Real.sin_sq_add_cos_sq (2 * Real.pi * q / d)

lemma kLM_hasDeriv2 {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q η : ℝ) :
    HasDerivAt (fun t : ℝ => kLM_G2 d ε (q, t)) (kLM_P2 d ε (q, η)) η := by
  have hDq : Real.cosh (2 * Real.pi * η / d) - Real.cos (2 * Real.pi * q / d) + ε ≠ 0 :=
    (kLM_D_pos (d := d) hε (q, η)).ne'
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t / d) (2 * Real.pi * 1 / d) η :=
    ((hasDerivAt_id' η).const_mul (2 * Real.pi)).div_const d
  have hnum : HasDerivAt (fun t : ℝ => Real.sinh (2 * Real.pi * t / d))
      (Real.cosh (2 * Real.pi * η / d) * (2 * Real.pi * 1 / d)) η := hθ.sinh
  have hden := ((hθ.cosh).sub_const (Real.cos (2 * Real.pi * q / d))).add_const ε
  have hDd := hden.const_mul (2 * d)
  have hq := hnum.div hDd (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDq)
  refine hq.congr_deriv ?_
  unfold kLM_P2
  dsimp only
  rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') hDq))
    (mul_ne_zero (mul_ne_zero two_ne_zero hd.ne') (pow_ne_zero 2 hDq))]
  linear_combination (4 * d ^ 2 * (2 * Real.pi / d) *
      (Real.cosh (2 * Real.pi * η / d) - Real.cos (2 * Real.pi * q / d) + ε) ^ 2) *
    Real.cosh_sq (2 * Real.pi * η / d)

lemma kLM_ftc {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (y : ℝ) :
    ∫ x in Set.Ico (-(d / 2)) (d / 2), kLM_P1 d ε (x, y) = 0 := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(d / 2) ≤ d / 2)]
  have hc : Continuous (fun x : ℝ => kLM_P1 d ε (x, y)) :=
    (kLM_P1_cont hd hε).comp (continuous_id.prodMk continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => kLM_G1 d ε (x, y))
    (f' := fun x => kLM_P1 d ε (x, y))
    (fun x _ => kLM_hasDeriv1 hd hε x y) (hc.intervalIntegrable _ _)]
  have hd0 : d ≠ 0 := hd.ne'
  have h1 : Real.sin (2 * Real.pi * (d / 2) / d) = 0 := by
    rw [show 2 * Real.pi * (d / 2) / d = Real.pi by field_simp]
    exact Real.sin_pi
  have h2 : Real.sin (2 * Real.pi * (-(d / 2)) / d) = 0 := by
    rw [show 2 * Real.pi * (-(d / 2)) / d = -Real.pi by field_simp]
    rw [Real.sin_neg, Real.sin_pi, neg_zero]
  simp only [kLM_G1, h1, h2, zero_div, sub_self]

lemma kLM_g_tendsto (k : ℝ) : Tendsto (kLM_g k) atTop (𝓝 1) := by
  have hu : Tendsto (fun φ : ℝ => Real.exp (-φ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 : Tendsto (fun φ : ℝ => 1 - Real.exp (-φ) ^ 2) atTop (𝓝 (1 - 0 ^ 2)) :=
    tendsto_const_nhds.sub (hu.pow 2)
  have h2 : Tendsto (fun φ : ℝ => 1 + Real.exp (-φ) ^ 2 - 2 * k * Real.exp (-φ)) atTop
      (𝓝 (1 + 0 ^ 2 - 2 * k * 0)) :=
    (tendsto_const_nhds.add (hu.pow 2)).sub (tendsto_const_nhds.mul hu)
  have h3 := h1.div h2 (by norm_num)
  have h4 : (1 - (0 : ℝ) ^ 2) / (1 + 0 ^ 2 - 2 * k * 0) = 1 := by norm_num
  rw [h4] at h3
  exact h3

lemma kLM_key (φ k : ℝ) (hX : Real.cosh φ - k ≠ 0) :
    Real.sinh φ / (Real.cosh φ - k) = kLM_g k φ := by
  unfold kLM_g
  have hE : Real.exp φ * Real.exp (-φ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hB : 1 + Real.exp (-φ) ^ 2 - 2 * k * Real.exp (-φ) ≠ 0 := by
    have e : 1 + Real.exp (-φ) ^ 2 - 2 * k * Real.exp (-φ) =
        2 * Real.exp (-φ) * (Real.cosh φ - k) := by
      rw [Real.cosh_eq]
      linear_combination (-1 : ℝ) * hE
    rw [e]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Real.exp_pos _).ne') hX
  rw [div_eq_div_iff hX hB, Real.sinh_eq, Real.cosh_eq]
  linear_combination (Real.exp (-φ) - k) * hE

lemma kLM_G2_eq {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q η : ℝ) :
    kLM_G2 d ε (q, η) = 1 / (2 * d) * kLM_g (Real.cos (2 * Real.pi * q / d) - ε) (2 * Real.pi * η / d) := by
  have hX : Real.cosh (2 * Real.pi * η / d) - (Real.cos (2 * Real.pi * q / d) - ε) ≠ 0 := by
    have hD := kLM_D_pos (d := d) hε (q, η)
    have e : Real.cosh (2 * Real.pi * η / d) - (Real.cos (2 * Real.pi * q / d) - ε) =
        Real.cosh (2 * Real.pi * η / d) - Real.cos (2 * Real.pi * q / d) + ε := by ring
    rw [e]
    exact hD.ne'
  have e1 : kLM_G2 d ε (q, η) = Real.sinh (2 * Real.pi * η / d) /
      (2 * d * (Real.cosh (2 * Real.pi * η / d) - (Real.cos (2 * Real.pi * q / d) - ε))) := by
    unfold kLM_G2
    dsimp only
    congr 1
    ring
  have hd0 : d ≠ 0 := hd.ne'
  rw [e1, ← kLM_key _ _ hX]
  field_simp

lemma kLM_tend_top {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q : ℝ) :
    Tendsto (fun η : ℝ => kLM_G2 d ε (q, η)) atTop (𝓝 (1 / (2 * d))) := by
  have hφ : Tendsto (fun η : ℝ => 2 * Real.pi * η / d) atTop atTop := by
    apply Filter.Tendsto.atTop_div_const hd
    exact Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
  have h := (((kLM_g_tendsto (Real.cos (2 * Real.pi * q / d) - ε)).comp hφ).const_mul
    (1 / (2 * d)))
  rw [mul_one] at h
  refine Tendsto.congr (fun η => ?_) h
  simp only [Function.comp_apply]
  rw [kLM_G2_eq hd hε q η]

lemma kLM_tend_bot {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q : ℝ) :
    Tendsto (fun η : ℝ => kLM_G2 d ε (q, η)) atBot (𝓝 (-(1 / (2 * d)))) := by
  have hodd : ∀ η : ℝ, kLM_G2 d ε (q, -η) = - kLM_G2 d ε (q, η) := by
    intro η
    unfold kLM_G2
    dsimp only
    rw [show 2 * Real.pi * (-η) / d = -(2 * Real.pi * η / d) by ring, Real.sinh_neg,
      Real.cosh_neg]
    ring
  have h := (kLM_tend_top hd hε q).comp tendsto_neg_atBot_atTop
  refine Tendsto.congr (fun x => ?_) h.neg
  simp only [Function.comp_apply]
  rw [hodd x]
  ring

lemma kLM_int_slice {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q : ℝ) :
    Integrable (fun η : ℝ => kLM_P2 d ε (q, η)) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (kLM_K d ε))
    ((kLM_P2_cont hd hε).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs]
  exact kLM_P2_bound hd hε (q, η)

lemma kLM_int_eta {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (q : ℝ) :
    ∫ η : ℝ, kLM_P2 d ε (q, η) = 1 / d := by
  have h := integral_of_hasDerivAt_of_tendsto
    (f := fun η : ℝ => kLM_G2 d ε (q, η)) (f' := fun η : ℝ => kLM_P2 d ε (q, η))
    (fun η => kLM_hasDeriv2 hd hε q η) (kLM_int_slice hd hε q)
    (kLM_tend_bot hd hε q) (kLM_tend_top hd hε q)
  rw [h]
  ring

lemma kLM_cell_int {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (hb : ∀ z : ℝ × ℝ, |f z| ≤ kLM_K d ε * (1 + z.2 ^ 2)⁻¹) :
    IntegrableOn f (B0579.cell d) := by
  have hg1 : Integrable (fun q : ℝ => (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) q) := by
    refine (integrable_indicator_iff measurableSet_Ico).2 ?_
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hg2 : Integrable (fun η : ℝ => kLM_K d ε * (1 + η ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hprod : Integrable (fun z : ℝ × ℝ =>
      (Set.Ico (-(d / 2)) (d / 2)).indicator (fun _ => (1 : ℝ)) z.1 *
        (kLM_K d ε * (1 + z.2 ^ 2)⁻¹)) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hg1.mul_prod hg2
  refine Integrable.mono' hprod.integrableOn hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with z hz
  have hzI : z.1 ∈ Set.Ico (-(d / 2)) (d / 2) := hz.1
  simp only [Real.norm_eq_abs, Set.indicator_of_mem hzI, one_mul]
  exact hb z

lemma kLM_cell_P1_zero {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hP1 : IntegrableOn (kLM_P1 d ε) (B0579.cell d)) :
    ∫ x in B0579.cell d, kLM_P1 d ε x = 0 := by
  show ∫ x in Set.Ico (-(d / 2)) (d / 2) ×ˢ (Set.univ : Set ℝ), kLM_P1 d ε x = 0
  rw [Measure.volume_eq_prod] at hP1 ⊢
  rw [← setIntegral_prod_swap (Set.Ico (-(d / 2)) (d / 2)) (Set.univ : Set ℝ) (kLM_P1 d ε)]
  have hsw := hP1.swap
  rw [setIntegral_prod (fun z : ℝ × ℝ => kLM_P1 d ε z.swap) hsw]
  simp only [Prod.swap_prod_mk]
  have hz : ∀ x : ℝ, ∫ y in Set.Ico (-(d / 2)) (d / 2), kLM_P1 d ε (y, x) = 0 :=
    fun x => kLM_ftc hd hε x
  simp only [hz, integral_zero]

lemma kLM_cell_P2_one {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hP2 : IntegrableOn (kLM_P2 d ε) (B0579.cell d)) :
    ∫ x in B0579.cell d, kLM_P2 d ε x = 1 := by
  show ∫ x in Set.Ico (-(d / 2)) (d / 2) ×ˢ (Set.univ : Set ℝ), kLM_P2 d ε x = 1
  rw [Measure.volume_eq_prod] at hP2 ⊢
  rw [setIntegral_prod (kLM_P2 d ε) hP2]
  have hin : ∀ x : ℝ, ∫ y in (Set.univ : Set ℝ), kLM_P2 d ε (x, y) = 1 / d := by
    intro x
    rw [setIntegral_univ]
    exact kLM_int_eta hd hε x
  simp only [hin]
  rw [setIntegral_const, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  have e : d / 2 - -(d / 2) = d := by ring
  rw [e]
  field_simp

theorem kerLapMass : UnforcedLeray.Short.IIIa.KerLapMass := by
  intro d ε hd hε
  have hP1i : IntegrableOn (kLM_P1 d ε) (B0579.cell d) :=
    kLM_cell_int hd hε _ (kLM_P1_cont hd hε) (fun z => kLM_P1_bound hd hε z)
  have hP2i : IntegrableOn (kLM_P2 d ε) (B0579.cell d) :=
    kLM_cell_int hd hε _ (kLM_P2_cont hd hε) (fun z => kLM_P2_bound hd hε z)
  have hsplit : (fun x => UnforcedLeray.Short.IIIa.lapForm d ε x) =
      fun x => kLM_P1 d ε x + kLM_P2 d ε x :=
    funext fun x => kLM_lap_eq hd hε x
  rw [hsplit, integral_add hP1i hP2i, kLM_cell_P1_zero hd hε hP1i,
    kLM_cell_P2_one hd hε hP2i, zero_add]

end UnforcedLeray.Short.IIIa
