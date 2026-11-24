import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkFDerivClosed

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : leaf (B1) `BrkGaussBound1`

Source of record: `the November 2 reference manuscript` (73 pages), 4963 (`a = 1 + νs ≥ 1`,
`G = a⁻² e^{-|y|²/(4a)}`), 4971-4973 (the closed form `b_j = G·bkP`, its derivative `DV_j`), 4978 (the
Gaussian bounds).

Write `y = x_j`, `M = A^y(s)`, `K = |M₀₀| + |M₀₂| + |M₂₀| + |M₂₂|`, `n = |y|`, `E = e^{-|y|²/(4a)}`.
The polynomial bounds are `‖bkP‖ ≤ 4K(1+n)³` and `‖bkD1·w‖ ≤ 16K(1+n)⁴‖w‖` (sup norm; `Jrot` is an
isometry, `|bkDot u w| ≤ 2|u||w|`, `|c/(2a)| ≤ |c|` for `a ≥ 1`). Since `G ≤ E` and `bkMaj = (1+n)⁶E`,
both claims hold with the constant `16K`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The meridional `ℓ¹`-type constant `|M₀₀| + |M₀₂| + |M₂₀| + |M₂₂|` of `gp_merApply_norm_le`. -/
def bkB1_K (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

lemma bkB1_K_nonneg (M : Mat3) : 0 ≤ bkB1_K M := by
  unfold bkB1_K; positivity

lemma bkB1_merApply (M : Mat3) (w : ℝ × ℝ) : ‖merApply M w‖ ≤ bkB1_K M * ‖w‖ :=
  gp_merApply_norm_le M w

/-- `|u·w| ≤ 2|u||w|` in the sup norm. -/
lemma bkB1_dot (u w : ℝ × ℝ) : |bkDot u w| ≤ 2 * ‖u‖ * ‖w‖ := by
  unfold bkDot
  have h1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have h3 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
  have h4 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
  calc |u.1 * w.1 + u.2 * w.2| ≤ |u.1 * w.1| + |u.2 * w.2| := abs_add_le _ _
    _ = |u.1| * |w.1| + |u.2| * |w.2| := by rw [abs_mul, abs_mul]
    _ ≤ ‖u‖ * ‖w‖ + ‖u‖ * ‖w‖ :=
        add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖u‖ * ‖w‖ := by ring

/-- Division by `2a ≥ 2` does not increase the absolute value. -/
lemma bkB1_div (c a : ℝ) (ha : 1 ≤ a) : |c / (2 * a)| ≤ |c| := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
  exact div_le_self (abs_nonneg c) (by linarith)

/-- `‖bkP M a y‖ ≤ 4K(1+|y|)³`. -/
lemma bkB1_P (M : Mat3) (a : ℝ) (y : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkP M a y‖ ≤ 4 * bkB1_K M * (1 + ‖y‖) ^ 3 := by
  have hK : 0 ≤ bkB1_K M := bkB1_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have h1 : ‖merApply M (Jrot y)‖ ≤ bkB1_K M * ‖y‖ := by
    have h := bkB1_merApply M (Jrot y)
    rwa [gp_jrot_norm] at h
  have h2 : ‖Jrot (merApply M y)‖ ≤ bkB1_K M * ‖y‖ := by
    rw [gp_jrot_norm]; exact bkB1_merApply M y
  have h4 : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkB1_K M * ‖y‖) :=
    (bkB1_dot y (merApply M y)).trans
      (mul_le_mul_of_nonneg_left (bkB1_merApply M y) (by positivity))
  have h5 : ‖(bkDot y (merApply M y) / (2 * a)) • Jrot y‖
      ≤ 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((bkB1_div _ a ha).trans h4) hn
  have h6 := norm_add_le (merApply M (Jrot y) - Jrot (merApply M y))
    ((bkDot y (merApply M y) / (2 * a)) • Jrot y)
  have h7 := norm_sub_le (merApply M (Jrot y)) (Jrot (merApply M y))
  have hsum : ‖bkP M a y‖ ≤ bkB1_K M * ‖y‖ + bkB1_K M * ‖y‖
      + 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖y‖ := by
    unfold bkP
    linarith
  have hA : ‖y‖ ≤ (1 + ‖y‖) ^ 3 := by nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]
  have hB : ‖y‖ ^ 3 ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_left₀ hn (by linarith) 3
  have hpoly : 0 ≤ 4 * (1 + ‖y‖) ^ 3 - 2 * ‖y‖ - 2 * ‖y‖ ^ 3 := by linarith
  have e : 4 * bkB1_K M * (1 + ‖y‖) ^ 3
      = (bkB1_K M * ‖y‖ + bkB1_K M * ‖y‖ + 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖y‖)
        + bkB1_K M * (4 * (1 + ‖y‖) ^ 3 - 2 * ‖y‖ - 2 * ‖y‖ ^ 3) := by ring
  rw [e]
  linarith [hsum, mul_nonneg hK hpoly]

/-- `‖∂_wbkP‖ ≤ 8K(1+|y|)²|w|`. -/
lemma bkB1_Pd (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkPd M a y w‖ ≤ 8 * bkB1_K M * (1 + ‖y‖) ^ 2 * ‖w‖ := by
  have hK : 0 ≤ bkB1_K M := bkB1_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have t1 : ‖merApply M (Jrot w)‖ ≤ bkB1_K M * ‖w‖ := by
    have h := bkB1_merApply M (Jrot w)
    rwa [gp_jrot_norm] at h
  have t2 : ‖Jrot (merApply M w)‖ ≤ bkB1_K M * ‖w‖ := by
    rw [gp_jrot_norm]; exact bkB1_merApply M w
  have hc1 : |bkDot w (merApply M y) + bkDot y (merApply M w)|
      ≤ 2 * ‖w‖ * (bkB1_K M * ‖y‖) + 2 * ‖y‖ * (bkB1_K M * ‖w‖) :=
    (abs_add_le _ _).trans (add_le_add
      ((bkB1_dot w (merApply M y)).trans
        (mul_le_mul_of_nonneg_left (bkB1_merApply M y) (by positivity)))
      ((bkB1_dot y (merApply M w)).trans
        (mul_le_mul_of_nonneg_left (bkB1_merApply M w) (by positivity))))
  have t3 : ‖((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y‖
      ≤ (2 * ‖w‖ * (bkB1_K M * ‖y‖) + 2 * ‖y‖ * (bkB1_K M * ‖w‖)) * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((bkB1_div _ a ha).trans hc1) hn
  have hc2 : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkB1_K M * ‖y‖) :=
    (bkB1_dot y (merApply M y)).trans
      (mul_le_mul_of_nonneg_left (bkB1_merApply M y) (by positivity))
  have t4 : ‖(bkDot y (merApply M y) / (2 * a)) • Jrot w‖
      ≤ 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, gp_jrot_norm]
    exact mul_le_mul_of_nonneg_right ((bkB1_div _ a ha).trans hc2) hw
  have h6 := norm_add_le
    (merApply M (Jrot w) - Jrot (merApply M w)
      + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y)
    ((bkDot y (merApply M y) / (2 * a)) • Jrot w)
  have h7 := norm_add_le (merApply M (Jrot w) - Jrot (merApply M w))
    (((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y)
  have h8 := norm_sub_le (merApply M (Jrot w)) (Jrot (merApply M w))
  have hsum : ‖bkPd M a y w‖ ≤ bkB1_K M * ‖w‖ + bkB1_K M * ‖w‖
      + (2 * ‖w‖ * (bkB1_K M * ‖y‖) + 2 * ‖y‖ * (bkB1_K M * ‖w‖)) * ‖y‖
      + 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖w‖ := by
    unfold bkPd
    linarith
  have hpoly : 0 ≤ 8 * (1 + ‖y‖) ^ 2 - 2 - 6 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖]
  have e : 8 * bkB1_K M * (1 + ‖y‖) ^ 2 * ‖w‖
      = (bkB1_K M * ‖w‖ + bkB1_K M * ‖w‖
          + (2 * ‖w‖ * (bkB1_K M * ‖y‖) + 2 * ‖y‖ * (bkB1_K M * ‖w‖)) * ‖y‖
          + 2 * ‖y‖ * (bkB1_K M * ‖y‖) * ‖w‖)
        + bkB1_K M * ‖w‖ * (8 * (1 + ‖y‖) ^ 2 - 2 - 6 * ‖y‖ ^ 2) := by ring
  rw [e]
  linarith [hsum, mul_nonneg (mul_nonneg hK hw) hpoly]

/-- `‖D_1(w)‖ ≤ 16K(1+|y|)⁴|w|`, where `D_1 w = ∂_w bkP - (y·w)/(2a)·bkP` (`bkD1`). -/
lemma bkB1_D1 (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkD1 M a y w‖ ≤ 16 * bkB1_K M * (1 + ‖y‖) ^ 4 * ‖w‖ := by
  have hK : 0 ≤ bkB1_K M := bkB1_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hPd := bkB1_Pd M a y w ha
  have hP := bkB1_P M a y ha
  have hc : |bkDot y w / (2 * a)| ≤ 2 * ‖y‖ * ‖w‖ := (bkB1_div _ a ha).trans (bkB1_dot y w)
  have hB : ‖(bkDot y w / (2 * a)) • bkP M a y‖ ≤ 2 * ‖y‖ * ‖w‖ * (4 * bkB1_K M * (1 + ‖y‖) ^ 3) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hP (norm_nonneg _) (by positivity)
  have h7 := norm_sub_le (bkPd M a y w) ((bkDot y w / (2 * a)) • bkP M a y)
  have hsum : ‖bkD1 M a y w‖ ≤ 8 * bkB1_K M * (1 + ‖y‖) ^ 2 * ‖w‖
      + 2 * ‖y‖ * ‖w‖ * (4 * bkB1_K M * (1 + ‖y‖) ^ 3) := by
    unfold bkD1
    linarith
  have hpoly : 0 ≤ (1 + ‖y‖) ^ 2 * (1 + 3 * ‖y‖ + ‖y‖ ^ 2) := by positivity
  have e : 16 * bkB1_K M * (1 + ‖y‖) ^ 4 * ‖w‖
      = 8 * bkB1_K M * (1 + ‖y‖) ^ 2 * ‖w‖
        + 2 * ‖y‖ * ‖w‖ * (4 * bkB1_K M * (1 + ‖y‖) ^ 3)
        + 8 * bkB1_K M * ‖w‖ * ((1 + ‖y‖) ^ 2 * (1 + 3 * ‖y‖ + ‖y‖ ^ 2)) := by ring
  rw [e]
  linarith [hsum, mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK) hw) hpoly]

/-- **(B1)** Gaussian bound of the bracket and its first derivative (source 4973, 4978). -/
theorem brkGaussBound1 : BrkGaussBound1 := by
  intro ν χ A s hν hs
  refine ⟨16 * bkB1_K (Ay ν χ A s), fun j z => ?_⟩
  have ha1 : 1 ≤ ageA ν s := bk_one_le_ageA hν hs
  have ha0 : 0 < ageA ν s := by linarith
  have hK : 0 ≤ bkB1_K (Ay ν χ A s) := bkB1_K_nonneg _
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hG0 : 0 ≤ bkG (ageA ν s) (xj ν j z) := by
    unfold bkG
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) hE0
  have hGE : bkG (ageA ν s) (xj ν j z) ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := by
    unfold bkG
    apply mul_le_of_le_one_left hE0
    apply inv_le_one_of_one_le₀
    nlinarith
  have hbase : 0 ≤ bkMaj ν (ageA ν s) j z := bkMaj_nonneg _ _ _ _
  have hmaj : bkMaj ν (ageA ν s) j z
      = (1 + ‖xj ν j z‖) ^ 6 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := rfl
  have hn1 : 1 ≤ 1 + ‖xj ν j z‖ := by linarith [norm_nonneg (xj ν j z)]
  have hc36 : (1 + ‖xj ν j z‖) ^ 3 ≤ (1 + ‖xj ν j z‖) ^ 6 :=
    pow_le_pow_right₀ hn1 (by norm_num)
  have hc46 : (1 + ‖xj ν j z‖) ^ 4 ≤ (1 + ‖xj ν j z‖) ^ 6 :=
    pow_le_pow_right₀ hn1 (by norm_num)
  constructor
  · rw [brkClosed ν χ A s j z, norm_smul, Real.norm_eq_abs, abs_of_nonneg hG0]
    have hP := bkB1_P (Ay ν χ A s) (ageA ν s) (xj ν j z) ha1
    have hfin := mul_nonneg (mul_nonneg hE0 hK) (sub_nonneg.2 hc36)
    have hfin2 := mul_nonneg (mul_nonneg hE0 hK) (by positivity : (0:ℝ) ≤ (1 + ‖xj ν j z‖) ^ 6)
    calc bkG (ageA ν s) (xj ν j z) * ‖bkP (Ay ν χ A s) (ageA ν s) (xj ν j z)‖
        ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
            * (4 * bkB1_K (Ay ν χ A s) * (1 + ‖xj ν j z‖) ^ 3) :=
          mul_le_mul hGE hP (norm_nonneg _) hE0
      _ ≤ 16 * bkB1_K (Ay ν χ A s) * bkMaj ν (ageA ν s) j z := by
          rw [hmaj]
          nlinarith [hfin, hfin2]
  · refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbase) (fun w => ?_)
    rw [(brkFDerivClosed ν χ A s j ha0).2 z w, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hG0]
    have hD := bkB1_D1 (Ay ν χ A s) (ageA ν s) (xj ν j z) w ha1
    have hfin := mul_nonneg (mul_nonneg (mul_nonneg hE0 hK) (norm_nonneg w)) (sub_nonneg.2 hc46)
    calc bkG (ageA ν s) (xj ν j z) * ‖bkD1 (Ay ν χ A s) (ageA ν s) (xj ν j z) w‖
        ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
            * (16 * bkB1_K (Ay ν χ A s) * (1 + ‖xj ν j z‖) ^ 4 * ‖w‖) :=
          mul_le_mul hGE hD (norm_nonneg _) hE0
      _ ≤ 16 * bkB1_K (Ay ν χ A s) * bkMaj ν (ageA ν s) j z * ‖w‖ := by
          rw [hmaj]
          nlinarith [hfin]

end UnforcedLeray.Short.PartIIIb.Concrete
