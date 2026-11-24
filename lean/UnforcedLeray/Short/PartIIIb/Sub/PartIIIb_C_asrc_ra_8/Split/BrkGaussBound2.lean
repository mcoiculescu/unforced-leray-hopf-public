import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkSecondClosed

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : leaf (B2) `BrkGaussBound2`

Source of record: `the November 2 reference manuscript` (73 pages), 4963 (`a = 1 + νs ≥ 1`,
`G = a⁻² e^{-|y|²/(4a)}`), 4973 (`b_j = G·bkP`, the second `x`-derivative `G·bkD2`), 4978 (the Gaussian
bounds).

With `w = ei b` (`|w| ≤ 1`) and `K = |M₀₀| + |M₀₂| + |M₂₀| + |M₂₂|`, `n = |y|`, `y = x_j`, the closed form
`bkD2 M a y w u = bkPdd M a y u w - ... ` splits into four terms, each bounded by the (B1) polynomial bounds
(`bkB2_P`, `bkB2_Pd`, `bkB2_D1`) and `‖bkPdd M a y u w‖ ≤ 12K n|u||w|`. Summing gives
`‖bkD2 w u‖ ≤ 68K(1+n)⁵|u|`, and `G ≤ E` with `bkMaj = (1+n)⁶E` gives the constant `68K`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The meridional `ℓ¹`-type constant `|M₀₀| + |M₀₂| + |M₂₀| + |M₂₂|` of `gp_merApply_norm_le`. -/
def bkB2_K (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

lemma bkB2_K_nonneg (M : Mat3) : 0 ≤ bkB2_K M := by
  unfold bkB2_K; positivity

lemma bkB2_merApply (M : Mat3) (w : ℝ × ℝ) : ‖merApply M w‖ ≤ bkB2_K M * ‖w‖ :=
  gp_merApply_norm_le M w

/-- `|u·w| ≤ 2|u||w|` in the sup norm. -/
lemma bkB2_dot (u w : ℝ × ℝ) : |bkDot u w| ≤ 2 * ‖u‖ * ‖w‖ := by
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
lemma bkB2_div (c a : ℝ) (ha : 1 ≤ a) : |c / (2 * a)| ≤ |c| := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
  exact div_le_self (abs_nonneg c) (by linarith)

/-- `‖bkP M a y‖ ≤ 4K(1+|y|)³`. -/
lemma bkB2_P (M : Mat3) (a : ℝ) (y : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkP M a y‖ ≤ 4 * bkB2_K M * (1 + ‖y‖) ^ 3 := by
  have hK : 0 ≤ bkB2_K M := bkB2_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have h1 : ‖merApply M (Jrot y)‖ ≤ bkB2_K M * ‖y‖ := by
    have h := bkB2_merApply M (Jrot y)
    rwa [gp_jrot_norm] at h
  have h2 : ‖Jrot (merApply M y)‖ ≤ bkB2_K M * ‖y‖ := by
    rw [gp_jrot_norm]; exact bkB2_merApply M y
  have h4 : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkB2_K M * ‖y‖) :=
    (bkB2_dot y (merApply M y)).trans
      (mul_le_mul_of_nonneg_left (bkB2_merApply M y) (by positivity))
  have h5 : ‖(bkDot y (merApply M y) / (2 * a)) • Jrot y‖
      ≤ 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((bkB2_div _ a ha).trans h4) hn
  have h6 := norm_add_le (merApply M (Jrot y) - Jrot (merApply M y))
    ((bkDot y (merApply M y) / (2 * a)) • Jrot y)
  have h7 := norm_sub_le (merApply M (Jrot y)) (Jrot (merApply M y))
  have hsum : ‖bkP M a y‖ ≤ bkB2_K M * ‖y‖ + bkB2_K M * ‖y‖
      + 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖y‖ := by
    unfold bkP
    linarith
  have hA : ‖y‖ ≤ (1 + ‖y‖) ^ 3 := by nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]
  have hB : ‖y‖ ^ 3 ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_left₀ hn (by linarith) 3
  have hpoly : 0 ≤ 4 * (1 + ‖y‖) ^ 3 - 2 * ‖y‖ - 2 * ‖y‖ ^ 3 := by linarith
  have e : 4 * bkB2_K M * (1 + ‖y‖) ^ 3
      = (bkB2_K M * ‖y‖ + bkB2_K M * ‖y‖ + 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖y‖)
        + bkB2_K M * (4 * (1 + ‖y‖) ^ 3 - 2 * ‖y‖ - 2 * ‖y‖ ^ 3) := by ring
  rw [e]
  linarith [hsum, mul_nonneg hK hpoly]

/-- `‖∂_wbkP‖ ≤ 8K(1+|y|)²|w|`. -/
lemma bkB2_Pd (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkPd M a y w‖ ≤ 8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖w‖ := by
  have hK : 0 ≤ bkB2_K M := bkB2_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have t1 : ‖merApply M (Jrot w)‖ ≤ bkB2_K M * ‖w‖ := by
    have h := bkB2_merApply M (Jrot w)
    rwa [gp_jrot_norm] at h
  have t2 : ‖Jrot (merApply M w)‖ ≤ bkB2_K M * ‖w‖ := by
    rw [gp_jrot_norm]; exact bkB2_merApply M w
  have hc1 : |bkDot w (merApply M y) + bkDot y (merApply M w)|
      ≤ 2 * ‖w‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖w‖) :=
    (abs_add_le _ _).trans (add_le_add
      ((bkB2_dot w (merApply M y)).trans
        (mul_le_mul_of_nonneg_left (bkB2_merApply M y) (by positivity)))
      ((bkB2_dot y (merApply M w)).trans
        (mul_le_mul_of_nonneg_left (bkB2_merApply M w) (by positivity))))
  have t3 : ‖((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y‖
      ≤ (2 * ‖w‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖w‖)) * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((bkB2_div _ a ha).trans hc1) hn
  have hc2 : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkB2_K M * ‖y‖) :=
    (bkB2_dot y (merApply M y)).trans
      (mul_le_mul_of_nonneg_left (bkB2_merApply M y) (by positivity))
  have t4 : ‖(bkDot y (merApply M y) / (2 * a)) • Jrot w‖
      ≤ 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, gp_jrot_norm]
    exact mul_le_mul_of_nonneg_right ((bkB2_div _ a ha).trans hc2) hw
  have h6 := norm_add_le
    (merApply M (Jrot w) - Jrot (merApply M w)
      + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y)
    ((bkDot y (merApply M y) / (2 * a)) • Jrot w)
  have h7 := norm_add_le (merApply M (Jrot w) - Jrot (merApply M w))
    (((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y)
  have h8 := norm_sub_le (merApply M (Jrot w)) (Jrot (merApply M w))
  have hsum : ‖bkPd M a y w‖ ≤ bkB2_K M * ‖w‖ + bkB2_K M * ‖w‖
      + (2 * ‖w‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖w‖)) * ‖y‖
      + 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖w‖ := by
    unfold bkPd
    linarith
  have hpoly : 0 ≤ 8 * (1 + ‖y‖) ^ 2 - 2 - 6 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖]
  have e : 8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖w‖
      = (bkB2_K M * ‖w‖ + bkB2_K M * ‖w‖
          + (2 * ‖w‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖w‖)) * ‖y‖
          + 2 * ‖y‖ * (bkB2_K M * ‖y‖) * ‖w‖)
        + bkB2_K M * ‖w‖ * (8 * (1 + ‖y‖) ^ 2 - 2 - 6 * ‖y‖ ^ 2) := by ring
  rw [e]
  linarith [hsum, mul_nonneg (mul_nonneg hK hw) hpoly]

/-- `‖D_1(w)‖ ≤ 16K(1+|y|)⁴|w|`, where `D_1 w = ∂_w bkP - (y·w)/(2a)·bkP` (`bkD1`). -/
lemma bkB2_D1 (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkD1 M a y w‖ ≤ 16 * bkB2_K M * (1 + ‖y‖) ^ 4 * ‖w‖ := by
  have hK : 0 ≤ bkB2_K M := bkB2_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hPd := bkB2_Pd M a y w ha
  have hP := bkB2_P M a y ha
  have hc : |bkDot y w / (2 * a)| ≤ 2 * ‖y‖ * ‖w‖ := (bkB2_div _ a ha).trans (bkB2_dot y w)
  have hB : ‖(bkDot y w / (2 * a)) • bkP M a y‖ ≤ 2 * ‖y‖ * ‖w‖ * (4 * bkB2_K M * (1 + ‖y‖) ^ 3) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hP (norm_nonneg _) (by positivity)
  have h7 := norm_sub_le (bkPd M a y w) ((bkDot y w / (2 * a)) • bkP M a y)
  have hsum : ‖bkD1 M a y w‖ ≤ 8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖w‖
      + 2 * ‖y‖ * ‖w‖ * (4 * bkB2_K M * (1 + ‖y‖) ^ 3) := by
    unfold bkD1
    linarith
  have hpoly : 0 ≤ (1 + ‖y‖) ^ 2 * (1 + 3 * ‖y‖ + ‖y‖ ^ 2) := by positivity
  have e : 16 * bkB2_K M * (1 + ‖y‖) ^ 4 * ‖w‖
      = 8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖w‖
        + 2 * ‖y‖ * ‖w‖ * (4 * bkB2_K M * (1 + ‖y‖) ^ 3)
        + 8 * bkB2_K M * ‖w‖ * ((1 + ‖y‖) ^ 2 * (1 + 3 * ‖y‖ + ‖y‖ ^ 2)) := by ring
  rw [e]
  linarith [hsum, mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK) hw) hpoly]

/-- Scaling by `1/(2a)`: `‖(c/(2a))•v‖ ≤ B‖v‖` when `|c| ≤ B`. -/
lemma bkB2_smul (c a : ℝ) (ha : 1 ≤ a) (v : ℝ × ℝ) (B : ℝ) (hc : |c| ≤ B) :
    ‖(c / (2 * a)) • v‖ ≤ B * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((bkB2_div c a ha).trans hc) (norm_nonneg v)

/-- `|p·(Mq)| ≤ 2|p|K|q|`. -/
lemma bkB2_pair (p q : ℝ × ℝ) (M : Mat3) :
    |bkDot p (merApply M q)| ≤ 2 * ‖p‖ * (bkB2_K M * ‖q‖) :=
  (bkB2_dot p (merApply M q)).trans
    (mul_le_mul_of_nonneg_left (bkB2_merApply M q) (by positivity))

/-- `‖∂_u∂_w bkP‖ ≤ 12K|y||u||w|`. -/
lemma bkB2_Pdd (M : Mat3) (a : ℝ) (y u w : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖bkPdd M a y u w‖ ≤ 12 * bkB2_K M * ‖y‖ * ‖u‖ * ‖w‖ := by
  have ta : |bkDot w (merApply M u) + bkDot u (merApply M w)| ≤ 4 * bkB2_K M * ‖u‖ * ‖w‖ := by
    refine (abs_add_le _ _).trans ?_
    have e : 2 * ‖w‖ * (bkB2_K M * ‖u‖) + 2 * ‖u‖ * (bkB2_K M * ‖w‖)
        = 4 * bkB2_K M * ‖u‖ * ‖w‖ := by ring
    linarith [bkB2_pair w u M, bkB2_pair u w M]
  have tb : |bkDot w (merApply M y) + bkDot y (merApply M w)| ≤ 4 * bkB2_K M * ‖y‖ * ‖w‖ := by
    refine (abs_add_le _ _).trans ?_
    have e : 2 * ‖w‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖w‖)
        = 4 * bkB2_K M * ‖y‖ * ‖w‖ := by ring
    linarith [bkB2_pair w y M, bkB2_pair y w M]
  have tc : |bkDot u (merApply M y) + bkDot y (merApply M u)| ≤ 4 * bkB2_K M * ‖y‖ * ‖u‖ := by
    refine (abs_add_le _ _).trans ?_
    have e : 2 * ‖u‖ * (bkB2_K M * ‖y‖) + 2 * ‖y‖ * (bkB2_K M * ‖u‖)
        = 4 * bkB2_K M * ‖y‖ * ‖u‖ := by ring
    linarith [bkB2_pair u y M, bkB2_pair y u M]
  have t1 := bkB2_smul _ a ha (Jrot y) _ ta
  have t2 := bkB2_smul _ a ha (Jrot u) _ tb
  have t3 := bkB2_smul _ a ha (Jrot w) _ tc
  rw [gp_jrot_norm] at t1 t2 t3
  unfold bkPdd
  have h6 := norm_add_le
    (((bkDot w (merApply M u) + bkDot u (merApply M w)) / (2 * a)) • Jrot y
      + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot u)
    (((bkDot u (merApply M y) + bkDot y (merApply M u)) / (2 * a)) • Jrot w)
  have h7 := norm_add_le
    (((bkDot w (merApply M u) + bkDot u (merApply M w)) / (2 * a)) • Jrot y)
    (((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot u)
  have e12 : 4 * bkB2_K M * ‖u‖ * ‖w‖ * ‖y‖ + 4 * bkB2_K M * ‖y‖ * ‖w‖ * ‖u‖
      + 4 * bkB2_K M * ‖y‖ * ‖u‖ * ‖w‖ = 12 * bkB2_K M * ‖y‖ * ‖u‖ * ‖w‖ := by ring
  linarith [h6, h7, t1, t2, t3, e12]

/-- `‖∂_w∂_u bkP‖`-free bound of the second bracket derivative: `‖D²b(w)(u)‖ ≤ 68K(1+|y|)⁵|u|` for
`|w| ≤ 1` (`bkD2`). -/
lemma bkB2_D2 (M : Mat3) (a : ℝ) (y w u : ℝ × ℝ) (ha : 1 ≤ a) (hw : ‖w‖ ≤ 1) :
    ‖bkD2 M a y w u‖ ≤ 68 * bkB2_K M * (1 + ‖y‖) ^ 5 * ‖u‖ := by
  have hK : 0 ≤ bkB2_K M := bkB2_K_nonneg M
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hX := bkB2_Pdd M a y u w ha
  have hT2 : ‖(bkDot u w / (2 * a)) • bkP M a y‖
      ≤ 2 * ‖u‖ * ‖w‖ * (4 * bkB2_K M * (1 + ‖y‖) ^ 3) :=
    (bkB2_smul (bkDot u w) a ha (bkP M a y) (2 * ‖u‖ * ‖w‖) (bkB2_dot u w)).trans
      (mul_le_mul_of_nonneg_left (bkB2_P M a y ha) (by positivity))
  have hT3 : ‖(bkDot y w / (2 * a)) • bkPd M a y u‖
      ≤ 2 * ‖y‖ * ‖w‖ * (8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖u‖) :=
    (bkB2_smul (bkDot y w) a ha (bkPd M a y u) (2 * ‖y‖ * ‖w‖) (bkB2_dot y w)).trans
      (mul_le_mul_of_nonneg_left (bkB2_Pd M a y u ha) (by positivity))
  have hT4 : ‖(bkDot y u / (2 * a)) • bkD1 M a y w‖
      ≤ 2 * ‖y‖ * ‖u‖ * (16 * bkB2_K M * (1 + ‖y‖) ^ 4 * ‖w‖) :=
    (bkB2_smul (bkDot y u) a ha (bkD1 M a y w) (2 * ‖y‖ * ‖u‖) (bkB2_dot y u)).trans
      (mul_le_mul_of_nonneg_left (bkB2_D1 M a y w ha) (by positivity))
  have h1 := norm_sub_le
    (bkPdd M a y u w - (bkDot u w / (2 * a)) • bkP M a y - (bkDot y w / (2 * a)) • bkPd M a y u)
    ((bkDot y u / (2 * a)) • bkD1 M a y w)
  have h2 := norm_sub_le (bkPdd M a y u w - (bkDot u w / (2 * a)) • bkP M a y)
    ((bkDot y w / (2 * a)) • bkPd M a y u)
  have h3 := norm_sub_le (bkPdd M a y u w) ((bkDot u w / (2 * a)) • bkP M a y)
  have hsplit : ‖bkD2 M a y w u‖ ≤ ‖bkPdd M a y u w‖ + ‖(bkDot u w / (2 * a)) • bkP M a y‖
      + ‖(bkDot y w / (2 * a)) • bkPd M a y u‖ + ‖(bkDot y u / (2 * a)) • bkD1 M a y w‖ := by
    unfold bkD2
    linarith
  have hA3 : ‖y‖ ≤ (1 + ‖y‖) ^ 3 := by nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]
  have hB : (1 + ‖y‖) ^ 3 ≤ (1 + ‖y‖) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hA : ‖y‖ ≤ (1 + ‖y‖) ^ 5 := hA3.trans hB
  have hC : ‖y‖ * (1 + ‖y‖) ^ 2 ≤ (1 + ‖y‖) ^ 5 := by
    have h := mul_le_mul_of_nonneg_right hA3 (sq_nonneg (1 + ‖y‖))
    have e : (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ^ 2 = (1 + ‖y‖) ^ 5 := by ring
    linarith
  have hD : ‖y‖ * (1 + ‖y‖) ^ 4 ≤ (1 + ‖y‖) ^ 5 := by
    have h := mul_le_mul_of_nonneg_right (show ‖y‖ ≤ 1 + ‖y‖ by linarith) (by positivity : (0:ℝ) ≤ (1 + ‖y‖) ^ 4)
    have e : (1 + ‖y‖) * (1 + ‖y‖) ^ 4 = (1 + ‖y‖) ^ 5 := by ring
    linarith
  have hQ : 12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
      + 32 * ‖y‖ * (1 + ‖y‖) ^ 4 ≤ 68 * (1 + ‖y‖) ^ 5 := by
    linarith
  have hKu : 0 ≤ bkB2_K M * ‖u‖ := mul_nonneg hK hu
  have hQ0 : 0 ≤ 12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
      + 32 * ‖y‖ * (1 + ‖y‖) ^ 4 := by positivity
  have hw1 : bkB2_K M * ‖u‖ * (12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
      + 32 * ‖y‖ * (1 + ‖y‖) ^ 4) * ‖w‖
      ≤ bkB2_K M * ‖u‖ * (12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
      + 32 * ‖y‖ * (1 + ‖y‖) ^ 4) :=
    mul_le_of_le_one_right (mul_nonneg hKu hQ0) hw
  have hKu2 : bkB2_K M * ‖u‖ * (12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
      + 32 * ‖y‖ * (1 + ‖y‖) ^ 4) ≤ bkB2_K M * ‖u‖ * (68 * (1 + ‖y‖) ^ 5) :=
    mul_le_mul_of_nonneg_left hQ hKu
  have e : 12 * bkB2_K M * ‖y‖ * ‖u‖ * ‖w‖ + 2 * ‖u‖ * ‖w‖ * (4 * bkB2_K M * (1 + ‖y‖) ^ 3)
      + 2 * ‖y‖ * ‖w‖ * (8 * bkB2_K M * (1 + ‖y‖) ^ 2 * ‖u‖)
      + 2 * ‖y‖ * ‖u‖ * (16 * bkB2_K M * (1 + ‖y‖) ^ 4 * ‖w‖)
      = bkB2_K M * ‖u‖ * (12 * ‖y‖ + 8 * (1 + ‖y‖) ^ 3 + 16 * ‖y‖ * (1 + ‖y‖) ^ 2
          + 32 * ‖y‖ * (1 + ‖y‖) ^ 4) * ‖w‖ := by ring
  linarith [hsplit, hX, hT2, hT3, hT4, e, hw1, hKu2]

/-- **(B2)** Gaussian bound of the second derivatives of the bracket (source 4973, 4978). -/
theorem brkGaussBound2 : BrkGaussBound2 := by
  intro ν χ A s hν hs
  refine ⟨68 * bkB2_K (Ay ν χ A s), fun j z b => ?_⟩
  have ha1 : 1 ≤ ageA ν s := bk_one_le_ageA hν hs
  have ha0 : 0 < ageA ν s := by linarith
  have hK : 0 ≤ bkB2_K (Ay ν χ A s) := bkB2_K_nonneg _
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
  have hc56 : (1 + ‖xj ν j z‖) ^ 5 ≤ (1 + ‖xj ν j z‖) ^ 6 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg (xj ν j z)]) (by norm_num)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hK) hbase) (fun u => ?_)
  rw [(brkSecondClosed ν χ A s j ha0 (ei b)).2 z u, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hG0]
  have hD := bkB2_D2 (Ay ν χ A s) (ageA ν s) (xj ν j z) (ei b) u ha1 (bk_norm_ei_le_one b)
  have hfin := mul_nonneg (mul_nonneg (mul_nonneg hE0 hK) (norm_nonneg u)) (sub_nonneg.2 hc56)
  calc bkG (ageA ν s) (xj ν j z) * ‖bkD2 (Ay ν χ A s) (ageA ν s) (xj ν j z) (ei b) u‖
      ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
          * (68 * bkB2_K (Ay ν χ A s) * (1 + ‖xj ν j z‖) ^ 5 * ‖u‖) :=
        mul_le_mul hGE hD (norm_nonneg _) hE0
    _ ≤ 68 * bkB2_K (Ay ν χ A s) * bkMaj ν (ageA ν s) j z * ‖u‖ := by
        rw [hmaj]
        nlinarith [hfin]

end UnforcedLeray.Short.PartIIIb.Concrete
