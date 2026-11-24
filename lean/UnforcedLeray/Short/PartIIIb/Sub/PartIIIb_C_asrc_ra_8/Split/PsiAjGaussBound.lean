import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.MgradPsiAjClosed

/-!
# `PartIII-b:C/asrc/ra/8/1/7` : leaf (B4) `PsiAjGaussBound`

Source of record: `the November 2 reference manuscript` (73 pages), 4964, 5024, 4978.

`Ψ_j(z) = (A^y_mer x_j)·∇p_j` with `∇p_j = G² x_j` (`bk_mgrad_pj`), and the gradient of `Ψ_j` is
`G² bkPsi` (`mgradPsiAjClosed`). The Gaussian factor satisfies `G² ≤ e^{-|x_j|²/(4a)}`, and the
polynomial factors are bounded by `(1 + |x_j|)^6`, giving the constant `K = 8 Kc` with
`Kc = |M₀₀| + |M₀₂| + |M₂₀| + |M₂₂|` for `M = A^y(s)`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The entry sum of a `3 × 3` matrix used in the matrix-action bound (`gp_merApply_norm_le`). -/
def bkB4_Kc (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

/-- `|u·w| ≤ 2 |u| |w|` in the meridional plane. -/
lemma bkB4_dot_le (u w : ℝ × ℝ) : |bkDot u w| ≤ 2 * ‖u‖ * ‖w‖ := by
  have h1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have h3 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
  have h4 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
  unfold bkDot
  have e1 : |u.1 * w.1| ≤ ‖u‖ * ‖w‖ := by
    rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
  have e2 : |u.2 * w.2| ≤ ‖u‖ * ‖w‖ := by
    rw [abs_mul]; exact mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _)
  calc |u.1 * w.1 + u.2 * w.2| ≤ |u.1 * w.1| + |u.2 * w.2| := abs_add_le _ _
    _ ≤ 2 * ‖u‖ * ‖w‖ := by nlinarith [e1, e2]

/-- The derivative of a real function applied to `u` is the pairing with its gradient. -/
lemma bkB4_fderiv_apply (f : ℝ × ℝ → ℝ) (x u : ℝ × ℝ) :
    fderiv ℝ f x u = bkDot u (mgrad f x) := by
  have hu : u = u.1 • ei 0 + u.2 • ei 1 := by
    obtain ⟨u1, u2⟩ := u
    ext <;> simp [ei]
  unfold bkDot mgrad
  conv_lhs => rw [hu]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Polynomial comparison `t² ≤ (1 + t)⁶` for `t ≥ 0`. -/
lemma bkB4_sq_le (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ (1 + t) ^ 6 := by
  have hA : t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  have hB : (1 + t) ^ 2 ≤ (1 + t) ^ 6 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

/-- An elementary inequality `(c e)² ≤ e` for `0 ≤ c, e ≤ 1`. -/
lemma bkB4_sq_aux (c e : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (c * e) ^ 2 ≤ e := by
  have h1 : c * e ≤ e := by nlinarith
  have h2 : (c * e) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (mul_nonneg hc0 he0) h1 2
  nlinarith

/-- `G² ≤ e^{-|y|²/(4a)}` for the Gaussian factor `G = (a²)⁻¹ e^{-|y|²/(4a)}`, `a ≥ 1`. -/
lemma bkB4_G2_le (a : ℝ) (ha : 1 ≤ a) (y : ℝ × ℝ) :
    bkG a y ^ 2 ≤ Real.exp (-(sq2 y) / (4 * a)) := by
  have ha0 : 0 < a := by linarith
  have hc0 : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hc1 : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hs : 0 ≤ sq2 y := by unfold sq2; positivity
  have he0 : 0 ≤ Real.exp (-(sq2 y) / (4 * a)) := (Real.exp_pos _).le
  have hneg : -(sq2 y) / (4 * a) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  have he1 : Real.exp (-(sq2 y) / (4 * a)) ≤ 1 := Real.exp_le_one_iff.mpr hneg
  unfold bkG
  exact bkB4_sq_aux _ _ hc0 hc1 he0 he1

/-- The norm of the Gaussian-free profile `bkPsi`. -/
lemma bkB4_psi_norm (M : Mat3) (a : ℝ) (ha : 1 ≤ a) (y : ℝ × ℝ) :
    ‖bkPsi M a y‖ ≤ 4 * bkB4_Kc M * (1 + ‖y‖) ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hKc : 0 ≤ bkB4_Kc M := by unfold bkB4_Kc; positivity
  have hMy : ‖merApply M y‖ ≤ bkB4_Kc M * ‖y‖ := gp_merApply_norm_le M y
  have hTy : ‖merApply (tr3 M) y‖ ≤ bkB4_Kc M * ‖y‖ := by
    have h := gp_merApply_norm_le (tr3 M) y
    have e : |tr3 M 0 0| + |tr3 M 0 2| + |tr3 M 2 0| + |tr3 M 2 2| = bkB4_Kc M := by
      simp only [bkB4_Kc, tr3]
      ring
    rw [e] at h
    exact h
  have hdot : |bkDot y (merApply M y)| ≤ 2 * ‖y‖ * (bkB4_Kc M * ‖y‖) := by
    have h := bkB4_dot_le y (merApply M y)
    have h2 : 2 * ‖y‖ * ‖merApply M y‖ ≤ 2 * ‖y‖ * (bkB4_Kc M * ‖y‖) :=
      mul_le_mul_of_nonneg_left hMy (by positivity)
    linarith
  have hterm : ‖(bkDot y (merApply M y) / a) • y‖ ≤ 2 * bkB4_Kc M * ‖y‖ ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos ha0]
    have h1 : |bkDot y (merApply M y)| / a ≤ |bkDot y (merApply M y)| :=
      div_le_self (abs_nonneg _) ha
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
    have h3 := mul_le_mul_of_nonneg_right hdot (norm_nonneg y)
    nlinarith [h2, h3]
  have hPsi : ‖bkPsi M a y‖ ≤
      ‖merApply M y‖ + ‖merApply (tr3 M) y‖ + ‖(bkDot y (merApply M y) / a) • y‖ := by
    unfold bkPsi
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have ht1 : ‖y‖ ≤ (1 + ‖y‖) ^ 3 := by
    nlinarith [norm_nonneg y, sq_nonneg ‖y‖, pow_nonneg (norm_nonneg y) 3]
  have ht2 : ‖y‖ ^ 3 ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg y) (by linarith) 3
  have k1 := mul_le_mul_of_nonneg_left ht1 hKc
  have k2 := mul_le_mul_of_nonneg_left ht2 hKc
  linarith [hPsi, hMy, hTy, hterm, k1, k2]

/-- The gradient bound `‖∇Ψ_j‖ ≤ 4 Kc (1+|y|)⁶ e^{-|y|²/(4a)}`. -/
lemma bkB4_mgrad_norm (M : Mat3) (a : ℝ) (ha : 1 ≤ a) (y : ℝ × ℝ) :
    ‖bkG a y ^ 2 • bkPsi M a y‖ ≤
      4 * bkB4_Kc M * ((1 + ‖y‖) ^ 6 * Real.exp (-(sq2 y) / (4 * a))) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hG := bkB4_G2_le a ha y
  have hP := bkB4_psi_norm M a ha y
  have hKc : 0 ≤ bkB4_Kc M := by unfold bkB4_Kc; positivity
  have he0 : 0 ≤ Real.exp (-(sq2 y) / (4 * a)) := (Real.exp_pos _).le
  have h1 : bkG a y ^ 2 * ‖bkPsi M a y‖ ≤
      Real.exp (-(sq2 y) / (4 * a)) * (4 * bkB4_Kc M * (1 + ‖y‖) ^ 3) :=
    mul_le_mul hG hP (norm_nonneg _) he0
  have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖y‖) ^ 6 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg y]) (by norm_num)
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hKc he0)
  nlinarith [h1, h3]

/-- **(B4)** Gaussian bound of `Ψ_j` and its first derivative (source 4964, 5024, 4978). -/
theorem psiAjGaussBound : PsiAjGaussBound := by
  intro ν χ A s hν hs
  have ha1 : 1 ≤ ageA ν s := bk_one_le_ageA hν hs
  have ha0 : 0 < ageA ν s := by linarith
  have hKc : 0 ≤ bkB4_Kc (Ay ν χ A s) := by unfold bkB4_Kc; positivity
  refine ⟨8 * bkB4_Kc (Ay ν χ A s), fun j z => ⟨?_, ?_⟩⟩
  · have hPsi : PsiAj ν χ A s j z = bkDot (merApply (Ay ν χ A s) (xj ν j z))
        (bkG (ageA ν s) (xj ν j z) ^ 2 • xj ν j z) := by
      rw [← bk_mgrad_pj ν s j z ha0]
      rfl
    have he0 : 0 ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    have hG2 := bkB4_G2_le (ageA ν s) ha1 (xj ν j z)
    have hMy : ‖merApply (Ay ν χ A s) (xj ν j z)‖ ≤ bkB4_Kc (Ay ν χ A s) * ‖xj ν j z‖ :=
      gp_merApply_norm_le _ _
    have hv1 : ‖PsiAj ν χ A s j z‖ ≤
        2 * ‖merApply (Ay ν χ A s) (xj ν j z)‖ *
          ‖bkG (ageA ν s) (xj ν j z) ^ 2 • xj ν j z‖ := by
      rw [hPsi, Real.norm_eq_abs]
      exact bkB4_dot_le _ _
    have hv3 : ‖bkG (ageA ν s) (xj ν j z) ^ 2 • xj ν j z‖ ≤
        Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) * ‖xj ν j z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right hG2 (norm_nonneg _)
    have hv4 : 2 * ‖merApply (Ay ν χ A s) (xj ν j z)‖ *
          ‖bkG (ageA ν s) (xj ν j z) ^ 2 • xj ν j z‖ ≤
        2 * (bkB4_Kc (Ay ν χ A s) * ‖xj ν j z‖) *
          (Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) * ‖xj ν j z‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hMy (by norm_num)) hv3 (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg hKc (norm_nonneg _)))
    have hfin : 2 * (bkB4_Kc (Ay ν χ A s) * ‖xj ν j z‖) *
          (Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) * ‖xj ν j z‖) ≤
        8 * bkB4_Kc (Ay ν χ A s) * bkMaj ν (ageA ν s) j z := by
      unfold bkMaj
      have ht2 := bkB4_sq_le ‖xj ν j z‖ (norm_nonneg _)
      have F1 := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hKc he0)
      have F2 : 0 ≤ bkB4_Kc (Ay ν χ A s) * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) *
          (1 + ‖xj ν j z‖) ^ 6 :=
        mul_nonneg (mul_nonneg hKc he0) (pow_nonneg (by linarith [norm_nonneg (xj ν j z)]) 6)
      nlinarith [F1, F2]
    exact hv1.trans (hv4.trans hfin)
  · have hg := (mgradPsiAjClosed ν χ A s j ha0).2 z
    have hgn : ‖mgrad (PsiAj ν χ A s j) z‖ ≤
        4 * bkB4_Kc (Ay ν χ A s) *
          ((1 + ‖xj ν j z‖) ^ 6 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))) := by
      rw [hg]
      exact bkB4_mgrad_norm _ _ ha1 _
    have hop : ‖fderiv ℝ (PsiAj ν χ A s j) z‖ ≤ 2 * ‖mgrad (PsiAj ν χ A s j) z‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      rw [bkB4_fderiv_apply, Real.norm_eq_abs]
      calc |bkDot v (mgrad (PsiAj ν χ A s j) z)|
          ≤ 2 * ‖v‖ * ‖mgrad (PsiAj ν χ A s j) z‖ := bkB4_dot_le _ _
        _ = 2 * ‖mgrad (PsiAj ν χ A s j) z‖ * ‖v‖ := by ring
    unfold bkMaj
    linarith [hop, hgn]

end UnforcedLeray.Short.PartIIIb.Concrete
