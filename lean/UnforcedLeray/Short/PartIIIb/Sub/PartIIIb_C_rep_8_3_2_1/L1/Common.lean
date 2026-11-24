import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.TermDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Hess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Shared analytic core for the Gaussian lattice sums (source 4963-4985, 4978)

Helpers for `L1`-`L4`: basis bounds for continuous linear maps on `ℝ × ℝ`, the Gaussian decay
of the profile `Vj ν s 0`, `pj ν s 0` (`td_domG`), its derivative bounds, and the shift identities
`Vj ν s j x = Vj ν s 0 (x - shiftVec (cOf ν) j)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open UnforcedLeray.Gaussian (shiftVec)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A continuous linear map on `ℝ × ℝ` is bounded by the sum of its two basis values. -/
theorem opNorm_le_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℝ × ℝ →L[ℝ] F) : ‖T‖ ≤ ‖T (ei 0)‖ + ‖T (ei 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    fun v => ?_
  have hv : v = v.1 • ei 0 + v.2 • ei 1 := by
    ext <;> simp [ei]
  have hTv : T v = v.1 • T (ei 0) + v.2 • T (ei 1) := by
    conv_lhs => rw [hv]
    simp [map_add, map_smul]
  rw [hTv]
  calc ‖v.1 • T (ei 0) + v.2 • T (ei 1)‖ ≤ ‖v.1 • T (ei 0)‖ + ‖v.2 • T (ei 1)‖ := norm_add_le _ _
    _ = |v.1| * ‖T (ei 0)‖ + |v.2| * ‖T (ei 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖T (ei 0)‖ + ‖v‖ * ‖T (ei 1)‖ := by
        have h1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
        have h2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
        gcongr
    _ = (‖T (ei 0)‖ + ‖T (ei 1)‖) * ‖v‖ := by ring

/-- `exp(u) ≥ (1+u)^4/24` for `u ≥ 0`. -/
theorem one_add_pow_four_le_exp {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) ^ 4 ≤ 24 * Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg hu 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u), mul_nonneg (mul_nonneg hu hu) (sq_nonneg u)]

/-- The Gaussian-times-cubic majorant: `(1+w)^3 e^{-w/(4a)} ≤ 24 (1+4a)^3`. -/
theorem quad_exp_decay {a : ℝ} (ha : 0 < a) {w : ℝ} (hw : 0 ≤ w) :
    (1 + w) ^ 3 * Real.exp (-w / (4 * a)) ≤ 24 * (1 + 4 * a) ^ 3 := by
  set u : ℝ := w / (4 * a) with hu_def
  have hu : 0 ≤ u := div_nonneg hw (by positivity)
  have hwu : w = 4 * a * u := by rw [hu_def]; field_simp
  have hneg : -w / (4 * a) = -u := by rw [hu_def, neg_div]
  rw [hneg, Real.exp_neg]
  have h1 : 1 + w ≤ (1 + 4 * a) * (1 + u) := by rw [hwu]; nlinarith
  have h2 : (1 + w) ^ 3 ≤ (1 + 4 * a) ^ 3 * (1 + u) ^ 3 := by
    have := pow_le_pow_left₀ (by linarith) h1 3
    simpa [mul_pow] using this
  have h3 : (1 + u) ^ 3 ≤ 24 * Real.exp u := by
    have := one_add_pow_four_le_exp hu
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + u) 3]
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hpos : 0 < (1 + 4 * a) ^ 3 := by positivity
  rw [mul_inv_le_iff₀ hE]
  calc (1 + w) ^ 3 ≤ (1 + 4 * a) ^ 3 * (1 + u) ^ 3 := h2
    _ ≤ (1 + 4 * a) ^ 3 * (24 * Real.exp u) := mul_le_mul_of_nonneg_left h3 hpos.le
    _ = 24 * (1 + 4 * a) ^ 3 * Real.exp u := by ring

/-- Decay of `(1+w)^2 e^{-w/(4a)}` at the Euclidean-squared level (cf. `td_domG`). -/
theorem td_domG_decay (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) :
    (1 + |x.1 - j * cOf ν|) ^ 2 * td_domG ν s j x ≤ 48 * (1 + 4 * ageA ν s) ^ 3 := by
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  set w : ℝ := sq2 (xj ν j x) with hw_def
  have hw0 : 0 ≤ w := hu_sq2_nonneg _
  set t : ℝ := |x.1 - j * cOf ν| with ht_def
  have ht2 : t ^ 2 ≤ w := by
    rw [ht_def, sq_abs, hw_def]
    simp only [sq2, xj]
    nlinarith [sq_nonneg x.2]
  have ht0 : 0 ≤ t := abs_nonneg _
  have hkey := quad_exp_decay ha hw0
  unfold td_domG
  rw [← hw_def]
  have h1 : (1 + t) ^ 2 ≤ 2 * (1 + w) := by nlinarith [sq_nonneg (t - 1)]
  have hE : 0 ≤ Real.exp (-w / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hq : 0 ≤ (1 + w) ^ 2 := by positivity
  calc (1 + t) ^ 2 * ((1 + w) ^ 2 * Real.exp (-w / (4 * ageA ν s)))
      = ((1 + t) ^ 2 * (1 + w) ^ 2) * Real.exp (-w / (4 * ageA ν s)) := by ring
    _ ≤ (2 * (1 + w) * (1 + w) ^ 2) * Real.exp (-w / (4 * ageA ν s)) := by
        gcongr
    _ = 2 * ((1 + w) ^ 3 * Real.exp (-w / (4 * ageA ν s))) := by ring
    _ ≤ 2 * (24 * (1 + 4 * ageA ν s) ^ 3) := by gcongr
    _ = 48 * (1 + 4 * ageA ν s) ^ 3 := by ring

/-- A translate bound with exponent `-2` from a pointwise bound. -/
theorem le_rpow_neg_two {X K t : ℝ} (hK : 0 ≤ K) (h : X * (1 + |t|) ^ 2 ≤ K) :
    X ≤ K * (1 + |t|) ^ (-(2 : ℝ)) := by
  have hp : 0 < (1 + |t|) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  exact h

/-! ### Profile bounds for `V_j` and `p_j` (uniform in `j`, ν, s > 0) -/

theorem ageA_ge_one {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 1 ≤ ageA ν s := by
  unfold ageA; nlinarith [mul_pos hν hs]

theorem ageA_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 < ageA ν s :=
  lt_of_lt_of_le one_pos (ageA_ge_one hν hs)

/-- The shift identity for `V_j`: translation by `(jc, 0)` of the profile `Vj ν s 0`. -/
private theorem Vj_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j x = Vj ν s 0 (x - shiftVec (cOf ν) j) := by
  simp [Vj, xj, shiftVec, sq2]

/-- The shift identity for `p_j`. -/
theorem pj_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    pj ν s j x = pj ν s 0 (x - shiftVec (cOf ν) j) := by
  simp [pj, xj, shiftVec, sq2]

theorem td_decay0 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    (1 + |z.1|) ^ 2 * td_domG ν s 0 z ≤ 48 * (1 + 4 * ageA ν s) ^ 3 := by
  have h := td_domG_decay ν s hν hs 0 z
  simpa using h

/-- The uniform profile majorant `td_domG ν s 0 z ≤ K (1+|z₁|)^{-2}`, `K = 48(1+4a)³`. -/
theorem td_G_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    td_domG ν s 0 z ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) :=
  le_rpow_neg_two (by have := ageA_pos hν hs; positivity) (by rw [mul_comm]; exact td_decay0 hν hs z)

theorem vj_norm_le_G {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) :
    ‖Vj ν s j x‖ ≤ td_domG ν s j x :=
  td_vj_norm ν s (ageA_ge_one hν hs) j x

theorem pj_norm_le_G {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) :
    ‖pj ν s j x‖ ≤ td_domG ν s j x := by
  have ha : 0 < ageA ν s := ageA_pos hν hs
  have ha1 : 1 ≤ ageA ν s := ageA_ge_one hν hs
  have hw : 0 ≤ sq2 (xj ν j x) := hu_sq2_nonneg _
  unfold pj td_domG
  rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hA : (ageA ν s ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hE : Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) ≤
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left hw (by positivity) (by linarith)
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hq : 1 ≤ (1 + sq2 (xj ν j x)) ^ 2 := one_le_pow₀ (by linarith)
  calc (ageA ν s ^ 3)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s))
      ≤ 1 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
        apply mul_le_mul hA hE (by positivity) zero_le_one
    _ ≤ (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
        rw [one_mul]; exact le_mul_of_one_le_left hE0 hq

/-- `|hsL| ≤ |x_j|` (sup norm) for `a ≥ 1`. -/
theorem abs_hsL_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (b : Fin 2) (y : ℝ × ℝ) :
    |hsL ν s j b y| ≤ ‖xj ν j y‖ := by
  have ha1 : 1 ≤ ageA ν s := ageA_ge_one hν hs
  have hpos : 0 < 4 * ageA ν s := by linarith
  have e1 : |(ei b).1| ≤ 1 := by fin_cases b <;> simp [ei]
  have e2 : |(ei b).2| ≤ 1 := by fin_cases b <;> simp [ei]
  have hx1 : |(xj ν j y).1| ≤ ‖xj ν j y‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le _
  have hx2 : |(xj ν j y).2| ≤ ‖xj ν j y‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le _
  have hn : 0 ≤ ‖xj ν j y‖ := norm_nonneg _
  have hnum : |2 * (xj ν j y).1 * (ei b).1 + 2 * (xj ν j y).2 * (ei b).2| ≤ 4 * ‖xj ν j y‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    norm_num
    nlinarith [abs_nonneg (xj ν j y).1, abs_nonneg (xj ν j y).2, abs_nonneg (ei b).1,
      abs_nonneg (ei b).2]
  unfold hsL
  rw [abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith

/-- The explicit first derivative bound `‖∂_b V_j‖ ≤ td_domG`. -/
theorem hsG_norm_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (b : Fin 2) (y : ℝ × ℝ) :
    ‖hsG ν s j b y‖ ≤ td_domG ν s j y := by
  have ha1 : 1 ≤ ageA ν s := ageA_ge_one hν hs
  have ha : 0 < ageA ν s := ageA_pos hν hs
  have hE0 : 0 ≤ hsE ν s j y := by unfold hsE; positivity
  have hEle : hsE ν s j y ≤ Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) := by
    unfold hsE
    have hinv : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
    exact mul_le_of_le_one_left (Real.exp_pos _).le hinv
  have hn : 0 ≤ ‖xj ν j y‖ := norm_nonneg _
  have hsq : ‖xj ν j y‖ ^ 2 ≤ sq2 (xj ν j y) := hu_norm_sq_le _
  have hL := abs_hsL_le hν hs j b y
  unfold hsG
  calc ‖hsE ν s j y • Jrot (ei b) + (hsE ν s j y * hsL ν s j b y) • Jrot (xj ν j y)‖
      ≤ ‖hsE ν s j y • Jrot (ei b)‖ + ‖(hsE ν s j y * hsL ν s j b y) • Jrot (xj ν j y)‖ :=
        norm_add_le _ _
    _ = hsE ν s j y * ‖ei b‖ + |hsE ν s j y * hsL ν s j b y| * ‖xj ν j y‖ := by
        rw [norm_smul, norm_smul, gp_jrot_norm, gp_jrot_norm, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hE0]
    _ ≤ hsE ν s j y * 1 + hsE ν s j y * ‖xj ν j y‖ * ‖xj ν j y‖ := by
        gcongr
        · exact hs_ei_norm_le b
        · rw [abs_mul, abs_of_nonneg hE0]
          exact mul_le_mul_of_nonneg_left hL hE0
    _ ≤ hsE ν s j y * (1 + sq2 (xj ν j y)) := by
        nlinarith [hE0]
    _ ≤ Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j y)) :=
        mul_le_mul_of_nonneg_right hEle (by linarith [hu_sq2_nonneg (xj ν j y)])
    _ ≤ (1 + sq2 (xj ν j y)) ^ 2 * Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) := by
        have hE' : 0 ≤ Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) := (Real.exp_pos _).le
        have hsq1 : (1 + sq2 (xj ν j y)) ≤ (1 + sq2 (xj ν j y)) ^ 2 := by
          nlinarith [hu_sq2_nonneg (xj ν j y)]
        calc Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j y))
            ≤ Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j y)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq1 hE'
          _ = (1 + sq2 (xj ν j y)) ^ 2 * Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) := by ring
    _ = td_domG ν s j y := by unfold td_domG; ring

/-! ### Smoothness and derivative bounds of the profiles -/

theorem vj0_contDiff (ν s : ℝ) : ContDiff ℝ 2 (Vj ν s 0) := by
  unfold Vj xj Jrot sq2
  fun_prop

theorem pj0_contDiff (ν s : ℝ) : ContDiff ℝ 2 (pj ν s 0) := by
  unfold pj xj sq2
  fun_prop

/-- Evaluation at a constant vector commutes with the derivative of a CLM-valued map. -/
theorem fderiv_apply_const_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × ℝ → (ℝ × ℝ →L[ℝ] F)} (hG : Differentiable ℝ G) (w v x : ℝ × ℝ) :
    fderiv ℝ (fun y => G y w) x v = fderiv ℝ G x v w := by
  have h := fderiv_clm_apply (hG x) (differentiableAt_const w)
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h
  rw [h]
  rfl

/-- The constant `C16 = 16 · 48 (1+4a)³` in all profile bounds. -/
def C16 (ν s : ℝ) : ℝ := 16 * (48 * (1 + 4 * ageA ν s) ^ 3)

theorem C16_nonneg {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 ≤ C16 ν s := by
  have := ageA_pos hν hs
  unfold C16; positivity

theorem prof_v0 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖Vj ν s 0 z‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h1 := vj_norm_le_G hν hs 0 z
  have h2 := td_G_le hν hs z
  have hP : 0 ≤ (1 + |z.1|) ^ (-(2 : ℝ)) := by positivity
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  unfold C16
  nlinarith

theorem prof_p0 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖pj ν s 0 z‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h1 := pj_norm_le_G hν hs 0 z
  have h2 := td_G_le hν hs z
  have hP : 0 ≤ (1 + |z.1|) ^ (-(2 : ℝ)) := by positivity
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  unfold C16
  nlinarith

theorem vj0_fderiv_ei_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (b : Fin 2) (z : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s 0) z (ei b)‖ ≤ td_domG ν s 0 z := by
  rw [hs_eq]
  exact hsG_norm_le hν hs 0 b z

theorem prof_v1 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s 0) z‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h0 := vj0_fderiv_ei_le hν hs 0 z
  have h1 := vj0_fderiv_ei_le hν hs 1 z
  have h2 := td_G_le hν hs z
  have hP : 0 ≤ (1 + |z.1|) ^ (-(2 : ℝ)) := by positivity
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  refine (opNorm_le_basis _).trans ?_
  unfold C16
  nlinarith

theorem pj0_fderiv_ei_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (b : Fin 2) (z : ℝ × ℝ) :
    ‖fderiv ℝ (pj ν s 0) z (ei b)‖ ≤ 2 * td_domG ν s 0 z := by
  have hm := td_mgrad ν s hν hs 0 z
  have hc : ‖fderiv ℝ (pj ν s 0) z (ei b)‖ ≤ ‖mgrad (pj ν s 0) z‖ := by
    fin_cases b
    · have := norm_fst_le (mgrad (pj ν s 0) z)
      simpa [mgrad] using this
    · have := norm_snd_le (mgrad (pj ν s 0) z)
      simpa [mgrad] using this
  linarith

theorem prof_p1 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖fderiv ℝ (pj ν s 0) z‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h0 := pj0_fderiv_ei_le hν hs 0 z
  have h1 := pj0_fderiv_ei_le hν hs 1 z
  have h2 := td_G_le hν hs z
  have hP : 0 ≤ (1 + |z.1|) ^ (-(2 : ℝ)) := by positivity
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  refine (opNorm_le_basis _).trans ?_
  unfold C16
  nlinarith

/-- The second derivative as a CLM-valued map, bounded through its meridional entries. -/
theorem vj0_hess_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖fderiv ℝ (fderiv ℝ (Vj ν s 0)) z‖ ≤ 16 * td_domG ν s 0 z := by
  have hG : Differentiable ℝ (fderiv ℝ (Vj ν s 0)) :=
    ((vj0_contDiff ν s).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine (opNorm_le_basis _).trans ?_
  have hA : ∀ a : Fin 2, ‖fderiv ℝ (fderiv ℝ (Vj ν s 0)) z (ei a)‖ ≤ 8 * td_domG ν s 0 z := by
    intro a
    refine (opNorm_le_basis _).trans ?_
    have e : ∀ b : Fin 2, fderiv ℝ (fderiv ℝ (Vj ν s 0)) z (ei a) (ei b) =
        fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) y (ei b)) z (ei a) :=
      fun b => (fderiv_apply_const_eq hG (ei b) (ei a) z).symm
    rw [e 0, e 1]
    have h0 := td_hess ν s hν hs 0 z a 0
    have h1 := td_hess ν s hν hs 0 z a 1
    linarith
  have := hA 0
  have := hA 1
  linarith

/-! ### Lattice sums: shifted forms and summability -/

theorem cOf_ne_zero {ν : ℝ} (hν : 0 < ν) : cOf ν ≠ 0 := by
  unfold cOf; have : 0 < ν ^ 2 := by positivity
  exact (inv_pos.2 this).ne'

theorem gaussV_fun {ν s : ℝ} : gaussV ν s = fun y => ∑' n : ℤ, Vj ν s 0 (y - shiftVec (cOf ν) n) := by
  funext y
  unfold gaussV
  exact tsum_congr fun j => Vj_shift ν s j y

theorem gaussP_fun {ν s : ℝ} : gaussP ν s = fun y => ∑' n : ℤ, pj ν s 0 (y - shiftVec (cOf ν) n) := by
  funext y
  unfold gaussP
  exact tsum_congr fun j => pj_shift ν s j y

theorem td_le_translate {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) :
    td_domG ν s j x ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |x.1 - j * cOf ν|) ^ (-(2 : ℝ)) :=
  le_rpow_neg_two (by have := ageA_pos hν hs; positivity)
    (by rw [mul_comm]; exact td_domG_decay ν s hν hs j x)

theorem summable_td_translate {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => td_domG ν s j x) :=
  Summable.of_nonneg_of_le (fun j => by unfold td_domG; have := ageA_pos hν hs; positivity)
    (fun j => td_le_translate hν hs j x)
    ((UnforcedLeray.Gaussian.summable_translate (by norm_num : (1 : ℝ) < 2) (cOf_ne_zero hν) x.1).mul_left _)

theorem summable_vj_translate {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => Vj ν s j x) :=
  Summable.of_norm_bounded (summable_td_translate hν hs x) (fun j => vj_norm_le_G hν hs j x)

theorem summable_pj_translate {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => pj ν s j x) :=
  Summable.of_norm_bounded (summable_td_translate hν hs x) (fun j => pj_norm_le_G hν hs j x)

theorem summable_mgrad_pj_translate {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => mgrad (pj ν s j) x) :=
  Summable.of_norm_bounded
    ((summable_td_translate hν hs x).mul_left 2)
    (fun j => (td_mgrad ν s hν hs j x))

theorem prof_v2 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖fderiv ℝ (fderiv ℝ (Vj ν s 0)) z‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h1 := vj0_hess_le hν hs z
  have h2 := td_G_le hν hs z
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  unfold C16
  nlinarith

theorem gaussV_periodize {ν s : ℝ} :
    gaussV ν s = UnforcedLeray.Gaussian.periodize (cOf ν) (Vj ν s 0) := by
  rw [gaussV_fun]; funext y; rw [UnforcedLeray.Gaussian.periodize_eq]

/-! ### Translates of derivatives -/

/-- Derivative of a translate: `Vj ν s n` is the translate of `Vj ν s 0`. -/
theorem fderiv_Vj_shift_rep8 {ν s : ℝ} (n : ℤ) (y : ℝ × ℝ) :
    fderiv ℝ (Vj ν s n) y = fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) := by
  rw [show Vj ν s n = fun y => Vj ν s 0 (y - shiftVec (cOf ν) n) from funext (Vj_shift ν s n),
    fderiv_comp_sub]

/-- Summability of the derivatives of a translate family under a pointwise derivative bound. -/
theorem summable_fderiv_translates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : ℝ × ℝ → F} {C c : ℝ} (hc : c ≠ 0)
    (h1 : ∀ z, ‖fderiv ℝ g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) (x : ℝ × ℝ) :
    Summable (fun n : ℤ => fderiv ℝ (fun y => g (y - shiftVec c n)) x) := by
  refine Summable.of_norm_bounded
    ((UnforcedLeray.Gaussian.summable_translate (by norm_num : (1 : ℝ) < 2) hc x.1).mul_left C)
    (fun n => ?_)
  rw [fderiv_comp_sub]
  have h := h1 (x - shiftVec c n)
  have e : (x - shiftVec c n).1 = x.1 - n * c := by simp [shiftVec]
  rw [e] at h
  exact h

theorem prof_Hb0 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (b : Fin 2) (z : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s 0) z (ei b)‖ ≤ C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h1 := vj0_fderiv_ei_le hν hs b z
  have h2 := td_G_le hν hs z
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  unfold C16
  nlinarith

theorem prof_Hb1 {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (b : Fin 2) (z : ℝ × ℝ) :
    ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) y (ei b)) z‖ ≤
      C16 ν s * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have h0 := td_hess ν s hν hs 0 z 0 b
  have h1 := td_hess ν s hν hs 0 z 1 b
  have h2 := td_G_le hν hs z
  have hK : 0 ≤ 48 * (1 + 4 * ageA ν s) ^ 3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    have := ageA_pos hν hs
    positivity
  refine (opNorm_le_basis _).trans ?_
  unfold C16
  nlinarith

theorem hb_diff {ν s : ℝ} (b : Fin 2) :
    Differentiable ℝ (fun y => fderiv ℝ (Vj ν s 0) y (ei b)) := by
  have hG : Differentiable ℝ (fderiv ℝ (Vj ν s 0)) :=
    ((vj0_contDiff ν s).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  intro y
  exact (hG y).clm_apply (differentiableAt_const _)

end UnforcedLeray.Short.PartIIIb.Concrete
