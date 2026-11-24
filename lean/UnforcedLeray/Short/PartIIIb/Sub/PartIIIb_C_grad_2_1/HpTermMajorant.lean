import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/grad/2/1/1`: the derivative majorant `HpTermMajorant`

Source `the November 2 reference manuscript` 4973-4980.
With `M = A^y_mer`, `J = Jrot`, `a = 1 + νs`, `P_j(w) = (a²)⁻¹ e^{-|x_j|²/(4a)}`, the lattice
term `M V_j(w) - DV_j(w)(M x_j(w))` equals `P_j(w) • Ψ(x_j w)` with
`Ψ(y) = M J y - J M y + (y·My)/(2a) • J y`. Its `w`-derivative is bounded by
`10 ‖M‖ P_j (1+|y|)^4 ‖v‖`, and the Gaussian majorant is summable over `j`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sum of absolute meridional entries (operator bound of `merApply`). -/
def hp4K (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

lemma hp4K_nonneg (M : Mat3) : 0 ≤ hp4K M := by
  unfold hp4K; positivity

lemma hp4_merApply_le (M : Mat3) (w : ℝ × ℝ) : ‖merApply M w‖ ≤ hp4K M * ‖w‖ := by
  unfold hp4K; exact gp_merApply_norm_le M w

lemma hp4_fst_le (w : ℝ × ℝ) : |w.1| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]; exact norm_fst_le w

lemma hp4_snd_le (w : ℝ × ℝ) : |w.2| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]; exact norm_snd_le w

lemma hp4_norm_le_abs (w : ℝ × ℝ) : ‖w‖ ≤ |w.1| + |w.2| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))

lemma hp4_bil (w u : ℝ × ℝ) : |w.1 * u.1 + w.2 * u.2| ≤ 2 * (‖w‖ * ‖u‖) := by
  have p1 : |w.1 * u.1| ≤ ‖w‖ * ‖u‖ := by
    rw [abs_mul]; exact mul_le_mul (hp4_fst_le w) (hp4_fst_le u) (abs_nonneg _) (norm_nonneg _)
  have p2 : |w.2 * u.2| ≤ ‖w‖ * ‖u‖ := by
    rw [abs_mul]; exact mul_le_mul (hp4_snd_le w) (hp4_snd_le u) (abs_nonneg _) (norm_nonneg _)
  calc |w.1 * u.1 + w.2 * u.2| ≤ |w.1 * u.1| + |w.2 * u.2| := abs_add_le _ _
    _ ≤ 2 * (‖w‖ * ‖u‖) := by linarith

lemma hp4_half_le (X a : ℝ) (ha : 1 ≤ a) : |X / (2 * a)| ≤ |X| := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
  exact div_le_self (abs_nonneg _) (by linarith)

lemma hp4_abs_le (p q : ℝ) (h : |p - q| < 1) : |p| ≤ |q| + 1 := by
  have h' := abs_lt.mp h
  exact abs_le.mpr ⟨by linarith [neg_abs_le q], by linarith [le_abs_self q]⟩

lemma hp4_add_pow4 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : (A + B) ^ 4 ≤ 8 * (A ^ 4 + B ^ 4) := by
  have h : 0 ≤ (A - B) ^ 2 * (7 * A ^ 2 + 10 * A * B + 7 * B ^ 2) := by
    apply mul_nonneg (sq_nonneg _)
    have := mul_nonneg hA hB
    nlinarith [sq_nonneg A, sq_nonneg B]
  nlinarith [h]

lemma hp4_poly4_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h4 := gp_gauss_pow_summable t α c hα hc 4
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.mul_left (8 * (1 + |t|) ^ 4)).add (h4.mul_left (8 * c ^ 4)))
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  have hjc : |(j : ℝ) * c| = |(j : ℝ)| * c := by rw [abs_mul, abs_of_pos hc]
  have hu : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
    rw [← hjc, abs_le]
    constructor <;> linarith [neg_abs_le t, le_abs_self t, neg_abs_le ((j : ℝ) * c), le_abs_self ((j : ℝ) * c)]
  have hB : 1 + |t - (j : ℝ) * c| ≤ (1 + |t|) + c * |(j : ℝ)| := by linarith [hu]
  have hpow := pow_le_pow_left₀ (by positivity) hB 4
  have h8 := hp4_add_pow4 (1 + |t|) (c * |(j : ℝ)|) (by positivity) (by positivity)
  calc (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ (8 * ((1 + |t|) ^ 4 + (c * |(j : ℝ)|) ^ 4)) * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (hpow.trans h8) hE
    _ = 8 * (1 + |t|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + 8 * c ^ 4 * (|(j : ℝ)| ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

/-! ## Definitions of the closed form -/

/-- Scalar quadratic form `y · (M y)`. -/
def hp4Q (M : Mat3) (y : ℝ × ℝ) : ℝ := y.1 * (merApply M y).1 + y.2 * (merApply M y).2

/-- Polarized form `v · (M y) + y · (M v)`, the derivative of `hp4Q` along `v`. -/
def hp4Qd (M : Mat3) (y v : ℝ × ℝ) : ℝ :=
  v.1 * (merApply M y).1 + v.2 * (merApply M y).2 + (y.1 * (merApply M v).1 + y.2 * (merApply M v).2)

/-- `Ψ(y) = M J y - J M y + (y·My)/(2a) J y`. -/
def hp4Psi (ν s : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ × ℝ :=
  (merApply M (Jrot y) - Jrot (merApply M y)) + (hp4Q M y / (2 * ageA ν s)) • Jrot y

/-- Directional derivative of `Ψ` at `y` along `v`. -/
def hp4Psi1 (ν s : ℝ) (M : Mat3) (y v : ℝ × ℝ) : ℝ × ℝ :=
  (merApply M (Jrot v) - Jrot (merApply M v))
    + ((hp4Qd M y v / (2 * ageA ν s)) • Jrot y + (hp4Q M y / (2 * ageA ν s)) • Jrot v)

/-- Scalar prefactor `(a²)⁻¹ e^{-|x_j|²/(4a)}`. -/
def hp4P (ν s : ℝ) (j : ℤ) (w : ℝ × ℝ) : ℝ :=
  (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j w)) / (4 * ageA ν s))

lemma hp4_xj_add (ν : ℝ) (j : ℤ) (z v : ℝ × ℝ) (t : ℝ) :
    xj ν j (z + t • v) = xj ν j z + t • v := by
  ext <;> simp [xj] <;> ring

/-- The closed form of the lattice term. -/
lemma hp4_eq (ν s : ℝ) (j : ℤ) (M : Mat3) :
    (fun w : ℝ × ℝ => merApply M (Vj ν s j w) - fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w)))
      = fun w => hp4P ν s j w • hp4Psi ν s M (xj ν j w) := by
  funext w
  rw [gp_fderiv_Vj]
  ext <;> simp only [Vj, hp4P, hp4Psi, hp4Q, merApply, Jrot, xj, sq2, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

lemma hp4_diff (ν s : ℝ) (j : ℤ) (M : Mat3) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w => hp4P ν s j w • hp4Psi ν s M (xj ν j w)) z := by
  simp only [hp4P, hp4Psi, hp4Q, merApply, Jrot, xj, sq2]
  fun_prop

lemma hp4_hasDeriv_affine (A B : ℝ × ℝ) (f : ℝ → ℝ × ℝ) (hf : ∀ t, f t = A + t • B) :
    HasDerivAt f B 0 := by
  have e : f = fun t => A + t • B := funext hf
  rw [e]
  have h := ((hasDerivAt_id (0:ℝ)).smul_const B).const_add A
  simpa using h

lemma hp4_quad_deriv (M : Mat3) (p v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (p + t • v).1 * (merApply M (p + t • v)).1
        + (p + t • v).2 * (merApply M (p + t • v)).2)
      (hp4Qd M p v) 0 := by
  have e : (fun t : ℝ => (p + t • v).1 * (merApply M (p + t • v)).1
        + (p + t • v).2 * (merApply M (p + t • v)).2)
      = fun t : ℝ => (hp4Q M p + t * hp4Qd M p v)
          + (t * t) * (v.1 * (merApply M v).1 + v.2 * (merApply M v).2) := by
    funext t
    simp only [hp4Q, hp4Qd, merApply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [e]
  have h1 := ((hasDerivAt_id (0:ℝ)).mul_const (hp4Qd M p v)).const_add (hp4Q M p)
  have h2 := ((hasDerivAt_id (0:ℝ)).mul (hasDerivAt_id (0:ℝ))).mul_const
    (v.1 * (merApply M v).1 + v.2 * (merApply M v).2)
  refine (h1.add h2).congr_deriv ?_
  simp

lemma hp4_psi_line_gen (ν s : ℝ) (M : Mat3) (y v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => hp4Psi ν s M (y + t • v)) (hp4Psi1 ν s M y v) 0 := by
  unfold hp4Psi hp4Psi1
  have hA := hp4_hasDeriv_affine (merApply M (Jrot y) - Jrot (merApply M y))
    (merApply M (Jrot v) - Jrot (merApply M v))
    (fun t : ℝ => merApply M (Jrot (y + t • v)) - Jrot (merApply M (y + t • v)))
    (fun t => by ext <;> simp [merApply, Jrot] <;> ring)
  have hB := hp4_hasDeriv_affine (Jrot y) (Jrot v) (fun t : ℝ => Jrot (y + t • v))
    (fun t => by ext <;> simp [Jrot] <;> ring)
  have hQ := (hp4_quad_deriv M y v).div_const (2 * ageA ν s)
  refine (hA.add (hQ.smul hB)).congr_deriv ?_
  simp only [zero_smul, add_zero]
  congr 1
  exact add_comm _ _

lemma hp4_line (ν s : ℝ) (j : ℤ) (M : Mat3) (z v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => hp4P ν s j (z + t • v) • hp4Psi ν s M (xj ν j (z + t • v)))
      ((hp4P ν s j z * (-(2 * (xj ν j z).1 * v.1 + 2 * (xj ν j z).2 * v.2) / (4 * ageA ν s)))
          • hp4Psi ν s M (xj ν j z)
        + hp4P ν s j z • hp4Psi1 ν s M (xj ν j z) v) 0 := by
  have hP : HasDerivAt (fun t : ℝ => hp4P ν s j (z + t • v))
      (hp4P ν s j z * (-(2 * (xj ν j z).1 * v.1 + 2 * (xj ν j z).2 * v.2) / (4 * ageA ν s))) 0 := by
    have h := (gp_exp_line ν s j z v).const_mul ((ageA ν s ^ 2)⁻¹)
    unfold hp4P
    exact h.congr_deriv (by ring)
  have hΨ : HasDerivAt (fun t : ℝ => hp4Psi ν s M (xj ν j (z + t • v)))
      (hp4Psi1 ν s M (xj ν j z) v) 0 := by
    simp only [hp4_xj_add]
    exact hp4_psi_line_gen ν s M (xj ν j z) v
  refine (hP.smul hΨ).congr_deriv ?_
  simp only [zero_smul, add_zero]
  exact add_comm _ _

lemma hp4_Q_le (M : Mat3) (y : ℝ × ℝ) : |hp4Q M y| ≤ 2 * hp4K M * ‖y‖ ^ 2 := by
  have hK := hp4K_nonneg M
  have hr : 0 ≤ ‖y‖ := norm_nonneg y
  have b := hp4_bil y (merApply M y)
  have e : ‖y‖ * ‖merApply M y‖ ≤ ‖y‖ * (hp4K M * ‖y‖) :=
    mul_le_mul_of_nonneg_left (hp4_merApply_le M y) hr
  unfold hp4Q
  nlinarith

lemma hp4_psi_bound (ν s : ℝ) (ha : 1 ≤ ageA ν s) (M : Mat3) (y : ℝ × ℝ) :
    ‖hp4Psi ν s M y‖ ≤ 4 * hp4K M * (1 + ‖y‖) ^ 3 := by
  have hK := hp4K_nonneg M
  have hr : 0 ≤ ‖y‖ := norm_nonneg y
  have hJy : ‖Jrot y‖ = ‖y‖ := gp_jrot_norm y
  have hA : ‖merApply M (Jrot y) - Jrot (merApply M y)‖ ≤ 2 * hp4K M * ‖y‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := hp4_merApply_le M (Jrot y)
    have h2 := hp4_merApply_le M y
    rw [hJy] at h1
    rw [gp_jrot_norm]
    linarith
  have hJ : ‖(hp4Q M y / (2 * ageA ν s)) • Jrot y‖ ≤ 2 * hp4K M * ‖y‖ ^ 3 := by
    rw [norm_smul, hJy, Real.norm_eq_abs]
    calc |hp4Q M y / (2 * ageA ν s)| * ‖y‖
        ≤ (2 * hp4K M * ‖y‖ ^ 2) * ‖y‖ :=
          mul_le_mul ((hp4_half_le _ _ ha).trans (hp4_Q_le M y)) le_rfl hr
            (mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg _))
      _ = 2 * hp4K M * ‖y‖ ^ 3 := by ring
  unfold hp4Psi
  refine (norm_add_le _ _).trans ?_
  have hpoly : ‖y‖ + ‖y‖ ^ 3 ≤ 2 * (1 + ‖y‖) ^ 3 := by
    nlinarith [pow_nonneg hr 2, pow_nonneg hr 3]
  nlinarith [mul_le_mul_of_nonneg_left hpoly hK]

lemma hp4_dpsi_bound (ν s : ℝ) (ha : 1 ≤ ageA ν s) (M : Mat3) (y v : ℝ × ℝ) :
    ‖hp4Psi1 ν s M y v‖ ≤ 6 * hp4K M * (1 + ‖y‖) ^ 2 * ‖v‖ := by
  have hK := hp4K_nonneg M
  have hr : 0 ≤ ‖y‖ := norm_nonneg y
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have hJv : ‖Jrot v‖ = ‖v‖ := gp_jrot_norm v
  have hJy : ‖Jrot y‖ = ‖y‖ := gp_jrot_norm y
  have hA : ‖merApply M (Jrot v) - Jrot (merApply M v)‖ ≤ 2 * hp4K M * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := hp4_merApply_le M (Jrot v)
    have h2 := hp4_merApply_le M v
    rw [hJv] at h1
    rw [gp_jrot_norm]
    linarith
  have hQd : |hp4Qd M y v| ≤ 4 * hp4K M * ‖y‖ * ‖v‖ := by
    unfold hp4Qd
    refine (abs_add_le _ _).trans ?_
    have b1 := hp4_bil v (merApply M y)
    have b2 := hp4_bil y (merApply M v)
    have e1 : ‖v‖ * ‖merApply M y‖ ≤ ‖v‖ * (hp4K M * ‖y‖) :=
      mul_le_mul_of_nonneg_left (hp4_merApply_le M y) hv
    have e2 : ‖y‖ * ‖merApply M v‖ ≤ ‖y‖ * (hp4K M * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hp4_merApply_le M v) hr
    nlinarith
  have hT1 : ‖(hp4Qd M y v / (2 * ageA ν s)) • Jrot y‖ ≤ 4 * hp4K M * ‖y‖ ^ 2 * ‖v‖ := by
    rw [norm_smul, hJy, Real.norm_eq_abs]
    calc |hp4Qd M y v / (2 * ageA ν s)| * ‖y‖
        ≤ (4 * hp4K M * ‖y‖ * ‖v‖) * ‖y‖ :=
          mul_le_mul ((hp4_half_le _ _ ha).trans hQd) le_rfl hr
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hr) hv)
      _ = 4 * hp4K M * ‖y‖ ^ 2 * ‖v‖ := by ring
  have hT2 : ‖(hp4Q M y / (2 * ageA ν s)) • Jrot v‖ ≤ 2 * hp4K M * ‖y‖ ^ 2 * ‖v‖ := by
    rw [norm_smul, hJv, Real.norm_eq_abs]
    calc |hp4Q M y / (2 * ageA ν s)| * ‖v‖
        ≤ (2 * hp4K M * ‖y‖ ^ 2) * ‖v‖ :=
          mul_le_mul ((hp4_half_le _ _ ha).trans (hp4_Q_le M y)) le_rfl hv
            (mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg _))
      _ = 2 * hp4K M * ‖y‖ ^ 2 * ‖v‖ := by ring
  unfold hp4Psi1
  have hsum := norm_add_le ((hp4Qd M y v / (2 * ageA ν s)) • Jrot y)
    ((hp4Q M y / (2 * ageA ν s)) • Jrot v)
  have htot := norm_add_le (merApply M (Jrot v) - Jrot (merApply M v))
    ((hp4Qd M y v / (2 * ageA ν s)) • Jrot y + (hp4Q M y / (2 * ageA ν s)) • Jrot v)
  have hsq1 : (1:ℝ) ≤ (1 + ‖y‖) ^ 2 := by nlinarith
  have hsq2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hK hv) (sub_nonneg.2 hsq2), mul_nonneg (mul_nonneg hK hv) hr,
    mul_nonneg hK hv]

lemma hp4_line_bound (ν s : ℝ) (j : ℤ) (ha : 1 ≤ ageA ν s) (M : Mat3) (z v : ℝ × ℝ) :
    ‖(hp4P ν s j z * (-(2 * (xj ν j z).1 * v.1 + 2 * (xj ν j z).2 * v.2) / (4 * ageA ν s)))
          • hp4Psi ν s M (xj ν j z)
        + hp4P ν s j z • hp4Psi1 ν s M (xj ν j z) v‖
      ≤ 10 * hp4K M * hp4P ν s j z * (1 + ‖xj ν j z‖) ^ 4 * ‖v‖ := by
  have hK := hp4K_nonneg M
  have hr : 0 ≤ ‖xj ν j z‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have ha0 : 0 < ageA ν s := by linarith
  have hP0 : 0 ≤ hp4P ν s j z := by unfold hp4P; positivity
  have hc : |-(2 * (xj ν j z).1 * v.1 + 2 * (xj ν j z).2 * v.2) / (4 * ageA ν s)|
      ≤ ‖xj ν j z‖ * ‖v‖ := by
    refine (gp_c1_abs (xj ν j z) v (ageA ν s) ha0).trans ?_
    exact div_le_self (mul_nonneg hr hv) ha
  have hcA : ‖(hp4P ν s j z * (-(2 * (xj ν j z).1 * v.1 + 2 * (xj ν j z).2 * v.2)
        / (4 * ageA ν s))) • hp4Psi ν s M (xj ν j z)‖
      ≤ hp4P ν s j z * (‖xj ν j z‖ * ‖v‖) * (4 * hp4K M * (1 + ‖xj ν j z‖) ^ 3) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc hP0) (hp4_psi_bound ν s ha M _) (norm_nonneg _)
      (mul_nonneg hP0 (mul_nonneg hr hv))
  have hdA : ‖hp4P ν s j z • hp4Psi1 ν s M (xj ν j z) v‖
      ≤ hp4P ν s j z * (6 * hp4K M * (1 + ‖xj ν j z‖) ^ 2 * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hP0]
    exact mul_le_mul_of_nonneg_left (hp4_dpsi_bound ν s ha M _ v) hP0
  refine (norm_add_le _ _).trans ?_
  have h1r : (0:ℝ) ≤ 1 + ‖xj ν j z‖ := by linarith
  have hQ0 : 0 ≤ hp4K M * hp4P ν s j z * ‖v‖ := mul_nonneg (mul_nonneg hK hP0) hv
  have f1 : ‖xj ν j z‖ * (1 + ‖xj ν j z‖) ^ 3 ≤ (1 + ‖xj ν j z‖) ^ 4 := by
    have e : (1 + ‖xj ν j z‖) ^ 4 = (1 + ‖xj ν j z‖) ^ 3 * (1 + ‖xj ν j z‖) := by ring
    nlinarith [pow_nonneg h1r 3]
  have f2 : (1 + ‖xj ν j z‖) ^ 2 ≤ (1 + ‖xj ν j z‖) ^ 4 := by
    have h1 : (1:ℝ) ≤ (1 + ‖xj ν j z‖) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (1 + ‖xj ν j z‖))]
  nlinarith [mul_le_mul_of_nonneg_left f1 hQ0, mul_le_mul_of_nonneg_left f2 hQ0]

lemma hp4_fderiv_bound (ν s : ℝ) (j : ℤ) (ha : 1 ≤ ageA ν s) (M : Mat3) (z v : ℝ × ℝ) :
    ‖fderiv ℝ (fun w => hp4P ν s j w • hp4Psi ν s M (xj ν j w)) z v‖ ≤
      10 * hp4K M * hp4P ν s j z * (1 + ‖xj ν j z‖) ^ 4 * ‖v‖ := by
  rw [gp_fderiv_line _ z v (hp4_diff ν s j M z), (hp4_line ν s j M z v).deriv]
  exact hp4_line_bound ν s j ha M z v

theorem hpTermMajorant : HpTermMajorant := by
  unfold HpTermMajorant
  intro ν hν s hs M x
  have hc : 0 < cOf ν := inv_pos.mpr (pow_pos hν 2)
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha0 : 0 < ageA ν s := by linarith
  have hαpos : 0 < 1 / (8 * ageA ν s) := div_pos one_pos (by linarith)
  have hK := hp4K_nonneg M
  have hC0 : 0 ≤ 10 * hp4K M * ((ageA ν s ^ 2)⁻¹ * Real.exp (1 / (4 * ageA ν s))) * (3 + |x.2|) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)) (by positivity)
  refine ⟨fun j => (10 * hp4K M * ((ageA ν s ^ 2)⁻¹ * Real.exp (1 / (4 * ageA ν s))) * (3 + |x.2|) ^ 4)
      * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)),
    (hp4_poly4_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hαpos hc).mul_left _, ?_⟩
  intro j z hz
  have hz1 : |z.1 - x.1| < 1 := by
    have h := norm_fst_le (z - x)
    rw [Prod.fst_sub, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt h hz
  have hz2 : |z.2 - x.2| < 1 := by
    have h := norm_snd_le (z - x)
    rw [Prod.snd_sub, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt h hz
  have hpq : |(x.1 - (j : ℝ) * cOf ν) - (z.1 - (j : ℝ) * cOf ν)| < 1 := by
    rw [sub_sub_sub_cancel_right, abs_sub_comm]; exact hz1
  have hy1pq : |(z.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν)| < 1 := by
    rw [sub_sub_sub_cancel_right]; exact hz1
  have hw := hp4_abs_le _ _ hpq
  have hy1 := hp4_abs_le _ _ hy1pq
  have hy2 := hp4_abs_le _ _ hz2
  have hn : ‖xj ν j z‖ ≤ |z.1 - (j : ℝ) * cOf ν| + |z.2| := hp4_norm_le_abs (xj ν j z)
  have hone : 1 + ‖xj ν j z‖ ≤ (3 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
    nlinarith [abs_nonneg x.2, abs_nonneg (x.1 - (j : ℝ) * cOf ν),
      mul_nonneg (abs_nonneg x.2) (abs_nonneg (x.1 - (j : ℝ) * cOf ν))]
  have hw2 : (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ 2 * (z.1 - (j : ℝ) * cOf ν) ^ 2 + 2 := by
    have hsqw := pow_le_pow_left₀ (abs_nonneg _) hw 2
    nlinarith [sq_abs (x.1 - (j : ℝ) * cOf ν), sq_abs (z.1 - (j : ℝ) * cOf ν),
      sq_nonneg (|z.1 - (j : ℝ) * cOf ν| - 1)]
  have hsq : (x.1 - (j : ℝ) * cOf ν) ^ 2 / 2 - 1 ≤ sq2 (xj ν j z) := by
    have e : sq2 (xj ν j z) = (z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2 := rfl
    rw [e]
    nlinarith [sq_nonneg z.2]
  have hq : 0 ≤ 1 / (4 * ageA ν s) := (div_pos one_pos (by linarith)).le
  have hE : Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
      ≤ Real.exp (1 / (4 * ageA ν s)) * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : 1 / (4 * ageA ν s) + -(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2
        = (1 / (4 * ageA ν s)) * (1 - (x.1 - (j : ℝ) * cOf ν) ^ 2 / 2) := by ring
    rw [e]
    have e2 : -(sq2 (xj ν j z)) / (4 * ageA ν s) = -(1 / (4 * ageA ν s)) * sq2 (xj ν j z) := by ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hsq hq]
  have hPle : hp4P ν s j z ≤ (ageA ν s ^ 2)⁻¹ *
      (Real.exp (1 / (4 * ageA ν s)) * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
    unfold hp4P
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hpow : (1 + ‖xj ν j z‖) ^ 4 ≤ (3 + |x.2|) ^ 4 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 := by
    have := pow_le_pow_left₀ (by linarith [norm_nonneg (xj ν j z)]) hone 4
    rwa [mul_pow] at this
  have h10K : 0 ≤ 10 * hp4K M := mul_nonneg (by norm_num) hK
  have hbound : 10 * hp4K M * hp4P ν s j z * (1 + ‖xj ν j z‖) ^ 4 ≤
      (10 * hp4K M * ((ageA ν s ^ 2)⁻¹ * Real.exp (1 / (4 * ageA ν s))) * (3 + |x.2|) ^ 4)
        * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
    calc 10 * hp4K M * hp4P ν s j z * (1 + ‖xj ν j z‖) ^ 4
        ≤ 10 * hp4K M * ((ageA ν s ^ 2)⁻¹ *
            (Real.exp (1 / (4 * ageA ν s)) * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)))
          * ((3 + |x.2|) ^ 4 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hPle h10K) hpow (by positivity)
            (mul_nonneg h10K (by positivity))
      _ = (10 * hp4K M * ((ageA ν s ^ 2)⁻¹ * Real.exp (1 / (4 * ageA ν s))) * (3 + |x.2|) ^ 4)
          * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 4 * Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
          ring
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 (mul_nonneg (by positivity) (Real.exp_pos _).le))
    (fun v => ?_)
  rw [hp4_eq ν s j M]
  exact (hp4_fderiv_bound ν s j ha1 M z v).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))

end UnforcedLeray.Short.PartIIIb.Concrete
