import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `C/inst/5` x-part: differentiability of `Σ_j Φ(x_j)` in `x` (source 4973-4980)

`psiPhi ν s M` is the translate profile `Φ`; `psiPhiD` is its explicit directional derivative
along `y`, and the lattice terms are bounded on a unit ball by Gaussian decay.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sum of the absolute entries of a meridional matrix (a norm bound for `merApply`). -/
def Kmat (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

theorem Kmat_nonneg (M : Mat3) : 0 ≤ Kmat M := by
  unfold Kmat; positivity

theorem merTrace_abs_le (M : Mat3) : |merTrace M| ≤ Kmat M := by
  unfold merTrace Kmat
  have h1 := abs_add_le (M 0 0) (M 2 2)
  have h2 := abs_nonneg (M 0 2)
  have h3 := abs_nonneg (M 2 0)
  linarith

theorem merApply_fst_le (M : Mat3) (y : ℝ × ℝ) :
    |(merApply M y).1| ≤ Kmat M * ‖y‖ := by
  have h := gp_merApply_norm_le M y
  have h1 : |(merApply M y).1| ≤ ‖merApply M y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le _
  unfold Kmat at *
  linarith

theorem merApply_snd_le (M : Mat3) (y : ℝ × ℝ) :
    |(merApply M y).2| ≤ Kmat M * ‖y‖ := by
  have h := gp_merApply_norm_le M y
  have h1 : |(merApply M y).2| ≤ ‖merApply M y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le _
  unfold Kmat at *
  linarith

theorem abs_fst_le' (y : ℝ × ℝ) : |y.1| ≤ ‖y‖ := by
  rw [← Real.norm_eq_abs]; exact norm_fst_le y

theorem abs_snd_le' (y : ℝ × ℝ) : |y.2| ≤ ‖y‖ := by
  rw [← Real.norm_eq_abs]; exact norm_snd_le y

/-- Pure algebra: `|t + (2 y₁ w₁ + 2 y₂ w₂)/(4a)| ≤ K(1+R²)` when `a ≥ 1`. -/
theorem P_bound (a K R t y1 y2 w1 w2 : ℝ) (ha1 : 1 ≤ a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hy1 : |y1| ≤ R) (hy2 : |y2| ≤ R) (hw1 : |w1| ≤ K * R) (hw2 : |w2| ≤ K * R)
    (ht : |t| ≤ K) :
    |t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a)| ≤ K * (1 + R ^ 2) := by
  have ha0 : 0 < a := by linarith
  have h4a : 0 < 4 * a := by linarith
  have h1 : |y1| * |w1| ≤ R * (K * R) := mul_le_mul hy1 hw1 (abs_nonneg _) hR
  have h2 : |y2| * |w2| ≤ R * (K * R) := mul_le_mul hy2 hw2 (abs_nonneg _) hR
  have e1 : |2 * y1 * w1| = 2 * (|y1| * |w1|) := by
    rw [abs_mul, abs_mul, abs_two]; ring
  have e2 : |2 * y2 * w2| = 2 * (|y2| * |w2|) := by
    rw [abs_mul, abs_mul, abs_two]; ring
  have hQ : |2 * y1 * w1 + 2 * y2 * w2| ≤ 4 * K * R ^ 2 := by
    have := abs_add_le (2 * y1 * w1) (2 * y2 * w2)
    nlinarith
  have hd : |(2 * y1 * w1 + 2 * y2 * w2) / (4 * a)| ≤ K * R ^ 2 := by
    rw [abs_div, abs_of_pos h4a, div_le_iff₀ h4a]
    nlinarith [mul_nonneg (mul_nonneg hK (sq_nonneg R)) (sub_nonneg.2 ha1)]
  calc |t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a)|
      ≤ |t| + |(2 * y1 * w1 + 2 * y2 * w2) / (4 * a)| := abs_add_le _ _
    _ ≤ K + K * R ^ 2 := add_le_add ht hd
    _ = K * (1 + R ^ 2) := by ring

/-- Pure algebra for the directional derivative of `Φ`. -/
theorem real_D_bound (a E K R n y1 y2 v1 v2 w1 w2 u1 u2 t : ℝ) (ha1 : 1 ≤ a) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hn : 0 ≤ n)
    (hy1 : |y1| ≤ R) (hy2 : |y2| ≤ R) (hv1 : |v1| ≤ n) (hv2 : |v2| ≤ n)
    (hw1 : |w1| ≤ K * R) (hw2 : |w2| ≤ K * R) (hu1 : |u1| ≤ K * n) (hu2 : |u2| ≤ K * n)
    (ht : |t| ≤ K) :
    |(-2 * a⁻¹) * (E * (-(2 * y1 * v1 + 2 * y2 * v2) / (4 * a))
        * (t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a))
      + E * ((2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)) / (4 * a)))|
      ≤ 6 * K * E * n * (1 + R) ^ 3 := by
  have ha0 : 0 < a := by linarith
  have h4a : 0 < 4 * a := by linarith
  have hinv1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have hinvpos : 0 < a⁻¹ := inv_pos.mpr ha0
  have hP := P_bound a K R t y1 y2 w1 w2 ha1 hK hR hy1 hy2 hw1 hw2 ht
  have hA : |-(2 * y1 * v1 + 2 * y2 * v2) / (4 * a)| ≤ R * n := by
    rw [abs_div, abs_neg, abs_of_pos h4a, div_le_iff₀ h4a]
    have e1 : |2 * y1 * v1| = 2 * (|y1| * |v1|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have e2 : |2 * y2 * v2| = 2 * (|y2| * |v2|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have h1 : |y1| * |v1| ≤ R * n := mul_le_mul hy1 hv1 (abs_nonneg _) hR
    have h2 : |y2| * |v2| ≤ R * n := mul_le_mul hy2 hv2 (abs_nonneg _) hR
    have := abs_add_le (2 * y1 * v1) (2 * y2 * v2)
    nlinarith [mul_nonneg hR hn, mul_nonneg (mul_nonneg hR hn) (sub_nonneg.2 ha1)]
  have hdP : |(2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)) / (4 * a)|
      ≤ 2 * K * R * n := by
    rw [abs_div, abs_of_pos h4a, div_le_iff₀ h4a]
    have e1 : |2 * v1 * w1| = 2 * (|v1| * |w1|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have e2 : |2 * y1 * u1| = 2 * (|y1| * |u1|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have e3 : |2 * v2 * w2| = 2 * (|v2| * |w2|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have e4 : |2 * y2 * u2| = 2 * (|y2| * |u2|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have f1 : |v1| * |w1| ≤ n * (K * R) := mul_le_mul hv1 hw1 (abs_nonneg _) hn
    have f2 : |y1| * |u1| ≤ R * (K * n) := mul_le_mul hy1 hu1 (abs_nonneg _) hR
    have f3 : |v2| * |w2| ≤ n * (K * R) := mul_le_mul hv2 hw2 (abs_nonneg _) hn
    have f4 : |y2| * |u2| ≤ R * (K * n) := mul_le_mul hy2 hu2 (abs_nonneg _) hR
    have hN : |2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)| ≤ 8 * K * R * n := by
      have t1 := abs_add_le (2 * v1 * w1 + 2 * y1 * u1) (2 * v2 * w2 + 2 * y2 * u2)
      have t2 := abs_add_le (2 * v1 * w1) (2 * y1 * u1)
      have t3 := abs_add_le (2 * v2 * w2) (2 * y2 * u2)
      nlinarith
    have hKRn : 0 ≤ K * R * n := mul_nonneg (mul_nonneg hK hR) hn
    nlinarith [mul_nonneg hKRn (sub_nonneg.2 ha1)]
  have hneg : |(-2 * a⁻¹)| = 2 * a⁻¹ := by
    rw [abs_of_neg (by linarith)]; ring
  have hi : |E * (-(2 * y1 * v1 + 2 * y2 * v2) / (4 * a))
        * (t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a))
      + E * ((2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)) / (4 * a))|
      ≤ E * (R * n) * (K * (1 + R ^ 2)) + E * (2 * K * R * n) := by
    have h1 : |E * (-(2 * y1 * v1 + 2 * y2 * v2) / (4 * a))
        * (t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a))| ≤ E * (R * n) * (K * (1 + R ^ 2)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hE]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA hE) hP (abs_nonneg _)
        (mul_nonneg hE (mul_nonneg hR hn))
    have h2 : |E * ((2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)) / (4 * a))|
        ≤ E * (2 * K * R * n) := by
      rw [abs_mul, abs_of_nonneg hE]
      exact mul_le_mul_of_nonneg_left hdP hE
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hpoly : 0 ≤ 3 * (1 + R) ^ 3 - R * (3 + R ^ 2) := by
    nlinarith [pow_nonneg hR 3, pow_nonneg hR 2]
  rw [abs_mul, hneg]
  have hstep : 2 * a⁻¹ * |E * (-(2 * y1 * v1 + 2 * y2 * v2) / (4 * a))
        * (t + (2 * y1 * w1 + 2 * y2 * w2) / (4 * a))
      + E * ((2 * v1 * w1 + 2 * y1 * u1 + (2 * v2 * w2 + 2 * y2 * u2)) / (4 * a))|
      ≤ 2 * (E * (R * n) * (K * (1 + R ^ 2)) + E * (2 * K * R * n)) :=
    mul_le_mul (by linarith) hi (abs_nonneg _) (by norm_num)
  refine hstep.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hE hK) hn) hpoly]


/-- Explicit directional derivative of `y ↦ psiPhi ν s M y` along `v`. -/
def psiPhiD (ν s : ℝ) (M : Mat3) (y v : ℝ × ℝ) : ℝ :=
  (-2 * (ageA ν s)⁻¹) *
    (Real.exp (-(sq2 y) / (4 * ageA ν s)) * (-(2 * y.1 * v.1 + 2 * y.2 * v.2) / (4 * ageA ν s))
        * (merTrace M + (2 * y.1 * (merApply M y).1 + 2 * y.2 * (merApply M y).2) / (4 * ageA ν s))
      + Real.exp (-(sq2 y) / (4 * ageA ν s)) *
        ((2 * v.1 * (merApply M y).1 + 2 * y.1 * (merApply M v).1
          + (2 * v.2 * (merApply M y).2 + 2 * y.2 * (merApply M v).2)) / (4 * ageA ν s)))

/-- Product rule for `t ↦ K0 · exp (g t) · (c + q t / A)` at `t = 0`. -/
theorem pp_form (K0 c A : ℝ) (g q : ℝ → ℝ) (g' q' : ℝ) (hg : HasDerivAt g g' 0)
    (hq : HasDerivAt q q' 0) :
    HasDerivAt (fun t => K0 * Real.exp (g t) * (c + q t / A))
      (K0 * (Real.exp (g 0) * g') * (c + q 0 / A) + K0 * Real.exp (g 0) * (q' / A)) 0 := by
  have h1 : HasDerivAt (fun t => K0 * Real.exp (g t)) (K0 * (Real.exp (g 0) * g')) 0 :=
    (hg.exp).const_mul K0
  have h2 : HasDerivAt (fun t => c + q t / A) (q' / A) 0 := (hq.div_const A).const_add c
  exact (h1.mul h2).congr_deriv (by ring)

/-- The line derivative of `y ↦ psiPhi ν s M y` at `y` along `v`. -/
theorem psiPhi_line (ν s : ℝ) (M : Mat3) (y v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => psiPhi ν s M (y + t • v)) (psiPhiD ν s M y v) 0 := by
  have hc1 : HasDerivAt (fun t : ℝ => y.1 + t * v.1) v.1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add y.1
  have hc2 : HasDerivAt (fun t : ℝ => y.2 + t * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add y.2
  have hfun : (fun t : ℝ => psiPhi ν s M (y + t • v)) = fun t : ℝ =>
      (-2 * (ageA ν s)⁻¹) * Real.exp (-(sq2 (y + t • v)) / (4 * ageA ν s)) *
        (merTrace M + (2 * (y + t • v).1 * (merApply M (y + t • v)).1
          + 2 * (y + t • v).2 * (merApply M (y + t • v)).2) / (4 * ageA ν s)) := by
    funext t
    unfold psiPhi
    ring
  have hs : HasDerivAt (fun t : ℝ => -(sq2 (y + t • v)) / (4 * ageA ν s))
      (-(2 * y.1 * v.1 + 2 * y.2 * v.2) / (4 * ageA ν s)) 0 := by
    have e : (fun t : ℝ => -(sq2 (y + t • v)) / (4 * ageA ν s)) = fun t : ℝ =>
        -((y.1 + t * v.1) * (y.1 + t * v.1) + (y.2 + t * v.2) * (y.2 + t * v.2))
          / (4 * ageA ν s) := by
      funext t
      simp only [sq2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [e]
    exact (((hc1.mul hc1).add (hc2.mul hc2)).neg.div_const (4 * ageA ν s)).congr_deriv
      (by ring)
  have hq : HasDerivAt (fun t : ℝ => 2 * (y + t • v).1 * (merApply M (y + t • v)).1
      + 2 * (y + t • v).2 * (merApply M (y + t • v)).2)
      (2 * v.1 * (merApply M y).1 + 2 * y.1 * (merApply M v).1
        + (2 * v.2 * (merApply M y).2 + 2 * y.2 * (merApply M v).2)) 0 := by
    have e : (fun t : ℝ => 2 * (y + t • v).1 * (merApply M (y + t • v)).1
        + 2 * (y + t • v).2 * (merApply M (y + t • v)).2) = fun t : ℝ =>
        2 * (y.1 + t * v.1) * (M 0 0 * (y.1 + t * v.1) + M 0 2 * (y.2 + t * v.2))
        + 2 * (y.2 + t * v.2) * (M 2 0 * (y.1 + t * v.1) + M 2 2 * (y.2 + t * v.2)) := by
      funext t
      simp only [merApply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [e]
    have hm1 : HasDerivAt (fun t : ℝ => M 0 0 * (y.1 + t * v.1) + M 0 2 * (y.2 + t * v.2))
        (M 0 0 * v.1 + M 0 2 * v.2) 0 := (hc1.const_mul _).add (hc2.const_mul _)
    have hm2 : HasDerivAt (fun t : ℝ => M 2 0 * (y.1 + t * v.1) + M 2 2 * (y.2 + t * v.2))
        (M 2 0 * v.1 + M 2 2 * v.2) 0 := (hc1.const_mul _).add (hc2.const_mul _)
    have A1 := (hc1.const_mul 2).mul hm1
    have A2 := (hc2.const_mul 2).mul hm2
    exact (A1.add A2).congr_deriv (by simp only [merApply]; ring)
  have hL := pp_form (-2 * (ageA ν s)⁻¹) (merTrace M) (4 * ageA ν s) _ _ _ _ hs hq
  rw [hfun]
  refine hL.congr_deriv ?_
  unfold psiPhiD
  simp only [zero_smul, add_zero, merApply]
  ring


theorem term_diff (ν s : ℝ) (M : Mat3) (j : ℤ) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w => psiPhi ν s M (xj ν j w)) z := by
  unfold psiPhi xj sq2 merApply merTrace
  fun_prop

/-- The derivative of a lattice term of `Φ` along a direction, in closed form. -/
theorem fderiv_term (ν s : ℝ) (M : Mat3) (j : ℤ) (z v : ℝ × ℝ) :
    fderiv ℝ (fun w => psiPhi ν s M (xj ν j w)) z v = psiPhiD ν s M (xj ν j z) v := by
  rw [gp_fderiv_line _ z v (term_diff ν s M j z)]
  have e : ∀ t : ℝ, xj ν j (z + t • v) = xj ν j z + t • v := fun t => by
    ext <;> simp [xj] <;> ring
  have hl : HasDerivAt (fun t : ℝ => psiPhi ν s M (xj ν j (z + t • v)))
      (psiPhiD ν s M (xj ν j z) v) 0 := by
    simp only [e]
    exact psiPhi_line ν s M (xj ν j z) v
  exact hl.deriv

/-- `|Φ(y)| ≤ 2K(1+|y|)³ e^{-|y|²/(4a)}`. -/
theorem psiPhi_abs_le (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (M : Mat3) (y : ℝ × ℝ) :
    |psiPhi ν s M y| ≤ 2 * Kmat M * ((1 + ‖y‖) ^ 3 * Real.exp (-(sq2 y) / (4 * ageA ν s))) := by
  have ha0 : 0 < ageA ν s := by linarith
  have hE : 0 ≤ Real.exp (-(sq2 y) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hP := P_bound (ageA ν s) (Kmat M) ‖y‖ (merTrace M) y.1 y.2 (merApply M y).1
    (merApply M y).2 ha1 (Kmat_nonneg M) (norm_nonneg y) (abs_fst_le' y) (abs_snd_le' y)
    (merApply_fst_le M y) (merApply_snd_le M y) (merTrace_abs_le M)
  have e : psiPhi ν s M y = (-2 * (ageA ν s)⁻¹) * Real.exp (-(sq2 y) / (4 * ageA ν s)) *
      (merTrace M + (2 * y.1 * (merApply M y).1 + 2 * y.2 * (merApply M y).2)
        / (4 * ageA ν s)) := by
    unfold psiPhi
    ring
  have hinv1 : (ageA ν s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have hinvpos : 0 < (ageA ν s)⁻¹ := inv_pos.mpr ha0
  have hneg : |(-2 * (ageA ν s)⁻¹)| = 2 * (ageA ν s)⁻¹ := by
    rw [abs_of_neg (by linarith)]; ring
  have hR : 1 + ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 3 := by
    nlinarith [norm_nonneg y, mul_nonneg (norm_nonneg y) (norm_nonneg y),
      pow_nonneg (norm_nonneg y) 3]
  rw [e, abs_mul, abs_mul, abs_of_nonneg hE, hneg]
  calc _ ≤ 2 * Real.exp (-(sq2 y) / (4 * ageA ν s)) * (Kmat M * (1 + ‖y‖ ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hE) hP (abs_nonneg _)
          (by positivity)
    _ ≤ 2 * Kmat M * ((1 + ‖y‖) ^ 3 * Real.exp (-(sq2 y) / (4 * ageA ν s))) := by
        have h := mul_le_mul_of_nonneg_left hR (mul_nonneg (Kmat_nonneg M) hE)
        nlinarith [h]

/-- Norm bound of the lattice derivative. -/
theorem psiPhiD_bound (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (M : Mat3) (y v : ℝ × ℝ) :
    ‖psiPhiD ν s M y v‖ ≤ 6 * Kmat M * ‖v‖ *
      ((1 + ‖y‖) ^ 3 * Real.exp (-(sq2 y) / (4 * ageA ν s))) := by
  rw [Real.norm_eq_abs]
  unfold psiPhiD
  have hE : 0 ≤ Real.exp (-(sq2 y) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have := real_D_bound (ageA ν s) (Real.exp (-(sq2 y) / (4 * ageA ν s))) (Kmat M) ‖y‖ ‖v‖
    y.1 y.2 v.1 v.2 (merApply M y).1 (merApply M y).2 (merApply M v).1 (merApply M v).2
    (merTrace M) ha1 hE (Kmat_nonneg M) (norm_nonneg y) (norm_nonneg v) (abs_fst_le' y)
    (abs_snd_le' y) (abs_fst_le' v) (abs_snd_le' v) (merApply_fst_le M y) (merApply_snd_le M y)
    (merApply_fst_le M v) (merApply_snd_le M v) (merTrace_abs_le M)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- Gaussian comparison on the unit ball: `(1+|x_j(z)|)³ e^{-|x_j(z)|²/(4a)}` is dominated
by `64(1+|x_2|)³ e^{1/(4a)} (1+|q_j|)³ e^{-q_j²/(8a)}` for `q_j = x_1 - jc`. -/
theorem ball_geom (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (x z : ℝ × ℝ) (hz : ‖z - x‖ < 1) (j : ℤ) :
    (1 + ‖xj ν j z‖) ^ 3 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) ≤
      64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have ha0 : 0 < ageA ν s := by linarith
  have hd1 : |z.1 - x.1| < 1 := by
    have := abs_fst_le' (z - x)
    simp only [Prod.fst_sub] at this
    linarith
  have hd2 : |z.2 - x.2| < 1 := by
    have := abs_snd_le' (z - x)
    simp only [Prod.snd_sub] at this
    linarith
  have hR := gp_one_add_norm ν j z
  have hz2 : 1 + |z.2| ≤ 2 * (1 + |x.2|) := by
    have := abs_sub_abs_le_abs_sub z.2 x.2
    linarith [abs_nonneg x.2]
  have hq1 : 1 + |z.1 - (j : ℝ) * cOf ν| ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
    have := abs_sub_abs_le_abs_sub (z.1 - (j : ℝ) * cOf ν) (x.1 - (j : ℝ) * cOf ν)
    have e : (z.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν) = z.1 - x.1 := by ring
    rw [e] at this
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν)]
  have hR3 : (1 + ‖xj ν j z‖) ^ 3 ≤
      (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    exact le_trans hR (mul_le_mul hz2 hq1 (by positivity) (by positivity))
  have hE := gp_exp_le ν s ha0 j z
  have hdd := abs_lt.mp hd1
  have hq2 : (1 / (4 * ageA ν s)) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 / 2 - 1)
      ≤ (1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg ((x.1 - (j : ℝ) * cOf ν) + 2 * (z.1 - x.1)),
      mul_nonneg (by linarith [hdd.1, hdd.2] : (0:ℝ) ≤ 1 - (z.1 - x.1))
        (by linarith [hdd.1, hdd.2] : (0:ℝ) ≤ 1 + (z.1 - x.1))]
  have hE2 : Real.exp (-(1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2)
      ≤ Real.exp (1 / (4 * ageA ν s)) *
        Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
    have hw : 1 / (8 * ageA ν s) = 1 / (4 * ageA ν s) / 2 := by ring
    rw [← Real.exp_add, hw]
    apply Real.exp_le_exp.mpr
    nlinarith [hq2]
  have hEnn : 0 ≤ Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  calc (1 + ‖xj ν j z‖) ^ 3 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))
      ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 3 *
          Real.exp (-(1 / (4 * ageA ν s)) * (z.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul hR3 (hE) hEnn (by positivity)
    _ ≤ (2 * (1 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 3 *
          (Real.exp (1 / (4 * ageA ν s)) *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = 64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
        ring

/-- The summable majorant of the lattice terms of `Φ` on the unit ball. -/
def ubd (ν s : ℝ) (x : ℝ × ℝ) (M : Mat3) (j : ℤ) : ℝ :=
  6 * Kmat M * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s))) *
    ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
      Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))

theorem ubd_nonneg (ν s : ℝ) (x : ℝ × ℝ) (M : Mat3) (j : ℤ) : 0 ≤ ubd ν s x M j := by
  unfold ubd
  have hK := Kmat_nonneg M
  have h1 : (0:ℝ) ≤ 64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) := by positivity
  have h2 : (0:ℝ) ≤ (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
      Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) h1) h2

theorem ubd_summable (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (x : ℝ × ℝ) (M : Mat3) (hν : 0 < ν) :
    Summable (ubd ν s x M) := by
  have ha0 : 0 < ageA ν s := by linarith
  have hα0 : 0 < 1 / (8 * ageA ν s) := by positivity
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have h := (gp_poly_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hα0 hc).mul_left
    (6 * Kmat M * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s))))
  exact h

theorem psiPhiXDiff : PsiPhiXDiff := by
  unfold PsiPhiXDiff
  intro ν s hν hs M x
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hu := ubd_summable ν s ha1 x M hν
  have hval : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 → ∀ v : ℝ × ℝ,
      ‖psiPhiD ν s M (xj ν j z) v‖ ≤ ubd ν s x M j * ‖v‖ := by
    intro j z hz v
    have h1 := psiPhiD_bound ν s ha1 M (xj ν j z) v
    have h2 := ball_geom ν s ha1 x z hz j
    have hn := norm_nonneg v
    have h6 : 0 ≤ 6 * Kmat M := by have := Kmat_nonneg M; linarith
    have h3 : 6 * Kmat M * ‖v‖ * ((1 + ‖xj ν j z‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)))
        ≤ 6 * Kmat M * ‖v‖ * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg h6 hn)
    refine h1.trans (h3.trans (le_of_eq ?_))
    unfold ubd
    ring
  have hfb : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν j w)) z‖ ≤ ubd ν s x M j := by
    intro j z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (ubd_nonneg ν s x M j)
    intro v
    rw [fderiv_term]
    exact hval j z hz v
  have hf0 : Summable (fun n : ℤ => psiPhi ν s M (xj ν n x)) := by
    apply Summable.of_norm_bounded hu
    intro j
    rw [Real.norm_eq_abs]
    have h1 := psiPhi_abs_le ν s ha1 M (xj ν j x)
    have h2 := ball_geom ν s ha1 x x (by simp) j
    have hK := Kmat_nonneg M
    have hpos : 0 ≤ 64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
      positivity
    have h5 : 2 * Kmat M * ((1 + ‖xj ν j x‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) ≤ ubd ν s x M j := by
      unfold ubd
      have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * Kmat M)
      nlinarith [mul_nonneg hK hpos, h6]
    exact h1.trans h5
  have hF : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      HasFDerivAt (fun w => psiPhi ν s M (xj ν n w))
        (fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z) z :=
    fun n z _ => (term_diff ν s M n z).hasFDerivAt
  have hbound : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z‖ ≤ ubd ν s x M n :=
    fun n z hz => hfb n z (mem_ball_iff_norm.mp hz)
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => psiPhi ν s M (xj ν n w))
    (f' := fun n z => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z)
    (u := ubd ν s x M) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hF hbound
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete
