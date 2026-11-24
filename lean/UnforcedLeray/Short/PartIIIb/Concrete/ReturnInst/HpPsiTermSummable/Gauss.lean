import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Gaussian bounds for the lattice terms (helpers of `ReturnInst/HpPsiTermSummable.lean`)

Summability over `j : ℤ` of the lattice terms of `h^p_A`, `ψ^p_A` (and of `f_A`, shared with
`ReturnInst/FATermSummable.lean`).  The line derivative of the Gaussian `V_j` and `ψ_j` is computed
by `HasDerivAt`; the norm bounds are polynomial times `exp(-(q - jc)²/(4a))`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Scalar Gaussian summability -/

lemma gp_gauss_dom (t α c : ℝ) (hα : 0 < α) (hc : 0 ≤ c) (j : ℤ) :
    Real.exp (-α * (t - (j : ℝ) * c) ^ 2) ≤
      Real.exp (-π * ((α * c ^ 2 / π) * (j : ℝ) ^ 2
        - 2 * (α * |t| * c / π) * |(j : ℝ)|)) := by
  apply Real.exp_le_exp.mpr
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have key : -π * ((α * c ^ 2 / π) * (j : ℝ) ^ 2 - 2 * (α * |t| * c / π) * |(j : ℝ)|)
      = -(α * c ^ 2 * (j : ℝ) ^ 2) + 2 * α * c * (|t| * |(j : ℝ)|) := by
    field_simp
    ring
  rw [key]
  have h1 : t * (j : ℝ) ≤ |t| * |(j : ℝ)| := by
    rw [← abs_mul]
    exact le_abs_self _
  nlinarith [mul_nonneg (mul_nonneg hα.le hc) (sub_nonneg.mpr h1), mul_nonneg hα.le (sq_nonneg t)]

lemma gp_gauss_pow_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) (k : ℕ) :
    Summable (fun j : ℤ => |(j : ℝ)| ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have hT : 0 < α * c ^ 2 / π := div_pos (mul_pos hα (pow_pos hc 2)) Real.pi_pos
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_pow_mul_jacobiTheta₂_term_bound (α * |t| * c / π) hT k)
  simp only [Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (gp_gauss_dom t α c hα hc.le j) (pow_nonneg (abs_nonneg _) k)

lemma gp_gauss_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  simpa using gp_gauss_pow_summable t α c hα hc 0

/-- The cubic-weighted shifted Gaussian is summable over `j ∈ ℤ`. -/
lemma gp_poly_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 3 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h3 := gp_gauss_pow_summable t α c hα hc 3
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ 3 := pow_nonneg (by linarith [abs_nonneg t]) 3
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add h3).mul_left (4 * (1 + |t| + c) ^ 3))
  have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |t| + c) * (1 + |(j : ℝ)|) := by
    have h1 : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
      have h2 := abs_sub t ((j : ℝ) * c)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg t, mul_nonneg hz hc.le, mul_nonneg (abs_nonneg t) hz]
  have hcube : (1 + |(j : ℝ)|) ^ 3 ≤ 4 * (1 + |(j : ℝ)| ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (1 - |(j : ℝ)|)) (by linarith : (0:ℝ) ≤ 1 + |(j : ℝ)|)]
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  have h1 : (1 + |t - (j : ℝ) * c|) ^ 3 ≤ (1 + |t| + c) ^ 3 * (1 + |(j : ℝ)|) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu 3
  calc (1 + |t - (j : ℝ) * c|) ^ 3 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ 3 * (4 * (1 + |(j : ℝ)| ^ 3))) *
          Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hcube hK)) hE
    _ = 4 * (1 + |t| + c) ^ 3 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ 3 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

/-! ## 2. Elementary facts -/

/-- `Jrot` is an isometry for the sup norm. -/
lemma gp_jrot_norm (y : ℝ × ℝ) : ‖Jrot y‖ = ‖y‖ := by
  show max ‖-y.2‖ ‖y.1‖ = max ‖y.1‖ ‖y.2‖
  rw [norm_neg, max_comm]

/-- Operator bound for the meridional block. -/
lemma gp_merApply_norm_le (M : Mat3) (w : ℝ × ℝ) :
    ‖merApply M w‖ ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖w‖ := by
  have h1 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
  have h2 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have k1 : |M 0 0 * w.1 + M 0 2 * w.2| ≤ (|M 0 0| + |M 0 2|) * ‖w‖ := by
    calc |M 0 0 * w.1 + M 0 2 * w.2| ≤ |M 0 0 * w.1| + |M 0 2 * w.2| := abs_add_le _ _
      _ = |M 0 0| * |w.1| + |M 0 2| * |w.2| := by rw [abs_mul, abs_mul]
      _ ≤ |M 0 0| * ‖w‖ + |M 0 2| * ‖w‖ :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (|M 0 0| + |M 0 2|) * ‖w‖ := by ring
  have k2 : |M 2 0 * w.1 + M 2 2 * w.2| ≤ (|M 2 0| + |M 2 2|) * ‖w‖ := by
    calc |M 2 0 * w.1 + M 2 2 * w.2| ≤ |M 2 0 * w.1| + |M 2 2 * w.2| := abs_add_le _ _
      _ = |M 2 0| * |w.1| + |M 2 2| * |w.2| := by rw [abs_mul, abs_mul]
      _ ≤ |M 2 0| * ‖w‖ + |M 2 2| * ‖w‖ :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (|M 2 0| + |M 2 2|) * ‖w‖ := by ring
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · show ‖M 0 0 * w.1 + M 0 2 * w.2‖ ≤ _
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (M 2 0), abs_nonneg (M 2 2)]
  · show ‖M 2 0 * w.1 + M 2 2 * w.2‖ ≤ _
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (M 0 0), abs_nonneg (M 0 2)]

/-- `1 + |x_j| ≤ (1 + |η|)(1 + |q - jc|)`. -/
lemma gp_one_add_norm (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    1 + ‖xj ν j x‖ ≤ (1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
  have h1 : ‖xj ν j x‖ ≤ |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  nlinarith [mul_nonneg (abs_nonneg x.2) (abs_nonneg (x.1 - (j : ℝ) * cOf ν))]

/-- The exponential factor of `V_j, ψ_j` is dominated by the one in the first coordinate. -/
lemma gp_exp_le (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x : ℝ × ℝ) :
    Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hsq : sq2 (xj ν j x) = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := rfl
  have e : -(sq2 (xj ν j x)) / (4 * ageA ν s) = -(1 / (4 * ageA ν s)) * sq2 (xj ν j x) := by
    ring
  rw [e, hsq]
  have hq : 0 ≤ 1 / (4 * ageA ν s) := by positivity
  nlinarith [sq_nonneg x.2, mul_nonneg hq (sq_nonneg x.2)]

/-! ## 3. The line derivative of `V_j` and `ψ_j` -/

/-- Along a line, `|x_j|²` has the expected derivative. -/
lemma gp_sq2_line (ν : ℝ) (j : ℤ) (y v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => sq2 (xj ν j (y + t • v)))
      (2 * (xj ν j y).1 * v.1 + 2 * (xj ν j y).2 * v.2) 0 := by
  have hx : HasDerivAt (fun t : ℝ => (xj ν j (y + t • v)).1) v.1 0 := by
    have : HasDerivAt (fun t : ℝ => y.1 + t * v.1 - (j : ℝ) * cOf ν) v.1 0 := by
      have h := (((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add y.1).sub_const ((j : ℝ) * cOf ν)
      simpa using h
    exact this
  have hy : HasDerivAt (fun t : ℝ => (xj ν j (y + t • v)).2) v.2 0 := by
    have : HasDerivAt (fun t : ℝ => y.2 + t * v.2) v.2 0 := by
      have h := ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add y.2
      simpa using h
    exact this
  have h := (hx.mul hx).add (hy.mul hy)
  have e : (fun t : ℝ => sq2 (xj ν j (y + t • v))) = fun t : ℝ =>
      (xj ν j (y + t • v)).1 * (xj ν j (y + t • v)).1
        + (xj ν j (y + t • v)).2 * (xj ν j (y + t • v)).2 := by
    funext t; simp only [sq2]; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero, xj]
  ring

/-- The line derivative of the Gaussian weight `E = exp(-|x_j|²/(4a))`. -/
lemma gp_exp_line (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(sq2 (xj ν j (x + t • v))) / (4 * ageA ν s)))
      (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s))) 0 := by
  have h := (((gp_sq2_line ν j x v).neg).div_const (4 * ageA ν s)).exp
  convert h using 2
  · simp
  · simp [neg_div]

/-- `fderiv` along a line through `y` (general codomain). -/
lemma gp_fderiv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (y v : ℝ × ℝ) (hf : DifferentiableAt ℝ f y) :
    fderiv ℝ f y v = deriv (fun t : ℝ => f (y + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h2 : HasFDerivAt f (fderiv ℝ f y) ((fun t : ℝ => y + t • v) 0) := by
    simpa using hf.hasFDerivAt
  have hc := h2.comp_hasDerivAt (0 : ℝ) hl
  exact hc.deriv.symm

/-- The Gaussian `V_j` along a line. -/
lemma gp_Vj_line (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Vj ν s j (x + t • v))
      (((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) • Jrot v
        + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
            (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))) •
          Jrot (xj ν j x)) 0 := by
  have hc := (gp_exp_line ν s j x v).const_mul ((ageA ν s ^ 2)⁻¹)
  have hJ : HasDerivAt (fun t : ℝ => Jrot (xj ν j (x + t • v))) (Jrot v) 0 := by
    have e1 : HasDerivAt (fun t : ℝ => -(xj ν j (x + t • v)).2) (-v.2) 0 := by
      have h : HasDerivAt (fun t : ℝ => -(x.2 + t * v.2)) (-v.2) 0 := by
        have h0 := (((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add x.2).neg
        rw [one_mul] at h0
        exact h0
      exact h
    have e2 : HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).1) v.1 0 := by
      have h : HasDerivAt (fun t : ℝ => x.1 + t * v.1 - (j : ℝ) * cOf ν) v.1 0 := by
        have := (((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add x.1).sub_const ((j : ℝ) * cOf ν)
        simpa using this
      exact h
    exact e1.prodMk e2
  have hV := hc.smul hJ
  refine hV.congr_deriv ?_
  simp only [zero_smul, add_zero]

/-- The Gaussian `ψ_j` along a line. -/
lemma gp_psij_line (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => psij ν s j (x + t • v))
      ((-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))) 0 :=
  (gp_exp_line ν s j x v).const_mul (-2 * (ageA ν s)⁻¹)

/-- `Vj` is differentiable. -/
lemma gp_Vj_diff (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : DifferentiableAt ℝ (Vj ν s j) x := by
  unfold Vj xj Jrot sq2
  fun_prop

/-- `psij` is differentiable. -/
lemma gp_psij_diff (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : DifferentiableAt ℝ (psij ν s j) x := by
  unfold psij xj sq2
  fun_prop

/-- `fderiv` of `Vj` in a direction. -/
lemma gp_fderiv_Vj (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) x v =
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) • Jrot v
        + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
            (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))) •
          Jrot (xj ν j x) := by
  rw [gp_fderiv_line (Vj ν s j) x v (gp_Vj_diff ν s j x)]
  exact (gp_Vj_line ν s j x v).deriv

/-- `fderiv` of `ψ_j` in a direction. -/
lemma gp_fderiv_psij (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    fderiv ℝ (psij ν s j) x v =
      (-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s))) := by
  rw [gp_fderiv_line (psij ν s j) x v (gp_psij_diff ν s j x)]
  exact (gp_psij_line ν s j x v).deriv

/-! ## 4. Norm bounds for the derivatives -/

/-- `|c₁| ≤ |y| |v| / a` for the directional derivative coefficient. -/
lemma gp_c1_abs (y v : ℝ × ℝ) (a : ℝ) (ha : 0 < a) :
    |-(2 * y.1 * v.1 + 2 * y.2 * v.2) / (4 * a)| ≤ ‖y‖ * ‖v‖ / a := by
  have h1 : |y.1| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le y
  have h3 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h4 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  have p1 : |y.1 * v.1| ≤ ‖y‖ * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
  have p2 : |y.2 * v.2| ≤ ‖y‖ * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _)
  have hS : |2 * y.1 * v.1 + 2 * y.2 * v.2| ≤ 4 * (‖y‖ * ‖v‖) := by
    have e : 2 * y.1 * v.1 + 2 * y.2 * v.2 = 2 * (y.1 * v.1) + 2 * (y.2 * v.2) := by ring
    rw [e]
    calc |2 * (y.1 * v.1) + 2 * (y.2 * v.2)| ≤ |2 * (y.1 * v.1)| + |2 * (y.2 * v.2)| :=
          abs_add_le _ _
      _ = 2 * |y.1 * v.1| + 2 * |y.2 * v.2| := by
          simp only [abs_mul, abs_two]
      _ ≤ 4 * (‖y‖ * ‖v‖) := by linarith
  have h4a : 0 < 4 * a := by linarith
  rw [abs_div, abs_neg, abs_of_pos h4a, div_le_div_iff₀ h4a ha]
  nlinarith [mul_le_mul_of_nonneg_right hS ha.le]

/-- The smul-pair bound for the line derivative of `V_j`. -/
lemma gp_smul_pair_bound (P c : ℝ) (y v : ℝ × ℝ) (hP : 0 ≤ P) (a : ℝ) (ha : 0 < a)
    (hc : |c| ≤ ‖y‖ * ‖v‖ / a) :
    ‖P • Jrot v + (P * c) • Jrot y‖ ≤ P * (1 + ‖y‖ ^ 2 / a) * ‖v‖ := by
  have n1 : ‖P • Jrot v‖ = P * ‖v‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs, abs_of_nonneg hP]
  have n2 : ‖(P * c) • Jrot y‖ = P * |c| * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
  have hQ : P * |c| * ‖y‖ ≤ P * (‖y‖ * ‖v‖ / a) * ‖y‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hP) (norm_nonneg y)
  calc ‖P • Jrot v + (P * c) • Jrot y‖ ≤ ‖P • Jrot v‖ + ‖(P * c) • Jrot y‖ := norm_add_le _ _
    _ = P * ‖v‖ + P * |c| * ‖y‖ := by rw [n1, n2]
    _ ≤ P * ‖v‖ + P * (‖y‖ * ‖v‖ / a) * ‖y‖ := by linarith
    _ = P * (1 + ‖y‖ ^ 2 / a) * ‖v‖ := by ring

/-- `‖V_j(x)‖ = (a²)⁻¹ e^{-|x_j|²/(4a)} |x_j|`. -/
lemma gp_Vj_norm_eq (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    ‖Vj ν s j x‖ = (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖ := by
  unfold Vj
  rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Norm bound on the directional derivative of `V_j`. -/
lemma gp_fderiv_Vj_norm (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x v : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s j) x v‖ ≤
      (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * ‖v‖ := by
  rw [gp_fderiv_Vj]
  have e : (ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
      (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))
      = ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)) := by ring
  rw [e]
  exact gp_smul_pair_bound _ _ _ _ (by positivity) _ ha
    (gp_c1_abs (xj ν j x) v (ageA ν s) ha)

/-- Value of `ψ_j`. -/
lemma gp_psij_norm_eq (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (ha : 0 < ageA ν s) :
    ‖psij ν s j x‖ = 2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
  unfold psij
  have hp : 0 ≤ 2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr ha.le)) (Real.exp_pos _).le
  have e : -2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      = -(2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by ring
  rw [e, norm_neg, Real.norm_eq_abs, abs_of_nonneg hp]

/-- Norm bound on the directional derivative of `ψ_j`. -/
lemma gp_fderiv_psij_norm (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x v : ℝ × ℝ) :
    ‖fderiv ℝ (psij ν s j) x v‖ ≤
      2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (‖xj ν j x‖ * ‖v‖ / ageA ν s) := by
  rw [gp_fderiv_psij]
  have hp : 0 ≤ 2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr ha.le)) (Real.exp_pos _).le
  have e : (-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))
      = -(2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s))) := by ring
  rw [e, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left (gp_c1_abs (xj ν j x) v (ageA ν s) ha) hp

/-! ## 5. Lattice term bounds (polynomial times Gaussian) -/

/-- Bound for the `h^p` lattice term `merApply M (V_j x) - DV_j(x)(merApply M x_j)`. -/
lemma gp_hp_bound (ν s : ℝ) (ha : 0 < ageA ν s) (M : Mat3) (x : ℝ × ℝ) :
    ∃ K : ℝ, ∀ j : ℤ, ‖merApply M (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply M (xj ν j x))‖ ≤
      K * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hK0 : 0 ≤ |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| := by positivity
  have hκ : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hA2 : 0 ≤ 2 + (ageA ν s)⁻¹ := by have := inv_nonneg.mpr ha.le; linarith
  refine ⟨(|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ * (2 + (ageA ν s)⁻¹)
    * (1 + |x.2|) ^ 3, fun j => ?_⟩
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hyn : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hq : 0 ≤ 1 + ‖xj ν j x‖ ^ 2 / ageA ν s := by
    have := div_nonneg (sq_nonneg ‖xj ν j x‖) ha.le; linarith
  have hpos : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
      (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) := mul_nonneg (mul_nonneg hκ hE0) hq
  have h1 : ‖merApply M (Vj ν s j x)‖ ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) *
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖) := by
    rw [← gp_Vj_norm_eq ν s j x]; exact gp_merApply_norm_le M _
  have h2 : ‖fderiv ℝ (Vj ν s j) x (merApply M (xj ν j x))‖ ≤
      (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) *
        ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖xj ν j x‖) :=
    (gp_fderiv_Vj_norm ν s ha j x (merApply M (xj ν j x))).trans
      (mul_le_mul_of_nonneg_left (gp_merApply_norm_le M _) hpos)
  have h3 : ‖xj ν j x‖ * (2 + ‖xj ν j x‖ ^ 2 / ageA ν s) ≤
      (2 + (ageA ν s)⁻¹) * (1 + ‖xj ν j x‖) ^ 3 := by
    have hzc : ‖xj ν j x‖ ≤ (1 + ‖xj ν j x‖) ^ 3 := by
      nlinarith [mul_nonneg hyn hyn, mul_nonneg (mul_nonneg hyn hyn) hyn]
    have hz3 : ‖xj ν j x‖ ^ 3 ≤ (1 + ‖xj ν j x‖) ^ 3 := pow_le_pow_left₀ hyn (by linarith) 3
    have hia : 0 ≤ (ageA ν s)⁻¹ := inv_nonneg.mpr ha.le
    calc ‖xj ν j x‖ * (2 + ‖xj ν j x‖ ^ 2 / ageA ν s)
        = 2 * ‖xj ν j x‖ + ‖xj ν j x‖ ^ 3 * (ageA ν s)⁻¹ := by ring
      _ ≤ 2 * (1 + ‖xj ν j x‖) ^ 3 + (1 + ‖xj ν j x‖) ^ 3 * (ageA ν s)⁻¹ :=
          add_le_add (by linarith) (mul_le_mul_of_nonneg_right hz3 hia)
      _ = (2 + (ageA ν s)⁻¹) * (1 + ‖xj ν j x‖) ^ 3 := by ring
  have h4 : (1 + ‖xj ν j x‖) ^ 3 ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (gp_one_add_norm ν j x) 3
  have hEb : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    gp_exp_le ν s ha j x
  have hK' : 0 ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ *
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := mul_nonneg (mul_nonneg hK0 hκ) hE0
  have hQ : 0 ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ *
      (2 + (ageA ν s)⁻¹) * (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK0 hκ) hA2) (by positivity)) (by positivity)
  calc ‖merApply M (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply M (xj ν j x))‖
      ≤ ‖merApply M (Vj ν s j x)‖ + ‖fderiv ℝ (Vj ν s j) x (merApply M (xj ν j x))‖ :=
        norm_sub_le _ _
    _ ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) *
          ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖) +
        (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) *
          ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖xj ν j x‖) := add_le_add h1 h2
    _ = ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ *
          Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
        (‖xj ν j x‖ * (2 + ‖xj ν j x‖ ^ 2 / ageA ν s)) := by ring
    _ ≤ ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ *
          Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
        ((2 + (ageA ν s)⁻¹) * (1 + ‖xj ν j x‖) ^ 3) := mul_le_mul_of_nonneg_left h3 hK'
    _ ≤ ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ *
          Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) *
        ((2 + (ageA ν s)⁻¹) * ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hA2) hK'
    _ = ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ * (2 + (ageA ν s)⁻¹) *
          (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring
    _ ≤ ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ * (2 + (ageA ν s)⁻¹) *
          (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) *
          Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul_of_nonneg_left hEb hQ
    _ = (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * (ageA ν s ^ 2)⁻¹ * (2 + (ageA ν s)⁻¹) *
          (1 + |x.2|) ^ 3 *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

/-- Bound for the `ψ^p` lattice term `tr M · ψ_j - Dψ_j(merApply M x_j)`. -/
lemma gp_psi_bound (ν s : ℝ) (ha : 0 < ageA ν s) (M : Mat3) (x : ℝ × ℝ) :
    ∃ K : ℝ, ∀ j : ℤ, ‖merTrace M * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply M (xj ν j x))‖ ≤
      K * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hK0 : 0 ≤ |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| := by positivity
  have hia : 0 ≤ (ageA ν s)⁻¹ := inv_nonneg.mpr ha.le
  have hP0 : 0 ≤ 2 * |merTrace M| * (ageA ν s)⁻¹ := by positivity
  have hQ0 : 0 ≤ 2 * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) := by
    positivity
  refine ⟨(2 * |merTrace M| * (ageA ν s)⁻¹ + 2 * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ *
    (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|)) * (1 + |x.2|) ^ 3, fun j => ?_⟩
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hyn : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have h1 : ‖merTrace M * psij ν s j x‖ ≤
      |merTrace M| * (2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by
    rw [norm_mul, Real.norm_eq_abs, gp_psij_norm_eq ν s j x ha]
  have hw : ‖merApply M (xj ν j x)‖ ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖xj ν j x‖ :=
    gp_merApply_norm_le M _
  have h2 : ‖fderiv ℝ (psij ν s j) x (merApply M (xj ν j x))‖ ≤
      2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (‖xj ν j x‖ * ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖xj ν j x‖) / ageA ν s) := by
    refine (gp_fderiv_psij_norm ν s ha j x (merApply M (xj ν j x))).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw hyn) ha.le
  set y := xj ν j x with hydef
  set E := Real.exp (-(sq2 y) / (4 * ageA ν s)) with hEdef
  set K₀ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| with hK₀def
  set T := |merTrace M| with hTdef
  set P := 2 * T * (ageA ν s)⁻¹ with hPdef
  set Q := 2 * (ageA ν s)⁻¹ * (ageA ν s)⁻¹ * K₀ with hQdef
  have hPQ : 0 ≤ P + Q := add_nonneg hP0 hQ0
  have hsq : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 3 := by nlinarith [mul_nonneg hyn hyn]
  have hone : 1 ≤ (1 + ‖y‖) ^ 3 := one_le_pow₀ (by linarith)
  have hcore : P + Q * ‖y‖ ^ 2 ≤ (P + Q) * (1 + ‖y‖) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hone hP0, mul_le_mul_of_nonneg_left hsq hQ0]
  have hEb : E ≤ Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    gp_exp_le ν s ha j x
  have hbig : (1 + ‖y‖) ^ 3 ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (gp_one_add_norm ν j x) 3
  calc ‖merTrace M * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply M (xj ν j x))‖
      ≤ ‖merTrace M * psij ν s j x‖ + ‖fderiv ℝ (psij ν s j) x (merApply M (xj ν j x))‖ :=
        norm_sub_le _ _
    _ ≤ T * (2 * (ageA ν s)⁻¹ * E) + 2 * (ageA ν s)⁻¹ * E * (‖y‖ * (K₀ * ‖y‖) / ageA ν s) :=
        add_le_add h1 h2
    _ = E * (P + Q * ‖y‖ ^ 2) := by
        rw [hPdef, hQdef]; ring
    _ ≤ E * ((P + Q) * (1 + ‖y‖) ^ 3) := mul_le_mul_of_nonneg_left hcore hE0
    _ ≤ E * ((P + Q) * ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbig hPQ) hE0
    _ = (P + Q) * (1 + |x.2|) ^ 3 * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 * E) := by ring
    _ ≤ (P + Q) * (1 + |x.2|) ^ 3 * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEb (by positivity))
          (mul_nonneg hPQ (by positivity))

end UnforcedLeray.Short.PartIIIb.Concrete
