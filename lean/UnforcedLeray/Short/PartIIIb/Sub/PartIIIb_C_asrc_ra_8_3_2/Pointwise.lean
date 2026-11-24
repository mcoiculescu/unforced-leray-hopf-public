import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.Pointwise.PwT

/-!
# `PartIII-b:C/asrc/ra/8/3/2/1` : the pointwise Gaussian-sum bound (`HpAPointwise`)

Source: `the November 2 reference manuscript` 4963-4977 (`h^p_A = Σ_j [V_j, A^y_mer x_j]`),
4978 (Gaussian decay). Helpers live in the folder `Pointwise/` (`Value`, `PwG`, `PwT`).

Strategy. `M = A^y(s)` is a fixed matrix, so `h^p_A = Σ_j T_j` with `T_j(x) = merApply M (V_j x) -
DV_j(x)(merApply M x_j)`. Value: `‖T_j‖ ≤ 12 |M|_F (1+|x_j|)^4 e^{-|x_j|²/9}`. Derivative: the
explicit formula for `DT_j` gives `‖DT_j‖ ≤ 24 |M|_F (1+|x_j|)^4 e^{-|x_j|²/9}`; on the unit ball
around `x` this is dominated by a summable Gaussian in `j` (`hasFDerivAt_tsum_of_isPreconnected`).
Summing gives `‖hpAMag‖ ≤ 36 |M|_F gEnv(x)`.
-/

set_option autoImplicit false

noncomputable section

open Set Real Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pw_params (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (hs1 : s ≤ (11 / 10) / ν) :
    0 < ageA ν s ∧ 1 ≤ ageA ν s ∧ ageA ν s ≤ 9 / 4 := by
  have hνs : ν * s ≤ 11 / 10 := by
    have := (le_div_iff₀ hν).1 hs1
    linarith
  have hp : 0 < ν * s := mul_pos hν hs
  refine ⟨?_, ?_, ?_⟩ <;> unfold ageA <;> linarith

/-- Summability of the lattice terms at a point. -/
lemma pw_T_summable (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s) (ha9 : ageA ν s ≤ 9 / 4) :
    Summable (fun j : ℤ => pwT ν s j (Ay ν χ A s) x) := by
  have hsum := pw_G_summable ν hν x
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => pw_T_value ν s ha hb ha9 (Ay ν χ A s) x j) (hsum.mul_left _))

/-- Uniform-on-a-ball derivative bound of one lattice term. -/
lemma pw_ball_bound (ν s : ℝ) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s) (ha9 : ageA ν s ≤ 9 / 4)
    (j : ℤ) (M : Mat3) (x0 y : ℝ × ℝ) (hy : y ∈ Metric.ball x0 1) :
    ‖fderiv ℝ (pwT ν s j M) y‖ ≤
      24 * frob M * (5200 * Real.exp (1 / 18)) * Real.exp (-(1 / 72) * (x0.1 - (j : ℝ) * cOf ν) ^ 2) := by
  have hF : 0 ≤ frob M := by unfold frob; positivity
  have h1 := pwT_fderiv_norm ν s ha hb ha9 j M y
  have h2 := gEnv_summand_le (norm_nonneg (xj ν j y))
  have hd : ‖y - x0‖ < 1 := by
    have := Metric.mem_ball.1 hy
    rwa [dist_eq_norm] at this
  have hyx : |y.1 - x0.1| < 1 := by
    have h := norm_fst_le (y - x0)
    rw [Prod.fst_sub, Real.norm_eq_abs] at h
    linarith
  have hA : |x0.1 - (j : ℝ) * cOf ν| ≤ |(xj ν j y).1| + |y.1 - x0.1| := by
    have e : x0.1 - (j : ℝ) * cOf ν = (xj ν j y).1 + (x0.1 - y.1) := by
      simp only [xj]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm]
  have hB : |(xj ν j y).1| ≤ ‖xj ν j y‖ := by
    have := norm_fst_le (xj ν j y)
    rwa [Real.norm_eq_abs] at this
  have hn0 : 0 ≤ ‖xj ν j y‖ := norm_nonneg _
  have hm : |x0.1 - (j : ℝ) * cOf ν| - 1 ≤ ‖xj ν j y‖ := by linarith
  have hsq : (x0.1 - (j : ℝ) * cOf ν) ^ 2 / 4 - 1 ≤ ‖xj ν j y‖ ^ 2 := by
    have hm0 : 0 ≤ |x0.1 - (j : ℝ) * cOf ν| := abs_nonneg _
    have hu2 : (x0.1 - (j : ℝ) * cOf ν) ^ 2 = |x0.1 - (j : ℝ) * cOf ν| ^ 2 := (sq_abs _).symm
    rw [hu2]
    rcases le_total |x0.1 - (j : ℝ) * cOf ν| 2 with h | h
    · nlinarith [sq_nonneg ‖xj ν j y‖]
    · have h3 : |x0.1 - (j : ℝ) * cOf ν| - 1 ≤ ‖xj ν j y‖ := hm
      have h4 : 0 ≤ |x0.1 - (j : ℝ) * cOf ν| - 1 := by linarith
      nlinarith [mul_le_mul h3 h3 h4 hn0, sq_nonneg (|x0.1 - (j : ℝ) * cOf ν| - 4 / 3)]
  have hexp : Real.exp (-(‖xj ν j y‖ ^ 2) / 18)
      ≤ Real.exp (1 / 18) * Real.exp (-(1 / 72) * (x0.1 - (j : ℝ) * cOf ν) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have hpos : 0 ≤ 24 * frob M := by linarith
  calc ‖fderiv ℝ (pwT ν s j M) y‖
      ≤ 24 * frob M * ((1 + ‖xj ν j y‖) ^ 4 * Real.exp (-(‖xj ν j y‖ ^ 2) / 9)) := h1
    _ ≤ 24 * frob M * (5200 * Real.exp (-(‖xj ν j y‖ ^ 2) / 18)) :=
        mul_le_mul_of_nonneg_left h2 hpos
    _ ≤ 24 * frob M * (5200 * (Real.exp (1 / 18) * Real.exp (-(1 / 72) * (x0.1 - (j : ℝ) * cOf ν) ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num)) hpos
    _ = 24 * frob M * (5200 * Real.exp (1 / 18)) * Real.exp (-(1 / 72) * (x0.1 - (j : ℝ) * cOf ν) ^ 2) := by
        ring

/-- Derivative part of the pointwise bound. -/
lemma pw_hpA_deriv (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) (hs1 : s ≤ (11 / 10) / ν) :
    ‖fderiv ℝ (hpA ν χ A s) x‖ ≤ 24 * frob (Ay ν χ A s) * gEnv ν x := by
  obtain ⟨ha, hb, ha9⟩ := pw_params ν s hν hs hs1
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hS := gp_gauss_summable x.1 (1 / 72) (cOf ν) (by norm_num) hc
  have hu : Summable (fun j : ℤ => 24 * frob (Ay ν χ A s) * (5200 * Real.exp (1 / 18))
      * Real.exp (-(1 / 72) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := hS.mul_left _
  have hfd := hasFDerivAt_tsum_of_isPreconnected (f := fun j : ℤ => pwT ν s j (Ay ν χ A s))
    (f' := fun (j : ℤ) (y : ℝ × ℝ) => fderiv ℝ (pwT ν s j (Ay ν χ A s)) y)
    (u := fun j : ℤ => 24 * frob (Ay ν χ A s) * (5200 * Real.exp (1 / 18))
      * Real.exp (-(1 / 72) * (x.1 - (j : ℝ) * cOf ν) ^ 2))
    hu isOpen_ball (convex_ball x 1).isPreconnected
    (fun j y _ => (pwT_diff ν s j (Ay ν χ A s) y).hasFDerivAt)
    (fun j y hy => pw_ball_bound ν s ha hb ha9 j (Ay ν χ A s) x y hy)
    (mem_ball_self one_pos) (pw_T_summable ν χ A s x hν ha hb ha9) (mem_ball_self one_pos)
  have hH : HasFDerivAt (hpA ν χ A s)
      (∑' j : ℤ, fderiv ℝ (pwT ν s j (Ay ν χ A s)) x) x := hfd
  rw [hH.fderiv]
  have hG := pw_G_summable ν hν x
  have hsn : Summable (fun j : ℤ => ‖fderiv ℝ (pwT ν s j (Ay ν χ A s)) x‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => pwT_fderiv_norm ν s ha hb ha9 j (Ay ν χ A s) x) (hG.mul_left _)
  calc ‖∑' j : ℤ, fderiv ℝ (pwT ν s j (Ay ν χ A s)) x‖
      ≤ ∑' j : ℤ, ‖fderiv ℝ (pwT ν s j (Ay ν χ A s)) x‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℤ, 24 * frob (Ay ν χ A s) * ((1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) :=
        hsn.tsum_le_tsum (fun j => pwT_fderiv_norm ν s ha hb ha9 j (Ay ν χ A s) x) (hG.mul_left _)
    _ = 24 * frob (Ay ν χ A s) * gEnv ν x := by
        rw [tsum_mul_left]
        rfl

/-- **Leaf (i): pointwise Gaussian-sum bound** (source 4963-4977, 4978). -/
theorem hpAPointwise_core : HpAPointwise := by
  refine ⟨36, by norm_num, ?_⟩
  intro ν χf A s x hν hs hs1
  obtain ⟨ha, hb, ha9⟩ := pw_params ν s hν hs hs1
  have hv := pw_hpA_value ν χf A s x hν hs hs1
  have hd := pw_hpA_deriv ν χf A s x hν hs hs1
  unfold hpAMag
  have e : 36 * frob (Ay ν χf A s) * gEnv ν x
      = 12 * frob (Ay ν χf A s) * gEnv ν x + 24 * frob (Ay ν χf A s) * gEnv ν x := by ring
  linarith [hv, hd, e]

end UnforcedLeray.Short.PartIIIb.Concrete

/-- Top-level name of the pointwise Gaussian-sum bound (source 4963-4977, 4978). -/
theorem hpAPointwise : UnforcedLeray.Short.PartIIIb.Concrete.HpAPointwise :=
  UnforcedLeray.Short.PartIIIb.Concrete.hpAPointwise_core
