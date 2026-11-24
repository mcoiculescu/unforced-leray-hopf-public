import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.Pointwise.PwG

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- One lattice term of `h^p_A` as a function of the point. -/
def pwT (ν s : ℝ) (j : ℤ) (M : Mat3) (z : ℝ × ℝ) : ℝ × ℝ :=
  merApply M (Vj ν s j z) - fderiv ℝ (Vj ν s j) z (merApply M (xj ν j z))

lemma pw_Vj_contDiff (ν s : ℝ) (j : ℤ) : ContDiff ℝ ⊤ (Vj ν s j) := by
  unfold Vj xj Jrot sq2
  fun_prop

lemma pw_Vj_differentiable (ν s : ℝ) (j : ℤ) : Differentiable ℝ (Vj ν s j) :=
  (pw_Vj_contDiff ν s j).differentiable (by simp)

lemma pw_c_diff (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun z => fderiv ℝ (Vj ν s j) z) x :=
  ((pw_Vj_contDiff ν s j).fderiv_right (m := 1) (by simp)).differentiable (by simp) x

lemma pw_c_hasFDerivAt (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    HasFDerivAt (fun z => fderiv ℝ (Vj ν s j) z) (fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z) x) x :=
  (pw_c_diff ν s j x).hasFDerivAt

lemma pw_fst_hasDerivAt {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => (f τ).1) f'.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf

lemma pw_snd_hasDerivAt {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => (f τ).2) f'.2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf

lemma pw_merApply_hasDerivAt (M : Mat3) {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun τ => merApply M (f τ)) (merApply M f') t := by
  have h1 := ((pw_fst_hasDerivAt hf).const_mul (M 0 0)).add ((pw_snd_hasDerivAt hf).const_mul (M 0 2))
  have h2 := ((pw_fst_hasDerivAt hf).const_mul (M 2 0)).add ((pw_snd_hasDerivAt hf).const_mul (M 2 2))
  exact h1.prodMk h2

lemma pw_xj_line (ν : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => xj ν j (x + t • v)) v 0 := by
  have hx : HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).1) v.1 0 := by
    have : HasDerivAt (fun t : ℝ => x.1 + t * v.1 - (j : ℝ) * cOf ν) v.1 0 := by
      have h := (((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add x.1).sub_const ((j : ℝ) * cOf ν)
      simpa using h
    exact this
  have hy : HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).2) v.2 0 := by
    have : HasDerivAt (fun t : ℝ => x.2 + t * v.2) v.2 0 := by
      have h := ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add x.2
      simpa using h
    exact this
  exact hx.prodMk hy

lemma pw_merApply_diff (M : Mat3) {g : ℝ × ℝ → ℝ × ℝ} {x : ℝ × ℝ} (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun z => merApply M (g z)) x := by
  unfold merApply
  exact ((hg.fst.const_mul (M 0 0)).add (hg.snd.const_mul (M 0 2))).prodMk
    ((hg.fst.const_mul (M 2 0)).add (hg.snd.const_mul (M 2 2)))

lemma pw_u_diff (ν : ℝ) (j : ℤ) (M : Mat3) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun z => merApply M (xj ν j z)) x := by
  unfold merApply xj
  fun_prop

lemma pw_u_fderiv (ν : ℝ) (j : ℤ) (M : Mat3) (x v : ℝ × ℝ) :
    fderiv ℝ (fun z => merApply M (xj ν j z)) x v = merApply M v := by
  rw [gp_fderiv_line _ x v (pw_u_diff ν j M x)]
  exact (pw_merApply_hasDerivAt M (pw_xj_line ν j x v)).deriv

lemma pw_c_const (ν s : ℝ) (j : ℤ) (x v w : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z) x v w
      = fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z w) x v := by
  rw [fderiv_clm_apply (pw_c_diff ν s j x) (differentiableAt_const w)]
  simp

lemma pw_c_line (ν s : ℝ) (j : ℤ) (x v w : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z w) x v = pwGD ν s j x v w := by
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ (Vj ν s j) z w) x :=
    (pw_c_diff ν s j x).clm_apply (differentiableAt_const w)
  rw [gp_fderiv_line _ x v hd]
  have e : (fun t : ℝ => fderiv ℝ (Vj ν s j) (x + t • v) w)
      = fun t : ℝ => pwG ν s j w (x + t • v) :=
    funext fun t => pw_fderiv_Vj_eq ν s j _ w
  show deriv (fun t : ℝ => fderiv ℝ (Vj ν s j) (x + t • v) w) 0 = _
  rw [e, (pwG_line_hasDerivAt ν s j x v w).deriv]

lemma pwT_hasDerivAt (ν s : ℝ) (j : ℤ) (M : Mat3) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => pwT ν s j M (x + t • v))
      (merApply M (fderiv ℝ (Vj ν s j) x v)
        - (fderiv ℝ (Vj ν s j) x (merApply M v) + pwGD ν s j x v (merApply M (xj ν j x)))) 0 := by
  have hV : HasDerivAt (fun t : ℝ => Vj ν s j (x + t • v)) (fderiv ℝ (Vj ν s j) x v) 0 := by
    rw [gp_fderiv_Vj]
    exact gp_Vj_line ν s j x v
  have h1 := pw_merApply_hasDerivAt M hV
  have hu : HasFDerivAt (fun z => merApply M (xj ν j z))
      (fderiv ℝ (fun z => merApply M (xj ν j z)) x) x := (pw_u_diff ν j M x).hasFDerivAt
  have hcu := (pw_c_hasFDerivAt ν s j x).clm_apply hu
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hcu hl (by simp)
  have h := h1.sub h2
  unfold pwT
  refine h.congr_deriv ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, pw_u_fderiv]
  rw [pw_c_const, pw_c_line]

lemma pwT_diff (ν s : ℝ) (j : ℤ) (M : Mat3) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (pwT ν s j M) x := by
  have hVd := pw_Vj_differentiable ν s j x
  unfold pwT
  refine DifferentiableAt.sub ?_ ?_
  · exact pw_merApply_diff M hVd
  · exact (pw_c_diff ν s j x).clm_apply (pw_u_diff ν j M x)

lemma pwT_fderiv (ν s : ℝ) (j : ℤ) (M : Mat3) (x v : ℝ × ℝ) :
    fderiv ℝ (pwT ν s j M) x v
      = merApply M (fderiv ℝ (Vj ν s j) x v)
        - (fderiv ℝ (Vj ν s j) x (merApply M v) + pwGD ν s j x v (merApply M (xj ν j x))) := by
  rw [gp_fderiv_line _ x v (pwT_diff ν s j M x)]
  exact (pwT_hasDerivAt ν s j M x v).deriv

/-- Abstract algebra for the derivative of one lattice term. -/
lemma pw_alg_T (κ E n a nv S : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hE : 0 ≤ E) (hn : 0 ≤ n)
    (ha : 1 ≤ a) (hnv : 0 ≤ nv) (hS : 0 ≤ S) :
    S * (κ * E * (1 + n ^ 2 / a) * nv) + κ * E * (1 + n ^ 2 / a) * (S * nv)
      + 4 * E * (1 + n) ^ 3 * nv * (S * n) ≤ 6 * S * E * (1 + n) ^ 4 * nv := by
  have ha0 : 0 < a := by linarith
  have hdiv : n ^ 2 / a ≤ n ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_right (sq_nonneg n) (inv_le_one_of_one_le₀ ha)
  have hX0 : 0 ≤ 1 + n ^ 2 / a := by positivity
  have hcube : 1 + n ^ 2 ≤ (1 + n) ^ 3 := by nlinarith [pow_nonneg hn 3]
  have q1 : κ * (1 + n ^ 2 / a) ≤ (1 + n) ^ 3 := by
    calc κ * (1 + n ^ 2 / a) ≤ 1 * (1 + n ^ 2 / a) := mul_le_mul_of_nonneg_right hκ1 hX0
      _ ≤ (1 + n) ^ 3 := by linarith
  have hM : 2 * κ * (1 + n ^ 2 / a) + 4 * (1 + n) ^ 3 * n ≤ 6 * (1 + n) ^ 4 := by
    have hp : 0 ≤ (1 + n) ^ 3 * (4 + 2 * n) := by positivity
    nlinarith [q1, hp]
  have hP : 0 ≤ S * E * nv := by positivity
  calc S * (κ * E * (1 + n ^ 2 / a) * nv) + κ * E * (1 + n ^ 2 / a) * (S * nv)
        + 4 * E * (1 + n) ^ 3 * nv * (S * n)
      = (S * E * nv) * (2 * κ * (1 + n ^ 2 / a) + 4 * (1 + n) ^ 3 * n) := by ring
    _ ≤ (S * E * nv) * (6 * (1 + n) ^ 4) := mul_le_mul_of_nonneg_left hM hP
    _ = 6 * S * E * (1 + n) ^ 4 * nv := by ring

/-- Pointwise derivative bound of one lattice term. -/
lemma pwT_fderiv_bound (ν s : ℝ) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s) (j : ℤ) (M : Mat3)
    (x v : ℝ × ℝ) :
    ‖fderiv ℝ (pwT ν s j M) x v‖ ≤
      6 * (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
        * (1 + ‖xj ν j x‖) ^ 4 * ‖v‖ := by
  rw [pwT_fderiv]
  refine (norm_sub_le _ _).trans ((add_le_add le_rfl (norm_add_le _ _)).trans ?_)
  have hS0 : 0 ≤ |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| := by positivity
  have h1 := gp_merApply_norm_le M (fderiv ℝ (Vj ν s j) x v)
  have h2 := gp_fderiv_Vj_norm ν s ha j x v
  have h3 := gp_fderiv_Vj_norm ν s ha j x (merApply M v)
  have h4 := gp_merApply_norm_le M v
  have h5 := pwGD_norm_le ν s j ha hb x v (merApply M (xj ν j x))
  have h6 := gp_merApply_norm_le M (xj ν j x)
  have k1 : (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖fderiv ℝ (Vj ν s j) x v‖
      ≤ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ((ageA ν s ^ 2)⁻¹
          * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * ‖v‖) :=
    mul_le_mul_of_nonneg_left h2 hS0
  have hpos1 : 0 ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      * (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) ha.le))
  have k2 : (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      * (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * ‖merApply M v‖
      ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      * (1 + ‖xj ν j x‖ ^ 2 / ageA ν s) * ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖v‖) :=
    mul_le_mul_of_nonneg_left h4 hpos1
  have hpos2 : 0 ≤ 4 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3
      * ‖v‖ := by positivity
  have k3 : ‖pwGD ν s j x v (merApply M (xj ν j x))‖
      ≤ 4 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3 * ‖v‖
        * ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * ‖xj ν j x‖) :=
    h5.trans (mul_le_mul_of_nonneg_left h6 hpos2)
  have hA := pw_alg_T (ageA ν s ^ 2)⁻¹ (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    ‖xj ν j x‖ (ageA ν s) ‖v‖ (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|)
    (inv_nonneg.2 (sq_nonneg _)) (inv_le_one_of_one_le₀ (one_le_pow₀ hb))
    (Real.exp_pos _).le (norm_nonneg _) hb (norm_nonneg _) hS0
  linarith [h1, h3, k1, k2, k3, hA]

/-- Operator-norm bound of the derivative of one lattice term. -/
lemma pwT_fderiv_norm (ν s : ℝ) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s)
    (ha9 : ageA ν s ≤ 9 / 4) (j : ℤ) (M : Mat3) (x : ℝ × ℝ) :
    ‖fderiv ℝ (pwT ν s j M) x‖ ≤
      24 * frob M * ((1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) := by
  have hF : 0 ≤ frob M := by unfold frob; positivity
  have hQ : 0 ≤ Real.exp (-(‖xj ν j x‖ ^ 2) / 9) := (Real.exp_pos _).le
  have hP : 0 ≤ (1 + ‖xj ν j x‖) ^ 4 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hF) (mul_nonneg hP hQ)) (fun v => ?_)
  have hb1 := pwT_fderiv_bound ν s ha hb j M x v
  have hS := pw_S_le_frob M
  have hE := pw_exp_le (ageA ν s) ha ha9 (xj ν j x)
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hS0 : 0 ≤ |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| := by positivity
  have hSE : (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ 4 * frob M * Real.exp (-(‖xj ν j x‖ ^ 2) / 9) :=
    mul_le_mul hS hE hE0 (by linarith)
  calc ‖fderiv ℝ (pwT ν s j M) x v‖
      ≤ 6 * (|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
          * (1 + ‖xj ν j x‖) ^ 4 * ‖v‖ := hb1
    _ = 6 * ((|M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|) * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
          * ((1 + ‖xj ν j x‖) ^ 4 * ‖v‖) := by ring
    _ ≤ 6 * (4 * frob M * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) * ((1 + ‖xj ν j x‖) ^ 4 * ‖v‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSE (by norm_num))
          (by positivity)
    _ = 24 * frob M * ((1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) * ‖v‖ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
