import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_2

/-!
# Leaf A: one periodized Gaussian term (SP 2356-2358)

Proves `GaussTermBound`.  The `k`-th term is `G(r) e^{2iϑ}` with `r = √((z.1+kc)²+z.2²)`, and
`e^{2iϑ} = angularTwo`.  Along the two coordinate lines the partial derivatives are computed
explicitly (`angularTwo` is `z/z̄` in complex form, so `∂_u e^{2iϑ} = -2iv(u+iv)²/r⁴`,
`∂_v e^{2iϑ} = 2iu(u+iv)²/r⁴`, of norm `2|v|/r²`, `2|u|/r²`), and the operator norm of the
derivative on `ℝ×ℝ` (sup norm) is at most the sum of the two partial norms.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Blueprint

/-- `‖angularTwo (u,v)‖ = 1` for `u²+v² > 0`. -/
private lemma gtb_norm_angTwo (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    ‖angularTwo (u, v)‖ = 1 := by
  have hn : ‖(u : ℂ) + (v : ℂ) * Complex.I‖ ^ 2 = u ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  unfold angularTwo
  dsimp only
  rw [norm_div, norm_pow, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact div_self hR.ne'

/-- The `u`-partial of `e^{2iϑ}`: `‖-(2 i v (u+iv)²)/R²‖ = 2|v|/R`. -/
private lemma gtb_norm_du (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    ‖-(2 * Complex.I * (v : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2) /
        ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2‖ = 2 * |v| / (u ^ 2 + v ^ 2) := by
  have hn : ‖(u : ℂ) + (v : ℂ) * Complex.I‖ ^ 2 = u ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hR' : u ^ 2 + v ^ 2 ≠ 0 := hR.ne'
  simp only [norm_div, norm_neg, norm_mul, norm_pow, hn, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, Complex.norm_two]
  field_simp
  try ring

/-- The `v`-partial of `e^{2iϑ}`: `‖2 i u (u+iv)²/R²‖ = 2|u|/R`. -/
private lemma gtb_norm_dv (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    ‖2 * Complex.I * (u : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 /
        ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2‖ = 2 * |u| / (u ^ 2 + v ^ 2) := by
  have hn : ‖(u : ℂ) + (v : ℂ) * Complex.I‖ ^ 2 = u ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hR' : u ^ 2 + v ^ 2 ≠ 0 := hR.ne'
  simp only [norm_div, norm_mul, norm_pow, hn, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, Complex.norm_two]
  field_simp
  try ring

/-- Derivative of `t ↦ e^{2iϑ}(u+t, v)` at `0`. -/
private lemma gtb_ang_u (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    HasDerivAt (fun t : ℝ => angularTwo (u + t, v))
      (-(2 * Complex.I * (v : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2) /
        ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2) 0 := by
  have hp : HasDerivAt (fun t : ℝ => ((u + t : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1 0 := by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add u).ofReal_comp).add_const
      ((v : ℂ) * Complex.I))
    simpa using h
  have hq1 : HasDerivAt (fun t : ℝ => (u + t) ^ 2 + v ^ 2) (2 * u) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_add u).pow 2).add_const (v ^ 2)
    simpa using h
  have hq : HasDerivAt (fun t : ℝ => (((u + t) ^ 2 + v ^ 2 : ℝ) : ℂ)) (2 * (u : ℂ)) 0 := by
    have h := hq1.ofReal_comp
    simpa using h
  have hd : (((u + 0) ^ 2 + v ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [add_zero]; exact_mod_cast hR.ne'
  have hdiv := (hp.pow 2).fun_div hq hd
  refine hdiv.congr_deriv ?_
  simp only [add_zero, Nat.cast_ofNat]
  norm_num
  congr 1
  push_cast
  linear_combination (2 * (v : ℂ) ^ 2 * ((u : ℂ) + (v : ℂ) * Complex.I)) * Complex.I_sq

/-- Derivative of `t ↦ e^{2iϑ}(u, v+t)` at `0`. -/
private lemma gtb_ang_v (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    HasDerivAt (fun t : ℝ => angularTwo (u, v + t))
      (2 * Complex.I * (u : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 /
        ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (u : ℂ) + ((v + t : ℝ) : ℂ) * Complex.I) Complex.I 0 := by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add v).ofReal_comp).mul_const Complex.I).const_add
      (u : ℂ)
    simpa using h
  have hq1 : HasDerivAt (fun t : ℝ => u ^ 2 + (v + t) ^ 2) (2 * v) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_add v).pow 2).const_add (u ^ 2)
    simpa using h
  have hq : HasDerivAt (fun t : ℝ => (((u ^ 2 + (v + t) ^ 2 : ℝ)) : ℂ)) (2 * (v : ℂ)) 0 := by
    have h := hq1.ofReal_comp
    simpa using h
  have hd : (((u ^ 2 + (v + 0) ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    simp only [add_zero]; exact_mod_cast hR.ne'
  have hdiv := (hp.pow 2).fun_div hq hd
  refine hdiv.congr_deriv ?_
  simp only [add_zero, Nat.cast_ofNat]
  norm_num
  congr 1
  push_cast
  linear_combination (-2 * (u : ℂ) * (v : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I)) *
    Complex.I_sq

/-- The `u`-derivative of the `k`-th term: `G(√((u+t)²+v²)) e^{2iϑ}(u+t,v)`. -/
private lemma gtb_prod_u (Gf : ℝ → ℂ) (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2)
    (hGd : DifferentiableAt ℝ Gf (Real.sqrt (u ^ 2 + v ^ 2))) :
    HasDerivAt (fun t : ℝ => Gf (Real.sqrt ((u + t) ^ 2 + v ^ 2)) * angularTwo (u + t, v))
      (((u / Real.sqrt (u ^ 2 + v ^ 2) : ℝ) • deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))) *
          angularTwo (u, v) +
        Gf (Real.sqrt (u ^ 2 + v ^ 2)) *
          (-(2 * Complex.I * (v : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2) /
            ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2)) 0 := by
  have hf : HasDerivAt (fun t : ℝ => (u + t) ^ 2 + v ^ 2) (2 * u) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_add u).pow 2).add_const (v ^ 2)
    simpa using h
  have hx : (u + 0) ^ 2 + v ^ 2 ≠ 0 := by simp only [add_zero]; exact hR.ne'
  have hs := hf.sqrt hx
  have hG'' : HasDerivAt Gf (deriv Gf (Real.sqrt (u ^ 2 + v ^ 2)))
      (Real.sqrt ((u + 0) ^ 2 + v ^ 2)) := by
    rw [add_zero]; exact hGd.hasDerivAt
  have hc := HasDerivAt.scomp (x := (0 : ℝ))
    (h := fun t : ℝ => Real.sqrt ((u + t) ^ 2 + v ^ 2)) hG'' hs
  have hm := hc.mul (gtb_ang_u u v hR)
  refine hm.congr_deriv ?_
  simp only [add_zero, Function.comp_apply]
  congr 2
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- The `v`-derivative of the `k`-th term: `G(√(u²+(v+t)²)) e^{2iϑ}(u,v+t)`. -/
private lemma gtb_prod_v (Gf : ℝ → ℂ) (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2)
    (hGd : DifferentiableAt ℝ Gf (Real.sqrt (u ^ 2 + v ^ 2))) :
    HasDerivAt (fun t : ℝ => Gf (Real.sqrt (u ^ 2 + (v + t) ^ 2)) * angularTwo (u, v + t))
      (((v / Real.sqrt (u ^ 2 + v ^ 2) : ℝ) • deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))) *
          angularTwo (u, v) +
        Gf (Real.sqrt (u ^ 2 + v ^ 2)) *
          (2 * Complex.I * (u : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 /
            ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2)) 0 := by
  have hf : HasDerivAt (fun t : ℝ => u ^ 2 + (v + t) ^ 2) (2 * v) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_add v).pow 2).const_add (u ^ 2)
    simpa using h
  have hx : u ^ 2 + (v + 0) ^ 2 ≠ 0 := by simp only [add_zero]; exact hR.ne'
  have hs := hf.sqrt hx
  have hG'' : HasDerivAt Gf (deriv Gf (Real.sqrt (u ^ 2 + v ^ 2)))
      (Real.sqrt (u ^ 2 + (v + 0) ^ 2)) := by
    rw [add_zero]; exact hGd.hasDerivAt
  have hc := HasDerivAt.scomp (x := (0 : ℝ))
    (h := fun t : ℝ => Real.sqrt (u ^ 2 + (v + t) ^ 2)) hG'' hs
  have hm := hc.mul (gtb_ang_v u v hR)
  refine hm.congr_deriv ?_
  simp only [add_zero, Function.comp_apply]
  congr 2
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- Norm bound for the `u`-derivative of the product. -/
private lemma gtb_bound_u (Gr gd : ℂ) (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    ‖((u / Real.sqrt (u ^ 2 + v ^ 2) : ℝ) • gd) * angularTwo (u, v) +
        Gr * (-(2 * Complex.I * (v : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2) /
            ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2)‖ ≤
      |u| / Real.sqrt (u ^ 2 + v ^ 2) * ‖gd‖ + ‖Gr‖ * (2 * |v| / (u ^ 2 + v ^ 2)) := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_smul, gtb_norm_angTwo u v hR, gtb_norm_du u v hR,
    Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.2 hR), mul_one]

/-- Norm bound for the `v`-derivative of the product. -/
private lemma gtb_bound_v (Gr gd : ℂ) (u v : ℝ) (hR : 0 < u ^ 2 + v ^ 2) :
    ‖((v / Real.sqrt (u ^ 2 + v ^ 2) : ℝ) • gd) * angularTwo (u, v) +
        Gr * (2 * Complex.I * (u : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 /
            ((u ^ 2 + v ^ 2 : ℝ) : ℂ) ^ 2)‖ ≤
      |v| / Real.sqrt (u ^ 2 + v ^ 2) * ‖gd‖ + ‖Gr‖ * (2 * |u| / (u ^ 2 + v ^ 2)) := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_smul, gtb_norm_angTwo u v hR, gtb_norm_dv u v hR,
    Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.2 hR), mul_one]

theorem gaussTermBound : UnforcedLeray.Short.IIIa.GaussTermBound := by
  intro Gf CG hG c k z hz
  have hv0 : z.2 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    norm_num at hz
  have hv2 : 1 / 4 < z.2 ^ 2 := by nlinarith [sq_abs z.2, abs_nonneg z.2]
  have hR : 0 < (z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2 := by
    have := sq_nonneg (z.1 + (k : ℝ) * c)
    linarith
  have hr0 : 0 < Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) := Real.sqrt_pos.2 hR
  have hr2 : Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) ^ 2 = (z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2 :=
    Real.sq_sqrt hR.le
  have hvr : |z.2| ≤ Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg (z.1 + (k : ℝ) * c)])
  have hhalf : 1 / 2 < Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) := by linarith
  have hsum : |z.1 + (k : ℝ) * c| + |z.2| ≤ 2 * Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) := by
    nlinarith [sq_abs (z.1 + (k : ℝ) * c), sq_abs z.2, abs_nonneg (z.1 + (k : ℝ) * c),
      abs_nonneg z.2, sq_nonneg (|z.1 + (k : ℝ) * c| - |z.2|)]
  have hGr : DifferentiableAt ℝ Gf (Real.sqrt ((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2)) :=
    (hG _ hhalf.le).1
  have hGb := (hG _ hhalf.le).2
  -- differentiability of the term
  have hsq : DifferentiableAt ℝ (fun w : ℝ × ℝ => (w.1 + (k : ℝ) * c) ^ 2 + w.2 ^ 2) z := by
    fun_prop
  have hdsq := hsq.sqrt hR.ne'
  have hdG : DifferentiableAt ℝ (fun w : ℝ × ℝ => Gf (Real.sqrt ((w.1 + (k : ℝ) * c) ^ 2 + w.2 ^ 2))) z :=
    DifferentiableAt.comp z hGr hdsq
  have hdA : DifferentiableAt ℝ (fun w : ℝ × ℝ => angularTwo (w.1 + (k : ℝ) * c, w.2)) z := by
    have hn : DifferentiableAt ℝ (fun w : ℝ × ℝ =>
        (((w.1 + (k : ℝ) * c : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * Complex.I) ^ 2) z := by fun_prop
    have hd : DifferentiableAt ℝ (fun w : ℝ × ℝ =>
        ((((w.1 + (k : ℝ) * c) ^ 2 + w.2 ^ 2 : ℝ)) : ℂ)) z := by fun_prop
    have hdz : ((((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast hR.ne'
    have hinv := hd.inv hdz
    have hmul := hn.mul hinv
    have hfun : (fun w : ℝ × ℝ => angularTwo (w.1 + (k : ℝ) * c, w.2)) =
        fun w : ℝ × ℝ => (((w.1 + (k : ℝ) * c : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * Complex.I) ^ 2 *
          ((((w.1 + (k : ℝ) * c) ^ 2 + w.2 ^ 2 : ℝ)) : ℂ)⁻¹ := by
      funext w
      unfold angularTwo
      rw [div_eq_mul_inv]
    rw [hfun]
    exact hmul
  have hdT : DifferentiableAt ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) z := hdG.mul hdA
  refine ⟨hdT, ?_⟩
  set u : ℝ := z.1 + (k : ℝ) * c with hu
  set v : ℝ := z.2 with hv
  set R : ℝ := u ^ 2 + v ^ 2 with hRdef
  set r : ℝ := Real.sqrt R with hrdef
  set F : ℝ × ℝ → ℂ := fun w : ℝ × ℝ => gaussTerm Gf c w k with hF
  have hFd : DifferentiableAt ℝ F z := hdT
  -- partial derivatives along the two coordinate lines
  have hline1 : HasDerivAt (fun t : ℝ => ((z.1 + t, z.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add z.1).prodMk (hasDerivAt_const (0 : ℝ) z.2)
  have hline2 : HasDerivAt (fun t : ℝ => ((z.1, z.2 + t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) z.1).prodMk ((hasDerivAt_id' (0 : ℝ)).const_add z.2)
  have hpt1 : z = (z.1 + 0, z.2) := by simp
  have hpt2 : z = (z.1, z.2 + 0) := by simp
  have hD1 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hFd.hasFDerivAt hline1 hpt1
  have hD2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hFd.hasFDerivAt hline2 hpt2
  have hGr' : DifferentiableAt ℝ Gf r := hGr
  have hfun1 : (fun t : ℝ => F (z.1 + t, z.2)) =
      fun t : ℝ => Gf (Real.sqrt ((u + t) ^ 2 + v ^ 2)) * angularTwo (u + t, v) := by
    funext t
    show Gf (Real.sqrt ((z.1 + t + (k : ℝ) * c) ^ 2 + z.2 ^ 2)) *
        angularTwo (z.1 + t + (k : ℝ) * c, z.2) = _
    rw [show z.1 + t + (k : ℝ) * c = u + t by rw [hu]; ring]
  have hfun2 : (fun t : ℝ => F (z.1, z.2 + t)) =
      fun t : ℝ => Gf (Real.sqrt (u ^ 2 + (v + t) ^ 2)) * angularTwo (u, v + t) := by
    funext t
    rfl
  have h1' := gtb_prod_u Gf u v hR hGr
  have h2' := gtb_prod_v Gf u v hR hGr
  rw [← hfun1] at h1'
  rw [← hfun2] at h2'
  have key1 := hD1.unique h1'
  have key2 := hD2.unique h2'
  -- the gradient of the term along the two coordinate directions
  have hdecomp : ∀ x : ℝ × ℝ,
      fderiv ℝ F z x = x.1 • fderiv ℝ F z (1, 0) + x.2 • fderiv ℝ F z (0, 1) := by
    intro x
    have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
  have hopn : ‖fderiv ℝ F z‖ ≤ ‖fderiv ℝ F z (1, 0)‖ + ‖fderiv ℝ F z (0, 1)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
    rw [hdecomp x]
    calc ‖x.1 • fderiv ℝ F z (1, 0) + x.2 • fderiv ℝ F z (0, 1)‖
        ≤ ‖x.1 • fderiv ℝ F z (1, 0)‖ + ‖x.2 • fderiv ℝ F z (0, 1)‖ := norm_add_le _ _
      _ = ‖x.1‖ * ‖fderiv ℝ F z (1, 0)‖ + ‖x.2‖ * ‖fderiv ℝ F z (0, 1)‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ ‖x‖ * ‖fderiv ℝ F z (1, 0)‖ + ‖x‖ * ‖fderiv ℝ F z (0, 1)‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le x) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_snd_le x) (norm_nonneg _))
      _ = (‖fderiv ℝ F z (1, 0)‖ + ‖fderiv ℝ F z (0, 1)‖) * ‖x‖ := by ring
  -- norms of the two partial derivatives
  have ha := gtb_norm_angTwo u v hR
  have hn0 : ‖gaussTerm Gf c z k‖ = ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ := by
    show ‖Gf (Real.sqrt (u ^ 2 + v ^ 2)) * angularTwo (u, v)‖ = _
    rw [norm_mul, ha, mul_one]
  have b1 := gtb_bound_u (Gf (Real.sqrt (u ^ 2 + v ^ 2))) (deriv Gf (Real.sqrt (u ^ 2 + v ^ 2)))
    u v hR
  have b2 := gtb_bound_v (Gf (Real.sqrt (u ^ 2 + v ^ 2))) (deriv Gf (Real.sqrt (u ^ 2 + v ^ 2)))
    u v hR
  rw [← key1] at b1
  rw [← key2] at b2
  -- elementary inequalities
  have hS : 0 < Real.sqrt (u ^ 2 + v ^ 2) := hr0
  have hRpos : 0 < u ^ 2 + v ^ 2 := hR
  have hsq2 : Real.sqrt (u ^ 2 + v ^ 2) ^ 2 = u ^ 2 + v ^ 2 := hr2
  have hsumS : |u| + |v| ≤ 2 * Real.sqrt (u ^ 2 + v ^ 2) := hsum
  have hhalfS : 1 / 2 < Real.sqrt (u ^ 2 + v ^ 2) := hhalf
  have hq1 : (|u| + |v|) / Real.sqrt (u ^ 2 + v ^ 2) ≤ 2 := by
    rw [div_le_iff₀ hS]
    linarith
  have hGbS : ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ + ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ ≤
      CG * Real.exp (-(R / 16)) := by
    have h := hGb
    rw [hr2] at h
    exact h
  have hA : |u| / Real.sqrt (u ^ 2 + v ^ 2) * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ +
      |v| / Real.sqrt (u ^ 2 + v ^ 2) * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ ≤
      2 * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ := by
    have e : |u| / Real.sqrt (u ^ 2 + v ^ 2) * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ +
        |v| / Real.sqrt (u ^ 2 + v ^ 2) * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ =
        ((|u| + |v|) / Real.sqrt (u ^ 2 + v ^ 2)) * ‖deriv Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
  have hC : ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ * (2 * |v| / (u ^ 2 + v ^ 2)) +
      ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ * (2 * |u| / (u ^ 2 + v ^ 2)) ≤
      8 * ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ := by
    have e : ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ * (2 * |v| / (u ^ 2 + v ^ 2)) +
        ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ * (2 * |u| / (u ^ 2 + v ^ 2)) =
        ‖Gf (Real.sqrt (u ^ 2 + v ^ 2))‖ * (2 * (|u| + |v|) / (u ^ 2 + v ^ 2)) := by
      ring
    rw [e]
    have hX : 2 * (|u| + |v|) / (u ^ 2 + v ^ 2) ≤ 8 := by
      rw [div_le_iff₀ hRpos]
      nlinarith [hsumS, hhalfS, hsq2, mul_pos hS (by linarith : (0 : ℝ) < 2 * Real.sqrt (u ^ 2 + v ^ 2) - 1)]
    have := mul_le_mul_of_nonneg_left hX (norm_nonneg (Gf (Real.sqrt (u ^ 2 + v ^ 2))))
    linarith
  have h10 : 10 * CG * Real.exp (-(R / 16)) = 10 * (CG * Real.exp (-(R / 16))) := by ring
  rw [hn0, h10]
  linarith [b1, b2, hA, hC, hGbS, hopn, norm_nonneg (Gf (Real.sqrt (u ^ 2 + v ^ 2))),
    norm_nonneg (deriv Gf (Real.sqrt (u ^ 2 + v ^ 2)))]

end UnforcedLeray.Short.IIIa
