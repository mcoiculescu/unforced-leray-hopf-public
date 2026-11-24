import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_4.Termwise

/-!
# Termwise differentiation of the Gaussian lattice sum (`HpTsumGrad`, source lines 4991-4994)

Proves `HpTsumGrad ν` for `ν > 0`: for `s > 0`, `B`, `x`, the series `∑_j mgrad (gjPsi ν s B j) x`
is summable and `mgrad` commutes with the sum over `j`.

Strategy: the explicit line-derivative formula `tw_fderiv_gjPsi` gives a pointwise bound
`‖fderiv (gjPsi_j) y‖ ≤ K (1+|x_j|)^3 exp(-|x_j|²/(4a))`.  On the ball `B(x,1)` this is dominated
by a summable Gaussian majorant `K' (1+|x.1-jc|)^3 exp(-(1/(8a))(x.1-jc)^2)`, which gives the
locally uniform derivative bound for `hasFDerivAt_tsum_of_isPreconnected`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `|u·z| ≤ 2 |u| |z|` for the sup-norm dot product on `ℝ × ℝ`. -/
lemma tsg_dot_le (u z : ℝ × ℝ) : |u.1 * z.1 + u.2 * z.2| ≤ 2 * ‖u‖ * ‖z‖ := by
  have h1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have h3 : |z.1| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le z
  have h4 : |z.2| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le z
  calc |u.1 * z.1 + u.2 * z.2| ≤ |u.1 * z.1| + |u.2 * z.2| := abs_add_le _ _
    _ = |u.1| * |z.1| + |u.2| * |z.2| := by rw [abs_mul, abs_mul]
    _ ≤ ‖u‖ * ‖z‖ + ‖u‖ * ‖z‖ :=
        add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖u‖ * ‖z‖ := by ring

/-- Real-variable core of the pointwise derivative bound. -/
lemma tsg_core (c a T b r P Q R nv : ℝ) (hc : 0 ≤ c) (ha : 1 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hnv : 0 ≤ nv) (hP : |P| ≤ 2 * r * nv) (hQ : |Q| ≤ 2 * b * r ^ 2)
    (hR : |R| ≤ 4 * b * r * nv) :
    |c * ((T + Q / (2 * a)) * P - R)| ≤ c * ((2 * |T| + 6 * b) * (1 + r) ^ 3 * nv) := by
  have hQa : |Q / (2 * a)| ≤ b * r ^ 2 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a),
      div_le_iff₀ (by linarith : (0:ℝ) < 2 * a)]
    nlinarith [abs_nonneg Q, mul_nonneg (mul_nonneg hb (sq_nonneg r)) (sub_nonneg.mpr ha)]
  have hX : |T + Q / (2 * a)| ≤ |T| + b * r ^ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hF : |(T + Q / (2 * a)) * P - R| ≤ (|T| + b * r ^ 2) * (2 * r * nv) + 4 * b * r * nv := by
    have e : (T + Q / (2 * a)) * P - R = (T + Q / (2 * a)) * P + -R := by ring
    rw [e]
    calc |(T + Q / (2 * a)) * P + -R| ≤ |(T + Q / (2 * a)) * P| + |-R| := abs_add_le _ _
      _ = |T + Q / (2 * a)| * |P| + |R| := by rw [abs_mul, abs_neg]
      _ ≤ (|T| + b * r ^ 2) * (2 * r * nv) + 4 * b * r * nv :=
          add_le_add (mul_le_mul hX hP (abs_nonneg _)
            (add_nonneg (abs_nonneg T) (mul_nonneg hb (sq_nonneg r)))) hR
  have hkey' : (|T| + b * r ^ 2) * (2 * r) + 4 * b * r ≤ (2 * |T| + 6 * b) * (1 + r) ^ 3 := by
    have h1 : r ≤ (1 + r) ^ 3 := by nlinarith [pow_nonneg hr 2, pow_nonneg hr 3]
    have h2 : r ^ 3 ≤ (1 + r) ^ 3 := pow_le_pow_left₀ hr (by linarith) 3
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg T), mul_le_mul_of_nonneg_left h2 hb,
      mul_le_mul_of_nonneg_left h1 hb]
  have hkey : (|T| + b * r ^ 2) * (2 * r * nv) + 4 * b * r * nv
      ≤ (2 * |T| + 6 * b) * (1 + r) ^ 3 * nv := by
    nlinarith [mul_le_mul_of_nonneg_right hkey' hnv]
  calc |c * ((T + Q / (2 * a)) * P - R)| = c * |(T + Q / (2 * a)) * P - R| := by
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ c * ((|T| + b * r ^ 2) * (2 * r * nv) + 4 * b * r * nv) :=
        mul_le_mul_of_nonneg_left hF hc
    _ ≤ c * ((2 * |T| + 6 * b) * (1 + r) ^ 3 * nv) := mul_le_mul_of_nonneg_left hkey hc

/-- Pointwise operator-norm bound on the derivative of the `j`-th summand. -/
lemma tsg_fderiv_opnorm_le (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (B : Mat3) (j : ℤ) (y : ℝ × ℝ) :
    ‖fderiv ℝ (gjPsi ν s B j) y‖ ≤
      (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (ageA ν s ^ 2)⁻¹) *
        ((2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)) *
          (1 + ‖xj ν j y‖) ^ 3) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [tw_fderiv_gjPsi, Real.norm_eq_abs]
  have hP := tsg_dot_le (xj ν j y) v
  have hQ : |(xj ν j y).1 * (merApply B (xj ν j y)).1 + (xj ν j y).2 * (merApply B (xj ν j y)).2|
      ≤ 2 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j y‖ ^ 2 := by
    refine (tsg_dot_le (xj ν j y) (merApply B (xj ν j y))).trans ?_
    calc 2 * ‖xj ν j y‖ * ‖merApply B (xj ν j y)‖
        ≤ 2 * ‖xj ν j y‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j y‖) :=
          mul_le_mul_of_nonneg_left (gp_merApply_norm_le B _) (by positivity)
      _ = 2 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j y‖ ^ 2 := by ring
  have hR : |v.1 * (merApply B (xj ν j y)).1 + (xj ν j y).1 * (merApply B v).1
      + (v.2 * (merApply B (xj ν j y)).2 + (xj ν j y).2 * (merApply B v).2)|
      ≤ 4 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j y‖ * ‖v‖ := by
    have e : v.1 * (merApply B (xj ν j y)).1 + (xj ν j y).1 * (merApply B v).1
        + (v.2 * (merApply B (xj ν j y)).2 + (xj ν j y).2 * (merApply B v).2)
        = (v.1 * (merApply B (xj ν j y)).1 + v.2 * (merApply B (xj ν j y)).2)
          + ((xj ν j y).1 * (merApply B v).1 + (xj ν j y).2 * (merApply B v).2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 := tsg_dot_le v (merApply B (xj ν j y))
    have h2 := tsg_dot_le (xj ν j y) (merApply B v)
    have h3 : 2 * ‖v‖ * ‖merApply B (xj ν j y)‖
        ≤ 2 * ‖v‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖xj ν j y‖) :=
      mul_le_mul_of_nonneg_left (gp_merApply_norm_le B _) (by positivity)
    have h4 : 2 * ‖xj ν j y‖ * ‖merApply B v‖
        ≤ 2 * ‖xj ν j y‖ * ((|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (gp_merApply_norm_le B _) (by positivity)
    linarith
  have hcore := tsg_core
    (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (ageA ν s ^ 2)⁻¹)
    (ageA ν s) (merTrace B) (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) ‖xj ν j y‖ _ _ _ ‖v‖
    (by positivity) ha1 (by positivity) (norm_nonneg _) (norm_nonneg _) hP hQ hR
  exact hcore.trans (le_of_eq (by ring))

/-- Gaussian-majorant bound on the derivative of the `j`-th summand, uniformly on `B(x,1)`. -/
lemma tsg_ball_bound (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (B : Mat3) (x : ℝ × ℝ) (j : ℤ)
    (y : ℝ × ℝ) (hy : y ∈ Metric.ball x 1) :
    ‖fderiv ℝ (gjPsi ν s B j) y‖ ≤
      (2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)) * (ageA ν s ^ 2)⁻¹ *
        (8 * (2 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s))) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha : 0 < ageA ν s := by linarith
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have d1 : |y.1 - x.1| < 1 := by
    have h1 : |y.1 - x.1| ≤ ‖y - x‖ := by
      have := norm_fst_le (y - x)
      simpa [Real.norm_eq_abs] using this
    linarith
  have d2 : |y.2 - x.2| < 1 := by
    have h1 : |y.2 - x.2| ≤ ‖y - x‖ := by
      have := norm_snd_le (y - x)
      simpa [Real.norm_eq_abs] using this
    linarith
  have hy2 : 1 + |y.2| ≤ 2 + |x.2| := by
    have := abs_sub_abs_le_abs_sub y.2 x.2
    linarith
  have hp1 : 1 + |y.1 - (j : ℝ) * cOf ν| ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν|) := by
    have h := abs_sub_abs_le_abs_sub (y.1 - (j : ℝ) * cOf ν) (x.1 - (j : ℝ) * cOf ν)
    have e : (y.1 - (j : ℝ) * cOf ν) - (x.1 - (j : ℝ) * cOf ν) = y.1 - x.1 := by ring
    rw [e] at h
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν)]
  have hr1 : 1 + ‖xj ν j y‖ ≤ (2 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|)) :=
    (gp_one_add_norm ν j y).trans (mul_le_mul hy2 hp1 (by positivity) (by positivity))
  have hcube : (1 + ‖xj ν j y‖) ^ 3 ≤ 8 * (2 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity) hr1 3
    calc (1 + ‖xj ν j y‖) ^ 3
        ≤ ((2 + |x.2|) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν|))) ^ 3 := h
      _ = 8 * (2 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by ring
  have hd : (x.1 - y.1) ^ 2 ≤ 1 := by
    have h0 : |x.1 - y.1| < 1 := by rw [abs_sub_comm]; exact d1
    nlinarith [sq_abs (x.1 - y.1), abs_nonneg (x.1 - y.1)]
  have hsq : (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ 2 * (y.1 - (j : ℝ) * cOf ν) ^ 2 + 2 := by
    nlinarith [sq_nonneg ((y.1 - (j : ℝ) * cOf ν) - (x.1 - y.1))]
  have hβ0 : 0 ≤ 1 / (8 * ageA ν s) := (div_pos one_pos (by linarith)).le
  have hexp : Real.exp (-(1 / (4 * ageA ν s)) * (y.1 - (j : ℝ) * cOf ν) ^ 2) ≤
      Real.exp (1 / (4 * ageA ν s)) *
        Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h4 : 1 / (4 * ageA ν s) = 2 * (1 / (8 * ageA ν s)) := by ring
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left hsq hβ0]
  have hE : Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) ≤
      Real.exp (1 / (4 * ageA ν s)) *
        Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    (gp_exp_le ν s ha j y).trans hexp
  have hpt := tsg_fderiv_opnorm_le ν s hν hs B j y
  calc ‖fderiv ℝ (gjPsi ν s B j) y‖
      ≤ (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (ageA ν s ^ 2)⁻¹) *
          ((2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)) *
            (1 + ‖xj ν j y‖) ^ 3) := hpt
    _ = ((ageA ν s ^ 2)⁻¹ * (2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|))) *
          (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) * (1 + ‖xj ν j y‖) ^ 3) := by ring
    _ ≤ ((ageA ν s ^ 2)⁻¹ * (2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|))) *
          ((Real.exp (1 / (4 * ageA ν s)) *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) *
            (8 * (2 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hE hcube (by positivity) (by positivity)
    _ = (2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)) * (ageA ν s ^ 2)⁻¹ *
        (8 * (2 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s))) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

/-- Operator norm of a continuous linear form on `ℝ × ℝ` applied to a unit vector. -/
lemma tsg_norm_apply_le (L : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) : ‖L v‖ ≤ ‖L‖ :=
  (L.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)

lemma tsg_ei0_le : ‖ei 0‖ ≤ 1 := by simp [ei, Prod.norm_def]

lemma tsg_ei1_le : ‖ei 1‖ ≤ 1 := by simp [ei, Prod.norm_def]

lemma tsg_mgrad_norm_le (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ‖mgrad f x‖ ≤ ‖fderiv ℝ f x‖ := by
  unfold mgrad
  rw [Prod.norm_def]
  exact max_le (tsg_norm_apply_le _ _ tsg_ei0_le) (tsg_norm_apply_le _ _ tsg_ei1_le)

theorem hpTsumGrad_proof (ν : ℝ) : HpTsumGrad ν := by
  intro hν s hs B x
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha : 0 < ageA ν s := by linarith
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hβ : 0 < 1 / (8 * ageA ν s) := div_pos one_pos (by linarith)
  have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
  have hu : Summable (fun j : ℤ =>
      (2 * |merTrace B| + 6 * (|B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|)) * (ageA ν s ^ 2)⁻¹ *
        (8 * (2 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s))) *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) :=
    (gp_poly_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hβ hc).mul_left _
  have hf0 : Summable (fun j : ℤ => gjPsi ν s B j x) := by
    obtain ⟨K, hK⟩ := gp_psi_bound ν s ha B x
    exact Summable.of_norm_bounded
      ((gp_poly_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc).mul_left K) (fun j => hK j)
  have hmem : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
  have hsumC : Summable (fun j : ℤ => fderiv ℝ (gjPsi ν s B j) x) :=
    Summable.of_norm_bounded hu (fun j => tsg_ball_bound ν s hν hs B x j x hmem)
  have hsumM : Summable (fun j : ℤ => mgrad (gjPsi ν s B j) x) :=
    Summable.of_norm_bounded hu
      (fun j => (tsg_mgrad_norm_le _ _).trans (tsg_ball_bound ν s hν hs B x j x hmem))
  refine ⟨hsumM, ?_⟩
  have hF : HasFDerivAt (fun y => ∑' j : ℤ, gjPsi ν s B j y)
      (∑' j : ℤ, fderiv ℝ (gjPsi ν s B j) x) x :=
    hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
      (fun j y _ => (tw_gjPsi_diff ν s j B y).hasFDerivAt)
      (fun j y hy => tsg_ball_bound ν s hν hs B x j y hy) hmem hf0 hmem
  have hcomp : ∀ v : ℝ × ℝ, fderiv ℝ (fun y => ∑' j : ℤ, gjPsi ν s B j y) x v
      = ∑' j : ℤ, fderiv ℝ (gjPsi ν s B j) x v := by
    intro v
    rw [hF.fderiv]
    have := (ContinuousLinearMap.apply ℝ ℝ v).map_tsum hsumC
    simpa using this
  have hs0 : Summable (fun j : ℤ => fderiv ℝ (gjPsi ν s B j) x (ei 0)) :=
    Summable.of_norm_bounded hu
      (fun j => (tsg_norm_apply_le _ _ tsg_ei0_le).trans (tsg_ball_bound ν s hν hs B x j x hmem))
  have hs1 : Summable (fun j : ℤ => fderiv ℝ (gjPsi ν s B j) x (ei 1)) :=
    Summable.of_norm_bounded hu
      (fun j => (tsg_norm_apply_le _ _ tsg_ei1_le).trans (tsg_ball_bound ν s hν hs B x j x hmem))
  unfold mgrad
  rw [hcomp (ei 0), hcomp (ei 1)]
  exact ((hs0.hasSum).prodMk hs1.hasSum).tsum_eq.symm

end UnforcedLeray.Short.PartIIIb.Concrete
