import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4

/-!
# `PartIII-b:C/grad/2/4/2`: Gaussian-weighted bound on the `y`-derivative of `sV`

Source `the November 2 reference manuscript` lines 4973-4980 and 4741-4745.
`sV ν y Mt D t = exp(-|y|²/(4a)) · G(y)` with `a = ageA ν t ≥ 1`, where `G` is a polynomial of
degree `4` in `y` whose coefficients are polynomial in `u = a⁻¹ ∈ (0,1]`, `ν`, and the entries of
`Mt, D`. Its line derivative is computed by the product rule; each piece is bounded by the entry
bounds and `|y|, |v|`, giving a bound `C ‖v‖ (1+|y|)⁵ e^{-|y|²/(4a)}` with `C = 60 (1+K)(1+ν)`,
`K = K1 + K2`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Algebraic helpers -/

theorem svb_abs_mul {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) (hX : 0 ≤ X) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hX

theorem svb_sum4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

theorem svb_sum6 (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  linarith

/-! ## Quadratic forms, their line derivatives, and the factored form of `sV` -/

/-- `2 w₁(M₀₀w₁+M₀₂w₂) + 2w₂(M₂₀w₁+M₂₂w₂)`. -/
def svQf (M : Mat3) (w : ℝ × ℝ) : ℝ :=
  2 * w.1 * (M 0 0 * w.1 + M 0 2 * w.2) + 2 * w.2 * (M 2 0 * w.1 + M 2 2 * w.2)

/-- Directional derivative of `svQf M` at `y` along `v`. -/
def svQfD (M : Mat3) (y v : ℝ × ℝ) : ℝ :=
  4 * M 0 0 * y.1 * v.1 + 2 * (M 0 2 + M 2 0) * (v.1 * y.2 + y.1 * v.2) + 4 * M 2 2 * y.2 * v.2

/-- Directional derivative of `sq2` at `y` along `v`. -/
def svSD (y v : ℝ × ℝ) : ℝ := 2 * y.1 * v.1 + 2 * y.2 * v.2

/-- The polynomial factor: `sV ν w Mt D t = exp(-sq2 w/(4a)) · svGc ν a⁻¹ Mt D w`. -/
def svGc (ν u : ℝ) (Mt D : Mat3) (w : ℝ × ℝ) : ℝ :=
  (-2 * u) * (D 0 0 + D 2 2) + (2 * ν * u ^ 2) * (Mt 0 0 + Mt 2 2)
    + (-(u ^ 2) / 2) * svQf D w + (ν * u ^ 3) * svQf Mt w
    + (-(ν * u ^ 3 / 2) * (Mt 0 0 + Mt 2 2)) * sq2 w
    + (-(ν * u ^ 4) / 8) * (sq2 w * svQf Mt w)

/-- Directional derivative of `svGc` at `y` along `v`. -/
def svGD (ν u : ℝ) (Mt D : Mat3) (y v : ℝ × ℝ) : ℝ :=
  (-(u ^ 2) / 2) * svQfD D y v + (ν * u ^ 3) * svQfD Mt y v
    + (-(ν * u ^ 3 / 2) * (Mt 0 0 + Mt 2 2)) * svSD y v
    + (-(ν * u ^ 4) / 8) * (svSD y v * svQf Mt y + sq2 y * svQfD Mt y v)

theorem sV_eq_svGc (ν t : ℝ) (Mt D : Mat3) (w : ℝ × ℝ) (ht : 0 < ageA ν t) :
    sV ν w Mt D t = Real.exp (-(sq2 w) / (4 * ageA ν t)) * svGc ν (ageA ν t)⁻¹ Mt D w := by
  have ha : ageA ν t ≠ 0 := ht.ne'
  unfold sV svGc svQf
  generalize ageA ν t = a at *
  generalize Real.exp (-(sq2 w) / (4 * a)) = E
  field_simp
  ring

theorem svQf_line (M : Mat3) (y v : ℝ × ℝ) :
    HasDerivAt (fun τ : ℝ => svQf M (y + τ • v)) (svQfD M y v) 0 := by
  have hc1 : HasDerivAt (fun τ : ℝ => y.1 + τ * v.1) v.1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add y.1
  have hc2 : HasDerivAt (fun τ : ℝ => y.2 + τ * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add y.2
  have e : (fun τ : ℝ => svQf M (y + τ • v)) = fun τ : ℝ =>
      2 * (y.1 + τ * v.1) * (M 0 0 * (y.1 + τ * v.1) + M 0 2 * (y.2 + τ * v.2))
      + 2 * (y.2 + τ * v.2) * (M 2 0 * (y.1 + τ * v.1) + M 2 2 * (y.2 + τ * v.2)) := by
    funext τ
    simp only [svQf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [e]
  have hm1 : HasDerivAt (fun τ : ℝ => M 0 0 * (y.1 + τ * v.1) + M 0 2 * (y.2 + τ * v.2))
      (M 0 0 * v.1 + M 0 2 * v.2) 0 := (hc1.const_mul _).add (hc2.const_mul _)
  have hm2 : HasDerivAt (fun τ : ℝ => M 2 0 * (y.1 + τ * v.1) + M 2 2 * (y.2 + τ * v.2))
      (M 2 0 * v.1 + M 2 2 * v.2) 0 := (hc1.const_mul _).add (hc2.const_mul _)
  have A1 := (hc1.const_mul 2).mul hm1
  have A2 := (hc2.const_mul 2).mul hm2
  refine (A1.add A2).congr_deriv ?_
  unfold svQfD
  ring

theorem svSq2_line (y v : ℝ × ℝ) :
    HasDerivAt (fun τ : ℝ => sq2 (y + τ • v)) (svSD y v) 0 := by
  have hc1 : HasDerivAt (fun τ : ℝ => y.1 + τ * v.1) v.1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add y.1
  have hc2 : HasDerivAt (fun τ : ℝ => y.2 + τ * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add y.2
  have e : (fun τ : ℝ => sq2 (y + τ • v)) = fun τ : ℝ =>
      (y.1 + τ * v.1) * (y.1 + τ * v.1) + (y.2 + τ * v.2) * (y.2 + τ * v.2) := by
    funext τ
    simp only [sq2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e]
  refine ((hc1.mul hc1).add (hc2.mul hc2)).congr_deriv ?_
  unfold svSD
  ring

theorem svExp_line (y v : ℝ × ℝ) (a : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (-(sq2 (y + τ • v)) / (4 * a)))
      (Real.exp (-(sq2 y) / (4 * a)) * (-(svSD y v) / (4 * a))) 0 := by
  have h := (((svSq2_line y v).neg).div_const (4 * a)).exp
  simpa using h

theorem svGc_line (ν u : ℝ) (Mt D : Mat3) (y v : ℝ × ℝ) :
    HasDerivAt (fun τ : ℝ => svGc ν u Mt D (y + τ • v)) (svGD ν u Mt D y v) 0 := by
  have h1 := (svQf_line D y v).const_mul (-(u ^ 2) / 2)
  have h2 := (svQf_line Mt y v).const_mul (ν * u ^ 3)
  have h3 := (svSq2_line y v).const_mul (-(ν * u ^ 3 / 2) * (Mt 0 0 + Mt 2 2))
  have h4 := ((svSq2_line y v).mul (svQf_line Mt y v)).const_mul (-(ν * u ^ 4) / 8)
  have h := ((((hasDerivAt_const (0:ℝ)
    ((-2 * u) * (D 0 0 + D 2 2) + (2 * ν * u ^ 2) * (Mt 0 0 + Mt 2 2))).add h1).add h2).add h3).add h4
  unfold svGc svGD
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_add]

theorem sV_line (ν t : ℝ) (Mt D : Mat3) (ht : 0 < ageA ν t) (y v : ℝ × ℝ) :
    HasDerivAt (fun τ : ℝ => sV ν (y + τ • v) Mt D t)
      (Real.exp (-(sq2 y) / (4 * ageA ν t)) * (-(svSD y v) / (4 * ageA ν t))
          * svGc ν (ageA ν t)⁻¹ Mt D y
        + Real.exp (-(sq2 y) / (4 * ageA ν t)) * svGD ν (ageA ν t)⁻¹ Mt D y v) 0 := by
  have hfun : (fun τ : ℝ => sV ν (y + τ • v) Mt D t) = fun τ : ℝ =>
      Real.exp (-(sq2 (y + τ • v)) / (4 * ageA ν t)) * svGc ν (ageA ν t)⁻¹ Mt D (y + τ • v) := by
    funext τ
    exact sV_eq_svGc ν t Mt D (y + τ • v) ht
  rw [hfun]
  have h := (svExp_line y v (ageA ν t)).mul (svGc_line ν (ageA ν t)⁻¹ Mt D y v)
  simp only [zero_smul, add_zero] at h
  exact h

theorem sV_diffAt (ν t : ℝ) (Mt D : Mat3) (ht : 0 < ageA ν t) (y : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w => sV ν w Mt D t) y := by
  have hfun : (fun w => sV ν w Mt D t) = fun w =>
      Real.exp (-(sq2 w) / (4 * ageA ν t)) * svGc ν (ageA ν t)⁻¹ Mt D w :=
    funext fun w => sV_eq_svGc ν t Mt D w ht
  rw [hfun]
  apply DifferentiableAt.mul
  · unfold sq2; fun_prop
  · unfold svGc svQf sq2; fun_prop

theorem sV_fderiv_eq (ν t : ℝ) (Mt D : Mat3) (ht : 0 < ageA ν t) (y v : ℝ × ℝ) :
    fderiv ℝ (fun w => sV ν w Mt D t) y v =
      Real.exp (-(sq2 y) / (4 * ageA ν t)) * (-(svSD y v) / (4 * ageA ν t))
          * svGc ν (ageA ν t)⁻¹ Mt D y
        + Real.exp (-(sq2 y) / (4 * ageA ν t)) * svGD ν (ageA ν t)⁻¹ Mt D y v := by
  rw [gp_fderiv_line _ y v (sV_diffAt ν t Mt D ht y)]
  exact (sV_line ν t Mt D ht y v).deriv

/-! ## Norm bounds -/

theorem svQf_abs (M : Mat3) (K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hM : ∀ i j, |M i j| ≤ K)
    (w : ℝ × ℝ) (hw1 : |w.1| ≤ R) (hw2 : |w.2| ≤ R) : |svQf M w| ≤ 8 * K * R ^ 2 := by
  unfold svQf
  exact sp_Q_bound (M 0 0) (M 0 2) (M 2 0) (M 2 2) w.1 w.2 K R hK hR
    (hM 0 0) (hM 0 2) (hM 2 0) (hM 2 2) hw1 hw2

theorem svQfD_abs (M : Mat3) (K R n : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hn : 0 ≤ n)
    (hM : ∀ i j, |M i j| ≤ K) (y v : ℝ × ℝ) (hy1 : |y.1| ≤ R) (hy2 : |y.2| ≤ R)
    (hv1 : |v.1| ≤ n) (hv2 : |v.2| ≤ n) : |svQfD M y v| ≤ 16 * K * R * n := by
  unfold svQfD
  have c4 : ∀ i j : Fin 3, |(4:ℝ) * M i j| ≤ 4 * K := fun i j => by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [hM i j]
  have c2 : |(2:ℝ) * (M 0 2 + M 2 0)| ≤ 4 * K := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := abs_add_le (M 0 2) (M 2 0)
    linarith [hM 0 2, hM 2 0]
  have a1 : |4 * M 0 0 * y.1 * v.1| ≤ 4 * K * R * n :=
    svb_abs_mul (svb_abs_mul (c4 0 0) hy1 (by linarith)) hv1
      (mul_nonneg (mul_nonneg (by linarith) hK) hR)
  have hs : |v.1 * y.2 + y.1 * v.2| ≤ 2 * R * n := by
    have := abs_add_le (v.1 * y.2) (y.1 * v.2)
    rw [abs_mul, abs_mul] at this
    nlinarith [mul_le_mul hv1 hy2 (abs_nonneg _) hn, mul_le_mul hy1 hv2 (abs_nonneg _) hR]
  have a2 : |2 * (M 0 2 + M 2 0) * (v.1 * y.2 + y.1 * v.2)| ≤ 8 * K * R * n := by
    have := svb_abs_mul c2 hs (by linarith)
    linarith
  have a3 : |4 * M 2 2 * y.2 * v.2| ≤ 4 * K * R * n :=
    svb_abs_mul (svb_abs_mul (c4 2 2) hy2 (by linarith)) hv2
      (mul_nonneg (mul_nonneg (by linarith) hK) hR)
  have t1 := abs_add_le (4 * M 0 0 * y.1 * v.1) (2 * (M 0 2 + M 2 0) * (v.1 * y.2 + y.1 * v.2))
  have t2 := abs_add_le (4 * M 0 0 * y.1 * v.1 + 2 * (M 0 2 + M 2 0) * (v.1 * y.2 + y.1 * v.2))
    (4 * M 2 2 * y.2 * v.2)
  linarith

theorem svSD_abs (R n : ℝ) (hR : 0 ≤ R) (hn : 0 ≤ n) (y v : ℝ × ℝ) (hy1 : |y.1| ≤ R)
    (hy2 : |y.2| ≤ R) (hv1 : |v.1| ≤ n) (hv2 : |v.2| ≤ n) : |svSD y v| ≤ 4 * R * n := by
  unfold svSD
  have c2 : |(2:ℝ)| ≤ 2 := by norm_num
  have a1 : |2 * y.1 * v.1| ≤ 2 * R * n :=
    svb_abs_mul (svb_abs_mul c2 hy1 (by norm_num)) hv1 (mul_nonneg (by norm_num) hR)
  have a2 : |2 * y.2 * v.2| ≤ 2 * R * n :=
    svb_abs_mul (svb_abs_mul c2 hy2 (by norm_num)) hv2 (mul_nonneg (by norm_num) hR)
  have := abs_add_le (2 * y.1 * v.1) (2 * y.2 * v.2)
  linarith

theorem sq2_abs (y : ℝ × ℝ) (R : ℝ) (hR : 0 ≤ R) (hy1 : |y.1| ≤ R) (hy2 : |y.2| ≤ R) :
    |sq2 y| ≤ 2 * R ^ 2 := by
  unfold sq2
  have e1 : y.1 ^ 2 ≤ R ^ 2 := by
    nlinarith [abs_mul_abs_self y.1, mul_le_mul hy1 hy1 (abs_nonneg _) hR]
  have e2 : y.2 ^ 2 ≤ R ^ 2 := by
    nlinarith [abs_mul_abs_self y.2, mul_le_mul hy2 hy2 (abs_nonneg _) hR]
  have e3 : 0 ≤ y.1 ^ 2 := sq_nonneg _
  have e4 : 0 ≤ y.2 ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

theorem svGc_abs (ν u K R : ℝ) (hν : 0 ≤ ν) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (hR : 0 ≤ R) (Mt D : Mat3) (hMt : ∀ i j, |Mt i j| ≤ K) (hD : ∀ i j, |D i j| ≤ K)
    (y : ℝ × ℝ) (hy1 : |y.1| ≤ R) (hy2 : |y.2| ≤ R) :
    |svGc ν u Mt D y| ≤ 24 * ((1 + K) * (1 + ν)) * (1 + R) ^ 4 := by
  have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
  have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le hu1
  have hu4 : u ^ 4 ≤ 1 := pow_le_one₀ hu0.le hu1
  have cKa : |-2 * u| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have cKp : |2 * ν * u ^ 2| ≤ 2 * ν := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg u))]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hν]
  have cD2 : |-(u ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [sq_nonneg u]
  have cM : |ν * u ^ 3| ≤ ν := by
    rw [abs_of_nonneg (mul_nonneg hν (pow_nonneg hu0.le 3))]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hν]
  have c3 : |-(ν * u ^ 3 / 2)| ≤ ν / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hu3 hν, mul_nonneg hν (pow_nonneg hu0.le 3)]
  have c4 : |-(ν * u ^ 4) / 8| ≤ ν / 8 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hu4 hν, mul_nonneg hν (pow_nonneg hu0.le 4)]
  have hT : |Mt 0 0 + Mt 2 2| ≤ 2 * K :=
    (abs_add_le _ _).trans (by linarith [hMt 0 0, hMt 2 2])
  have hTD : |D 0 0 + D 2 2| ≤ 2 * K :=
    (abs_add_le _ _).trans (by linarith [hD 0 0, hD 2 2])
  have hQD := svQf_abs D K R hK hR hD y hy1 hy2
  have hQM := svQf_abs Mt K R hK hR hMt y hy1 hy2
  have hs2 := sq2_abs y R hR hy1 hy2
  have b1 : |(-2 * u) * (D 0 0 + D 2 2)| ≤ 2 * (2 * K) := svb_abs_mul cKa hTD (by norm_num)
  have b2 : |(2 * ν * u ^ 2) * (Mt 0 0 + Mt 2 2)| ≤ (2 * ν) * (2 * K) :=
    svb_abs_mul cKp hT (by linarith)
  have b3 : |(-(u ^ 2) / 2) * svQf D y| ≤ (1 / 2) * (8 * K * R ^ 2) :=
    svb_abs_mul cD2 hQD (by norm_num)
  have b4 : |(ν * u ^ 3) * svQf Mt y| ≤ ν * (8 * K * R ^ 2) := svb_abs_mul cM hQM hν
  have b5 : |(-(ν * u ^ 3 / 2) * (Mt 0 0 + Mt 2 2)) * sq2 y|
      ≤ ((ν / 2) * (2 * K)) * (2 * R ^ 2) :=
    svb_abs_mul (svb_abs_mul c3 hT (by linarith)) hs2 (mul_nonneg (by linarith) (by linarith))
  have b6 : |(-(ν * u ^ 4) / 8) * (sq2 y * svQf Mt y)|
      ≤ (ν / 8) * ((2 * R ^ 2) * (8 * K * R ^ 2)) :=
    svb_abs_mul c4 (svb_abs_mul hs2 hQM (by positivity)) (by linarith)
  unfold svGc
  refine (svb_sum6 _ _ _ _ _ _).trans ?_
  have hA0 : 0 ≤ (1 + K) * (1 + ν) := mul_nonneg (by linarith) (by linarith)
  have hS1 : 1 ≤ 1 + R := by linarith
  have hS4 : 1 ≤ (1 + R) ^ 4 := one_le_pow₀ hS1
  have hAS : (1 + K) * (1 + ν) ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 := le_mul_of_one_le_right hA0 hS4
  have hAK : K ≤ (1 + K) * (1 + ν) := by nlinarith
  have hAKν : ν * K ≤ (1 + K) * (1 + ν) := by nlinarith
  have hR2 : R ^ 2 ≤ (1 + R) ^ 4 :=
    (pow_le_pow_left₀ hR (by linarith : R ≤ 1 + R) 2).trans (pow_le_pow_right₀ hS1 (by norm_num))
  have hR4 : R ^ 4 ≤ (1 + R) ^ 4 := pow_le_pow_left₀ hR (by linarith) 4
  have p1 : K ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 := hAK.trans hAS
  have p2 : ν * K ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 := hAKν.trans hAS
  have p3 : K * R ^ 2 ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 := mul_le_mul hAK hR2 (sq_nonneg R) hA0
  have p4 : ν * K * R ^ 2 ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 :=
    mul_le_mul hAKν hR2 (sq_nonneg R) hA0
  have p5 : ν * K * R ^ 4 ≤ (1 + K) * (1 + ν) * (1 + R) ^ 4 :=
    mul_le_mul hAKν hR4 (pow_nonneg hR 4) hA0
  linarith

theorem svGD_abs (ν u K R n : ℝ) (hν : 0 ≤ ν) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (hR : 0 ≤ R) (hn : 0 ≤ n) (Mt D : Mat3) (hMt : ∀ i j, |Mt i j| ≤ K)
    (hD : ∀ i j, |D i j| ≤ K) (y v : ℝ × ℝ) (hy1 : |y.1| ≤ R) (hy2 : |y.2| ≤ R)
    (hv1 : |v.1| ≤ n) (hv2 : |v.2| ≤ n) :
    |svGD ν u Mt D y v| ≤ 36 * ((1 + K) * (1 + ν)) * n * (1 + R) ^ 3 := by
  have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
  have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le hu1
  have hu4 : u ^ 4 ≤ 1 := pow_le_one₀ hu0.le hu1
  have cD2 : |-(u ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [sq_nonneg u]
  have cM : |ν * u ^ 3| ≤ ν := by
    rw [abs_of_nonneg (mul_nonneg hν (pow_nonneg hu0.le 3))]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hν]
  have c3 : |-(ν * u ^ 3 / 2)| ≤ ν / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hu3 hν, mul_nonneg hν (pow_nonneg hu0.le 3)]
  have c4 : |-(ν * u ^ 4) / 8| ≤ ν / 8 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hu4 hν, mul_nonneg hν (pow_nonneg hu0.le 4)]
  have hT : |Mt 0 0 + Mt 2 2| ≤ 2 * K :=
    (abs_add_le _ _).trans (by linarith [hMt 0 0, hMt 2 2])
  have hQD := svQfD_abs D K R n hK hR hn hD y v hy1 hy2 hv1 hv2
  have hQM := svQfD_abs Mt K R n hK hR hn hMt y v hy1 hy2 hv1 hv2
  have hSD := svSD_abs R n hR hn y v hy1 hy2 hv1 hv2
  have hQf := svQf_abs Mt K R hK hR hMt y hy1 hy2
  have hs2 := sq2_abs y R hR hy1 hy2
  have g1 : |(-(u ^ 2) / 2) * svQfD D y v| ≤ (1 / 2) * (16 * K * R * n) :=
    svb_abs_mul cD2 hQD (by norm_num)
  have g2 : |(ν * u ^ 3) * svQfD Mt y v| ≤ ν * (16 * K * R * n) := svb_abs_mul cM hQM hν
  have g3 : |(-(ν * u ^ 3 / 2) * (Mt 0 0 + Mt 2 2)) * svSD y v|
      ≤ ((ν / 2) * (2 * K)) * (4 * R * n) :=
    svb_abs_mul (svb_abs_mul c3 hT (by linarith)) hSD (mul_nonneg (by linarith) (by linarith))
  have i1 : |svSD y v * svQf Mt y| ≤ (4 * R * n) * (8 * K * R ^ 2) :=
    svb_abs_mul hSD hQf (mul_nonneg (mul_nonneg (by norm_num) hR) hn)
  have i2 : |sq2 y * svQfD Mt y v| ≤ (2 * R ^ 2) * (16 * K * R * n) :=
    svb_abs_mul hs2 hQM (by positivity)
  have i3 : |svSD y v * svQf Mt y + sq2 y * svQfD Mt y v|
      ≤ (4 * R * n) * (8 * K * R ^ 2) + (2 * R ^ 2) * (16 * K * R * n) :=
    (abs_add_le _ _).trans (by linarith)
  have g4 : |(-(ν * u ^ 4) / 8) * (svSD y v * svQf Mt y + sq2 y * svQfD Mt y v)|
      ≤ (ν / 8) * ((4 * R * n) * (8 * K * R ^ 2) + (2 * R ^ 2) * (16 * K * R * n)) :=
    svb_abs_mul c4 i3 (by linarith)
  unfold svGD
  refine (svb_sum4 _ _ _ _).trans ?_
  have hA0 : 0 ≤ (1 + K) * (1 + ν) := mul_nonneg (by linarith) (by linarith)
  have hS1 : 1 ≤ 1 + R := by linarith
  have hAK : K ≤ (1 + K) * (1 + ν) := by nlinarith
  have hAKν : ν * K ≤ (1 + K) * (1 + ν) := by nlinarith
  have hRS3 : R ≤ (1 + R) ^ 3 := by
    have h13 : (1 + R) ^ 1 ≤ (1 + R) ^ 3 := pow_le_pow_right₀ hS1 (by norm_num)
    rw [pow_one] at h13
    linarith
  have hR3S3 : R ^ 3 ≤ (1 + R) ^ 3 := pow_le_pow_left₀ hR (by linarith) 3
  have q1 : K * R * n ≤ (1 + K) * (1 + ν) * (1 + R) ^ 3 * n :=
    mul_le_mul_of_nonneg_right (mul_le_mul hAK hRS3 hR hA0) hn
  have q2 : ν * K * R * n ≤ (1 + K) * (1 + ν) * (1 + R) ^ 3 * n :=
    mul_le_mul_of_nonneg_right (mul_le_mul hAKν hRS3 hR hA0) hn
  have q3 : ν * K * R ^ 3 * n ≤ (1 + K) * (1 + ν) * (1 + R) ^ 3 * n :=
    mul_le_mul_of_nonneg_right (mul_le_mul hAKν hR3S3 (pow_nonneg hR 3) hA0) hn
  linarith

/-! ## The bound `PAMXSVBound` -/

theorem pamxSVBound : PAMXSVBound := by
  unfold PAMXSVBound
  intro ν hν K1 K2 hK1 hK2
  refine ⟨60 * ((1 + (K1 + K2)) * (1 + ν)), ?_, ?_⟩
  · have : 0 ≤ (1 + (K1 + K2)) * (1 + ν) := mul_nonneg (by linarith) (by linarith)
    linarith
  intro Mt D t ht hMt hD y
  have hK : 0 ≤ K1 + K2 := by linarith
  have hMt' : ∀ i j, |Mt i j| ≤ K1 + K2 := fun i j => (hMt i j).trans (by linarith)
  have hD' : ∀ i j, |D i j| ≤ K1 + K2 := fun i j => (hD i j).trans (by linarith)
  have ht0 : 0 < ageA ν t := by linarith
  refine ⟨sV_diffAt ν t Mt D ht0 y, ?_⟩
  intro v
  rw [sV_fderiv_eq ν t Mt D ht0 y v, Real.norm_eq_abs]
  have hu0 : 0 < (ageA ν t)⁻¹ := inv_pos.mpr ht0
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hG := svGc_abs ν (ageA ν t)⁻¹ (K1 + K2) ‖y‖ hν.le hu0 hu1 hK (norm_nonneg y) Mt D hMt' hD'
    y (abs_fst_le' y) (abs_snd_le' y)
  have hGD := svGD_abs ν (ageA ν t)⁻¹ (K1 + K2) ‖y‖ ‖v‖ hν.le hu0 hu1 hK (norm_nonneg y)
    (norm_nonneg v) Mt D hMt' hD' y v (abs_fst_le' y) (abs_snd_le' y) (abs_fst_le' v)
    (abs_snd_le' v)
  have hX : |-(svSD y v) / (4 * ageA ν t)| ≤ ‖y‖ * ‖v‖ := by
    have hS := svSD_abs ‖y‖ ‖v‖ (norm_nonneg y) (norm_nonneg v) y v (abs_fst_le' y)
      (abs_snd_le' y) (abs_fst_le' v) (abs_snd_le' v)
    rw [abs_div, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 4 * ageA ν t),
      div_le_iff₀ (by linarith : (0:ℝ) < 4 * ageA ν t)]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg y) (norm_nonneg v))
      (by linarith : (0:ℝ) ≤ ageA ν t - 1)]
  have hE : 0 ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) := (Real.exp_pos _).le
  have hp1 : |Real.exp (-(sq2 y) / (4 * ageA ν t)) * (-(svSD y v) / (4 * ageA ν t))
      * svGc ν (ageA ν t)⁻¹ Mt D y|
      ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) * (‖y‖ * ‖v‖)
          * (24 * ((1 + (K1 + K2)) * (1 + ν)) * (1 + ‖y‖) ^ 4) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hE]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hX hE) hG (abs_nonneg _)
      (mul_nonneg hE (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hp2 : |Real.exp (-(sq2 y) / (4 * ageA ν t)) * svGD ν (ageA ν t)⁻¹ Mt D y v|
      ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) *
          (36 * ((1 + (K1 + K2)) * (1 + ν)) * ‖v‖ * (1 + ‖y‖) ^ 3) := by
    rw [abs_mul, abs_of_nonneg hE]
    exact mul_le_mul_of_nonneg_left hGD hE
  have hS1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hRS : ‖y‖ ≤ 1 + ‖y‖ := by linarith
  have hRS4 : ‖y‖ * (1 + ‖y‖) ^ 4 ≤ (1 + ‖y‖) ^ 5 := by
    have : (1 + ‖y‖) * (1 + ‖y‖) ^ 4 = (1 + ‖y‖) ^ 5 := by ring
    nlinarith [mul_le_mul_of_nonneg_right hRS (by positivity : (0:ℝ) ≤ (1 + ‖y‖) ^ 4)]
  have hS3 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖y‖) ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
  have hw : 0 ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) * ((1 + (K1 + K2)) * (1 + ν)) * ‖v‖ :=
    mul_nonneg (mul_nonneg hE (mul_nonneg (by linarith) (by linarith))) (norm_nonneg v)
  have key1 := mul_le_mul_of_nonneg_left hRS4 hw
  have key2 := mul_le_mul_of_nonneg_left hS3 hw
  have hsum := abs_add_le
    (Real.exp (-(sq2 y) / (4 * ageA ν t)) * (-(svSD y v) / (4 * ageA ν t))
          * svGc ν (ageA ν t)⁻¹ Mt D y)
    (Real.exp (-(sq2 y) / (4 * ageA ν t)) * svGD ν (ageA ν t)⁻¹ Mt D y v)
  linarith [hsum, hp1, hp2, key1, key2]

end UnforcedLeray.Short.PartIIIb.Concrete
