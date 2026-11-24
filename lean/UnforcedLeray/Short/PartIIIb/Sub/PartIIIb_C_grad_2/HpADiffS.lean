import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.SPart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable

/-!
# `PartIII-b:C/grad/2/2`: `s' ↦ h^p_A(s', x)` is differentiable at `s > 0`

Source `the November 2 reference manuscript` lines 4973 (`h^p_A = Σ_j [V_j, A^y x_j]`),
4978 ("the sums and their required derivatives converge by Gaussian decay"), 4741-4745 (`A` is `C^6`).

With `y = x_j`, `a = 1 + νs`, `E = e^{-|y|²/(4a)}`, `w = A^y y`, the `j`-th term of `h^p_A` has the
components `E (a⁻² L_i(A^y) + a⁻³ C_i(A^y))` where `L_i`, `C_i` are linear in the four meridional
entries of `A^y` with coefficients polynomial in `y` (degree 1 and 3).  Each term is differentiable in
`s` with a derivative bounded by `const · (1+|y|)^5 E`, uniformly for `s ∈ (s₀/2, 2s₀)`; the sum is
handled by `hasDerivAt_tsum_of_isPreconnected`, as in `SPart.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Linear functionals of the four meridional entries -/

def lin4 (a b c d : ℝ) (M : Mat3) : ℝ := a * M 0 0 + b * M 0 2 + c * M 2 0 + d * M 2 2

theorem lin4_hasDerivAt (a b c d : ℝ) {M : ℝ → Mat3} {D : Mat3} {t : ℝ} (h : HasDerivAt M D t) :
    HasDerivAt (fun τ => lin4 a b c d (M τ)) (lin4 a b c d D) t := by
  unfold lin4
  exact ((((sp_entry_hasDerivAt h 0 0).const_mul a).add ((sp_entry_hasDerivAt h 0 2).const_mul b)).add
    ((sp_entry_hasDerivAt h 2 0).const_mul c)).add ((sp_entry_hasDerivAt h 2 2).const_mul d)

theorem lin4_bound (a b c d S K : ℝ) (M : Mat3) (hS : |a| + |b| + |c| + |d| ≤ S)
    (hM : ∀ i j, |M i j| ≤ K) : |lin4 a b c d M| ≤ S * K := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hM 0 0)
  unfold lin4
  have t1 := abs_add_le (a * M 0 0 + b * M 0 2 + c * M 2 0) (d * M 2 2)
  have t2 := abs_add_le (a * M 0 0 + b * M 0 2) (c * M 2 0)
  have t3 := abs_add_le (a * M 0 0) (b * M 0 2)
  rw [abs_mul] at t1 t2 t3
  rw [abs_mul] at t3
  have e1 := mul_le_mul_of_nonneg_left (hM 0 0) (abs_nonneg a)
  have e2 := mul_le_mul_of_nonneg_left (hM 0 2) (abs_nonneg b)
  have e3 := mul_le_mul_of_nonneg_left (hM 2 0) (abs_nonneg c)
  have e4 := mul_le_mul_of_nonneg_left (hM 2 2) (abs_nonneg d)
  have e5 := mul_le_mul_of_nonneg_right hS hK
  nlinarith

/-! ## The real product-rule value and its bound -/

def genVal (E w u u' L L' C C' : ℝ) : ℝ :=
  E * w * (u * u * L + u * u * u * C)
    + E * ((u' * u + u * u') * L + u * u * L' + ((u' * u + u * u') * u + u * u * u') * C
      + u * u * u * C')

theorem abs_mul_le2 {p q P Q : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) : |p * q| ≤ P * Q := by
  rw [abs_mul]
  exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)

theorem abs_pmul_le {p X B : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hX : |X| ≤ B) : |p * X| ≤ B := by
  rw [abs_mul, abs_of_nonneg hp0]
  have hB : 0 ≤ B := (abs_nonneg _).trans hX
  nlinarith [abs_nonneg X]

theorem genVal_bound (E w u u' L L' C C' A0 A1 B0 B1 ν W : ℝ) (hE : 0 ≤ E) (hw : |w| ≤ W)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hu' : |u'| ≤ ν) (hL : |L| ≤ A0) (hL' : |L'| ≤ A1)
    (hC : |C| ≤ B0) (hC' : |C'| ≤ B1) :
    |genVal E w u u' L L' C C'| ≤ E * (W * (A0 + B0) + 2 * ν * A0 + A1 + 3 * ν * B0 + B1) := by
  have hν : 0 ≤ ν := (abs_nonneg _).trans hu'
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans hL
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans hC
  have huu0 : 0 ≤ u * u := by positivity
  have huu1 : u * u ≤ 1 := by nlinarith
  have huuu0 : 0 ≤ u * u * u := by positivity
  have huuu1 : u * u * u ≤ 1 := by nlinarith
  have hq : |u' * u + u * u'| ≤ 2 * ν := by
    have a1 : |u' * u| ≤ ν := by
      rw [abs_mul, abs_of_pos hu0]; nlinarith [abs_nonneg u']
    have a2 : |u * u'| ≤ ν := by
      rw [abs_mul, abs_of_pos hu0]; nlinarith [abs_nonneg u']
    linarith [abs_add_le (u' * u) (u * u')]
  have hr : |(u' * u + u * u') * u + u * u * u'| ≤ 3 * ν := by
    have a1 : |(u' * u + u * u') * u| ≤ 2 * ν := by
      rw [abs_mul, abs_of_pos hu0]; nlinarith [abs_nonneg (u' * u + u * u')]
    have a2 : |u * u * u'| ≤ ν := by
      rw [abs_mul, abs_of_nonneg huu0]; nlinarith [abs_nonneg u']
    linarith [abs_add_le ((u' * u + u * u') * u) (u * u * u')]
  have b1 : |u * u * L + u * u * u * C| ≤ A0 + B0 :=
    (abs_add_le _ _).trans (add_le_add (abs_pmul_le huu0 huu1 hL) (abs_pmul_le huuu0 huuu1 hC))
  have b2 : |E * w * (u * u * L + u * u * u * C)| ≤ E * (W * (A0 + B0)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hE]
    have := mul_le_mul hw b1 (abs_nonneg _) ((abs_nonneg _).trans hw)
    nlinarith [this]
  have c1 : |(u' * u + u * u') * L| ≤ 2 * ν * A0 := abs_mul_le2 hq hL
  have c3 : |((u' * u + u * u') * u + u * u * u') * C| ≤ 3 * ν * B0 := abs_mul_le2 hr hC
  have c2 : |u * u * L'| ≤ A1 := abs_pmul_le huu0 huu1 hL'
  have c4 : |u * u * u * C'| ≤ B1 := abs_pmul_le huuu0 huuu1 hC'
  have b3 : |(u' * u + u * u') * L + u * u * L' + ((u' * u + u * u') * u + u * u * u') * C
      + u * u * u * C'| ≤ 2 * ν * A0 + A1 + 3 * ν * B0 + B1 := by
    have s1 := abs_add_le ((u' * u + u * u') * L + u * u * L' + ((u' * u + u * u') * u + u * u * u') * C) (u * u * u * C')
    have s2 := abs_add_le ((u' * u + u * u') * L + u * u * L') (((u' * u + u * u') * u + u * u * u') * C)
    have s3 := abs_add_le ((u' * u + u * u') * L) (u * u * L')
    linarith
  have b4 : |E * ((u' * u + u * u') * L + u * u * L' + ((u' * u + u * u') * u + u * u * u') * C
      + u * u * u * C')| ≤ E * (2 * ν * A0 + A1 + 3 * ν * B0 + B1) := by
    rw [abs_mul, abs_of_nonneg hE]
    exact mul_le_mul_of_nonneg_left b3 hE
  unfold genVal
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ E * (W * (A0 + B0)) + E * (2 * ν * A0 + A1 + 3 * ν * B0 + B1) := add_le_add b2 b4
    _ = _ := by ring

/-! ## A generic term `E (a⁻² ℓ(M) + a⁻³ k(M))` -/

def gcomp (ν t : ℝ) (ℓ k : Mat3 → ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  Real.exp (-(sq2 y) / (4 * ageA ν t)) *
    ((ageA ν t)⁻¹ * (ageA ν t)⁻¹ * ℓ M + (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * k M)

def gcompD (ν t : ℝ) (ℓ k : Mat3 → ℝ) (M D : Mat3) (y : ℝ × ℝ) : ℝ :=
  genVal (Real.exp (-(sq2 y) / (4 * ageA ν t)))
    ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2)
    (ageA ν t)⁻¹ (-ν / (ageA ν t) ^ 2) (ℓ M) (ℓ D) (k M) (k D)

theorem gcomp_hasDerivAt (ν : ℝ) (y : ℝ × ℝ) (ℓ k : Mat3 → ℝ) (M : ℝ → Mat3) (D : Mat3) (t : ℝ)
    (hν : 0 < ν) (ht : 0 < t) (hl : HasDerivAt (fun τ => ℓ (M τ)) (ℓ D) t)
    (hk : HasDerivAt (fun τ => k (M τ)) (k D) t) :
    HasDerivAt (fun τ => gcomp ν τ ℓ k (M τ) y) (gcompD ν t ℓ k (M t) D y) t := by
  have ha0 : 0 < ageA ν t := by unfold ageA; nlinarith
  have hA : HasDerivAt (fun τ => ageA ν τ) ν t := by
    unfold ageA
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have hu := hA.inv ha0.ne'
  have hne : 4 * ageA ν t ≠ 0 := by linarith
  have hg : HasDerivAt (fun τ => -(sq2 y) / (4 * ageA ν τ))
      ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2) t :=
    (hasDerivAt_const t (-(sq2 y))).div (hA.const_mul 4) hne
  have hE := hg.exp
  have hF := hE.mul (((hu.mul hu).mul hl).add (((hu.mul hu).mul hu).mul hk))
  unfold gcomp gcompD genVal
  refine hF.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.inv_apply]
  ring

theorem sq2_le_two_sq (y : ℝ × ℝ) : sq2 y ≤ 2 * ‖y‖ ^ 2 := by
  have e1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y.1) (abs_fst_le' y) 2
    rwa [sq_abs] at this
  have e2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y.2) (abs_snd_le' y) 2
    rwa [sq_abs] at this
  unfold sq2
  linarith

theorem gcomp_bound (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (y : ℝ × ℝ) (ℓ k : Mat3 → ℝ)
    (M D : Mat3) (A0 A1 B0 B1 : ℝ) (hL : |ℓ M| ≤ A0) (hL' : |ℓ D| ≤ A1) (hC : |k M| ≤ B0)
    (hC' : |k D| ≤ B1) :
    |gcompD ν t ℓ k M D y| ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) *
      ((ν * ‖y‖ ^ 2 / 2) * (A0 + B0) + 2 * ν * A0 + A1 + 3 * ν * B0 + B1) := by
  have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith
  have ha0 : 0 < ageA ν t := by linarith
  have hc0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hw := sp_gD_bound (ageA ν t) (sq2 y) ν ‖y‖ ha1 hν.le hc0 (sq2_le_two_sq y)
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have hu' : |-ν / (ageA ν t) ^ 2| ≤ ν := by
    have ha2 : (1:ℝ) ≤ (ageA ν t) ^ 2 := one_le_pow₀ ha1
    rw [abs_div, abs_neg, abs_of_nonneg hν.le, abs_of_pos (by linarith : (0:ℝ) < (ageA ν t) ^ 2)]
    exact div_le_self hν.le ha2
  unfold gcompD
  exact genVal_bound _ _ _ _ _ _ _ _ A0 A1 B0 B1 ν (ν * ‖y‖ ^ 2 / 2) (Real.exp_pos _).le hw
    (inv_pos.mpr ha0) hu1 hu' hL hL' hC hC'

/-! ## The terms of `h^p_A` -/

/-- Coefficients of the linear part of the `r`-component. -/
def hpPhi (ν t : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ × ℝ :=
  (gcomp ν t (lin4 (-y.2) y.1 y.1 y.2)
      (lin4 (-(y.2 * (y.1 * y.1)) / 2) (-(y.2 * (y.1 * y.2)) / 2) (-(y.2 * (y.2 * y.1)) / 2)
        (-(y.2 * (y.2 * y.2)) / 2)) M y,
   gcomp ν t (lin4 (-y.1) (-y.2) (-y.2) y.1)
      (lin4 (y.1 * (y.1 * y.1) / 2) (y.1 * (y.1 * y.2) / 2) (y.1 * (y.2 * y.1) / 2)
        (y.1 * (y.2 * y.2) / 2)) M y)

def hpPhiD (ν t : ℝ) (M D : Mat3) (y : ℝ × ℝ) : ℝ × ℝ :=
  (gcompD ν t (lin4 (-y.2) y.1 y.1 y.2)
      (lin4 (-(y.2 * (y.1 * y.1)) / 2) (-(y.2 * (y.1 * y.2)) / 2) (-(y.2 * (y.2 * y.1)) / 2)
        (-(y.2 * (y.2 * y.2)) / 2)) M D y,
   gcompD ν t (lin4 (-y.1) (-y.2) (-y.2) y.1)
      (lin4 (y.1 * (y.1 * y.1) / 2) (y.1 * (y.1 * y.2) / 2) (y.1 * (y.2 * y.1) / 2)
        (y.1 * (y.2 * y.2) / 2)) M D y)

theorem hpATerm_eq_hpPhi (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ)
    (ha : 0 < ageA ν s) :
    hpATerm ν χ A s x j = hpPhi ν s (Ay ν χ A s) (xj ν j x) := by
  unfold hpATerm hpPhi
  rw [gp_fderiv_Vj]
  have hne : ageA ν s ≠ 0 := ha.ne'
  ext
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Vj, Jrot, merApply,
      gcomp, lin4]
    field_simp
    ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, Vj, Jrot,
      merApply, gcomp, lin4]
    field_simp
    ring

theorem hpPhi_hasDerivAt (ν : ℝ) (y : ℝ × ℝ) (M : ℝ → Mat3) (D : Mat3) (t : ℝ) (hν : 0 < ν)
    (ht : 0 < t) (hM : HasDerivAt M D t) :
    HasDerivAt (fun τ => hpPhi ν τ (M τ) y) (hpPhiD ν t (M t) D y) t := by
  unfold hpPhi hpPhiD
  exact (gcomp_hasDerivAt ν y _ _ M D t hν ht (lin4_hasDerivAt _ _ _ _ hM)
    (lin4_hasDerivAt _ _ _ _ hM)).prodMk
    (gcomp_hasDerivAt ν y _ _ M D t hν ht (lin4_hasDerivAt _ _ _ _ hM)
    (lin4_hasDerivAt _ _ _ _ hM))

theorem cube_abs_le (a b c R : ℝ) (ha : |a| ≤ R) (hb : |b| ≤ R) (hc : |c| ≤ R) :
    |a * (b * c) / 2| ≤ R ^ 3 / 2 := by
  have h1 := abs_mul_le2 hb hc
  have h2 := abs_mul_le2 ha h1
  rw [abs_div, abs_two, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
  have : R * (R * R) = R ^ 3 := by ring
  rw [this] at h2
  exact h2

theorem hp_poly (ν K1 K2 R : ℝ) (hν : 0 ≤ ν) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hR : 0 ≤ R) :
    (ν * R ^ 2 / 2) * (4 * R * K1 + 2 * R ^ 3 * K1) + 2 * ν * (4 * R * K1) + 4 * R * K2
      + 3 * ν * (2 * R ^ 3 * K1) + 2 * R ^ 3 * K2 ≤ (17 * ν * K1 + 6 * K2) * (1 + R) ^ 5 := by
  have p1 : R ≤ (1 + R) ^ 5 := by
    nlinarith [pow_nonneg hR 2, pow_nonneg hR 3, pow_nonneg hR 4, pow_nonneg hR 5]
  have p3 : R ^ 3 ≤ (1 + R) ^ 5 := by
    nlinarith [pow_nonneg hR 2, pow_nonneg hR 3, pow_nonneg hR 4, pow_nonneg hR 5]
  have p5 : R ^ 5 ≤ (1 + R) ^ 5 := by
    nlinarith [pow_nonneg hR 2, pow_nonneg hR 3, pow_nonneg hR 4, pow_nonneg hR 5]
  have e : (ν * R ^ 2 / 2) * (4 * R * K1 + 2 * R ^ 3 * K1) + 2 * ν * (4 * R * K1) + 4 * R * K2
      + 3 * ν * (2 * R ^ 3 * K1) + 2 * R ^ 3 * K2
      = ν * K1 * (R ^ 5 + 8 * R ^ 3 + 8 * R) + K2 * (4 * R + 2 * R ^ 3) := by ring
  rw [e]
  have hνK : 0 ≤ ν * K1 := mul_nonneg hν hK1
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : R ^ 5 + 8 * R ^ 3 + 8 * R ≤ 17 * (1 + R) ^ 5) hνK,
    mul_le_mul_of_nonneg_left (by linarith : 4 * R + 2 * R ^ 3 ≤ 6 * (1 + R) ^ 5) hK2]

theorem hpPhiD_bound (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (y : ℝ × ℝ) (K1 K2 : ℝ) (M D : Mat3)
    (hMb : ∀ i j, |M i j| ≤ K1) (hDb : ∀ i j, |D i j| ≤ K2) :
    ‖hpPhiD ν t M D y‖ ≤ (17 * ν * K1 + 6 * K2) * (1 + ‖y‖) ^ 5 *
      Real.exp (-(sq2 y) / (4 * ageA ν t)) := by
  have hK1 : 0 ≤ K1 := (abs_nonneg _).trans (hMb 0 0)
  have hK2 : 0 ≤ K2 := (abs_nonneg _).trans (hDb 0 0)
  have hR : 0 ≤ ‖y‖ := norm_nonneg y
  have h1 := abs_fst_le' y
  have h2 := abs_snd_le' y
  have n1 : |-y.2| ≤ ‖y‖ := by rwa [abs_neg]
  have n2 : |-y.1| ≤ ‖y‖ := by rwa [abs_neg]
  -- sums of coefficients
  have SL1 : |-y.2| + |y.1| + |y.1| + |y.2| ≤ 4 * ‖y‖ := by linarith
  have SL2 : |-y.1| + |-y.2| + |-y.2| + |y.1| ≤ 4 * ‖y‖ := by linarith
  have c1 := cube_abs_le y.2 y.1 y.1 ‖y‖ h2 h1 h1
  have c2 := cube_abs_le y.2 y.1 y.2 ‖y‖ h2 h1 h2
  have c3 := cube_abs_le y.2 y.2 y.1 ‖y‖ h2 h2 h1
  have c4 := cube_abs_le y.2 y.2 y.2 ‖y‖ h2 h2 h2
  have d1 := cube_abs_le y.1 y.1 y.1 ‖y‖ h1 h1 h1
  have d2 := cube_abs_le y.1 y.1 y.2 ‖y‖ h1 h1 h2
  have d3 := cube_abs_le y.1 y.2 y.1 ‖y‖ h1 h2 h1
  have d4 := cube_abs_le y.1 y.2 y.2 ‖y‖ h1 h2 h2
  have SK1 : |-(y.2 * (y.1 * y.1)) / 2| + |-(y.2 * (y.1 * y.2)) / 2| + |-(y.2 * (y.2 * y.1)) / 2|
      + |-(y.2 * (y.2 * y.2)) / 2| ≤ 2 * ‖y‖ ^ 3 := by
    have e : ∀ z : ℝ, |-z / 2| = |z / 2| := fun z => by rw [neg_div, abs_neg]
    rw [e, e, e, e]
    linarith
  have SK2 : |y.1 * (y.1 * y.1) / 2| + |y.1 * (y.1 * y.2) / 2| + |y.1 * (y.2 * y.1) / 2|
      + |y.1 * (y.2 * y.2) / 2| ≤ 2 * ‖y‖ ^ 3 := by linarith
  have hE0 := (Real.exp_pos (-(sq2 y) / (4 * ageA ν t))).le
  have key : ∀ (l1 l2 l3 l4 k1 k2 k3 k4 : ℝ), |l1| + |l2| + |l3| + |l4| ≤ 4 * ‖y‖ →
      |k1| + |k2| + |k3| + |k4| ≤ 2 * ‖y‖ ^ 3 →
      |gcompD ν t (lin4 l1 l2 l3 l4) (lin4 k1 k2 k3 k4) M D y| ≤
        (17 * ν * K1 + 6 * K2) * (1 + ‖y‖) ^ 5 * Real.exp (-(sq2 y) / (4 * ageA ν t)) := by
    intro l1 l2 l3 l4 k1 k2 k3 k4 hl hk
    have g := gcomp_bound ν t hν ht y (lin4 l1 l2 l3 l4) (lin4 k1 k2 k3 k4) M D
      (4 * ‖y‖ * K1) (4 * ‖y‖ * K2) (2 * ‖y‖ ^ 3 * K1) (2 * ‖y‖ ^ 3 * K2)
      (lin4_bound _ _ _ _ _ _ M hl hMb) (lin4_bound _ _ _ _ _ _ D hl hDb)
      (lin4_bound _ _ _ _ _ _ M hk hMb) (lin4_bound _ _ _ _ _ _ D hk hDb)
    refine g.trans ?_
    have hp := hp_poly ν K1 K2 ‖y‖ hν.le hK1 hK2 hR
    have : (ν * ‖y‖ ^ 2 / 2) * (4 * ‖y‖ * K1 + 2 * ‖y‖ ^ 3 * K1) + 2 * ν * (4 * ‖y‖ * K1)
        + 4 * ‖y‖ * K2 + 3 * ν * (2 * ‖y‖ ^ 3 * K1) + 2 * ‖y‖ ^ 3 * K2
        ≤ (17 * ν * K1 + 6 * K2) * (1 + ‖y‖) ^ 5 := hp
    nlinarith [mul_le_mul_of_nonneg_left this hE0]
  unfold hpPhiD
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (key _ _ _ _ _ _ _ _ SL1 SK1) (key _ _ _ _ _ _ _ _ SL2 SK2)

/-! ## Power-5 Gaussian majorants -/

theorem sp_poly5_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h4 := gp_gauss_pow_summable t α c hα hc 5
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ 5 := pow_nonneg (by linarith [abs_nonneg t]) 5
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add h4).mul_left (16 * (1 + |t| + c) ^ 5))
  have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |t| + c) * (1 + |(j : ℝ)|) := by
    have h1 : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
      have h2 := abs_sub t ((j : ℝ) * c)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg t, mul_nonneg hz hc.le, mul_nonneg (abs_nonneg t) hz]
  have h1 : (1 + |t - (j : ℝ) * c|) ^ 5 ≤ (1 + |t| + c) ^ 5 * (1 + |(j : ℝ)|) ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu 5
  have h2 : (1 + |(j : ℝ)|) ^ 5 ≤ 16 * (1 + |(j : ℝ)| ^ 5) := by
    have hq : 0 ≤ 15 * |(j : ℝ)| ^ 3 + 25 * |(j : ℝ)| ^ 2 + 25 * |(j : ℝ)| + 15 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (|(j : ℝ)| - 1)) hq]
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  calc (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ 5 * (16 * (1 + |(j : ℝ)| ^ 5))) *
          Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hK)) hE
    _ = 16 * (1 + |t| + c) ^ 5 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

theorem sp5_major (ν t Pm C1 c : ℝ) (x : ℝ × ℝ) (n : ℤ) (ha1 : 1 ≤ ageA ν t)
    (hPm : ageA ν t ≤ Pm) (hc0 : 0 ≤ c) (hcC : c ≤ C1) (hC1 : 0 ≤ C1) :
    c * (1 + ‖xj ν n x‖) ^ 5 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) ≤
      C1 * (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
  have hy := gp_one_add_norm ν n x
  have hR0 : 0 ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
  have hpow : (1 + ‖xj ν n x‖) ^ 5 ≤ (1 + |x.2|) ^ 5 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hR0 hy 5
  have hexp := sp_exp_le ν t Pm (xj ν n x) ha1 hPm
  have hxj : (xj ν n x).1 = x.1 - (n : ℝ) * cOf ν := rfl
  rw [hxj] at hexp
  have hE0 := (Real.exp_pos (-(sq2 (xj ν n x)) / (4 * ageA ν t))).le
  have s1 : c * (1 + ‖xj ν n x‖) ^ 5 ≤ C1 * ((1 + |x.2|) ^ 5 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5) :=
    mul_le_mul hcC hpow (pow_nonneg hR0 5) hC1
  calc c * (1 + ‖xj ν n x‖) ^ 5 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t))
      ≤ (C1 * ((1 + |x.2|) ^ 5 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5)) *
          Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul s1 hexp hE0 (mul_nonneg hC1 (by positivity))
    _ = C1 * (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by ring

/-! ## The target -/

theorem hpADiffS (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : HpADiffS as χf := by
  unfold HpADiffS
  intro ν hν A hA s hs x
  have hMd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (Ay ν χf A) t :=
    fun t ht => ayDiffAt as χf hχ ν A hA t ht
  have hC1 : ContDiffOn ℝ 1 (Ay ν χf A) (Ioi 0) := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
      ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffOn).of_le (by norm_num)
    have ha : ContDiffOn ℝ 1 A (Ioi 0) := hA.smooth.of_le (by norm_num)
    unfold Ay
    exact hc.smul ha
  have hDC : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hJpos : ∀ t ∈ Icc (s / 2) (2 * s), 0 < t := fun t ht => by linarith [ht.1]
  have hsJ : s ∈ Icc (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := Ay ν χf A) (fun t ht => (hMd t (hJpos t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (Ay ν χf A)) (hDC.mono (fun t ht => hJpos t ht))
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 s hsJ)
  have hK2nn : 0 ≤ K2 := (norm_nonneg _).trans (hK2 s hsJ)
  have hMb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |Ay ν χf A t i j| ≤ K1 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK1 t ht)
  have hDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (Ay ν χf A) t i j| ≤ K2 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK2 t ht)
  have hPm : ∀ t ∈ Icc (s / 2) (2 * s), ageA ν t ≤ 1 + ν * (2 * s) := by
    intro t ht
    unfold ageA
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hν.le]
  have ha1s : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hCnn : 0 ≤ 17 * ν * K1 + 6 * K2 := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 17) hν.le) hK1nn
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hK2nn
    linarith
  set Cm : ℝ := 17 * ν * K1 + 6 * K2 with hCm
  have hu : Summable (fun n : ℤ => Cm * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly5_summable x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      (Cm * (1 + |x.2|) ^ 5)
  have hbound : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x)‖ ≤
        Cm * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ hτ
    have hτJ : τ ∈ Icc (s / 2) (2 * s) := ⟨hτ.1.le, hτ.2.le⟩
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 := hpPhiD_bound ν τ hν hτ0 (xj ν n x) K1 K2 (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
      (hMb τ hτJ) (hDb τ hτJ)
    refine h1.trans ?_
    have ha1τ : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν hτ0]
    exact sp5_major ν τ (1 + ν * (2 * s)) Cm Cm x n ha1τ (hPm τ hτJ) hCnn le_rfl hCnn
  have hdiff : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => hpPhi ν τ' (Ay ν χf A τ') (xj ν n x))
        (hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x)) τ := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact hpPhi_hasDerivAt ν (xj ν n x) (Ay ν χf A) (deriv (Ay ν χf A) τ) τ hν hτ0
      (hMd τ hτ0).hasDerivAt
  have hg0 : Summable (fun n : ℤ => hpPhi ν s (Ay ν χf A s) (xj ν n x)) := by
    have h := (hpPsiTermSummable ν χf A s x hν hs).1
    refine h.congr (fun n => ?_)
    exact hpATerm_eq_hpPhi ν χf A s x n (by linarith)
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun n τ => hpPhi ν τ (Ay ν χf A τ) (xj ν n x))
    (g' := fun n τ => hpPhiD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x))
    (u := fun n : ℤ => Cm * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => hdiff n τ hτ) (fun n τ hτ => hbound n τ hτ)
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hd : DifferentiableAt ℝ (fun τ => ∑' n : ℤ, hpPhi ν τ (Ay ν χf A τ) (xj ν n x)) s :=
    key.differentiableAt
  have hev : Filter.EventuallyEq (nhds s) (fun τ => hpA ν χf A τ x)
      (fun τ => ∑' n : ℤ, hpPhi ν τ (Ay ν χf A τ) (xj ν n x)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    rw [hpA_eq]
    exact tsum_congr fun j => hpATerm_eq_hpPhi ν χf A τ x j
      (by unfold ageA; nlinarith [mul_pos hν hτ0])
  exact hd.congr_of_eventuallyEq hev

end UnforcedLeray.Short.PartIIIb.Concrete
