import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2

/-!
# `PartIII-b:C/grad/2/5`: the mixed derivative `∂_s ∂_η ψ^p_A` exists at `s > 0`

Source `the November 2 reference manuscript` lines 4973-4980 (`ψ^p_A = Σ_j Φ(x_j)`,
the sums and their `s`-derivatives converge by Gaussian decay), 4741-4745 (`A` is `C^6`).
`ei 1 = (0,1)` is the `η`-direction.

Closed form: `∂_η Φ` along `(0,1)` is `E · (u² R + u³ S)` with `u = a⁻¹`, `a = 1 + ν s`,
`E = exp(-|y|²/(4a))`, `R = y₂(M₀₀-M₂₂) - y₁(M₀₂+M₂₀)`, `S = y₂(M₀₀y₁²+(M₀₂+M₂₀)y₁y₂+M₂₂y₂²)/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Linear piece `R` of the closed form of `∂_η Φ`. -/
def pamRe (M : Mat3) (y : ℝ × ℝ) : ℝ := y.2 * (M 0 0 - M 2 2) - y.1 * (M 0 2 + M 2 0)

/-- Cubic piece `S` of the closed form of `∂_η Φ`. -/
def pamSe (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  y.2 * (M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2 + M 2 2 * y.2 ^ 2) / 2

/-- Product-rule value of `d/dt [E · (u² R + u³ S)]`. -/
def pamDerivVal (E w u u' R R' S S' : ℝ) : ℝ :=
  E * w * (u * u * R + u * u * u * S)
    + E * ((u' * u + u * u') * R + u * u * R' + ((u' * u + u * u') * u + u * u * u') * S
      + u * u * u * S')

/-- The `t`-derivative of the `η`-lattice term `t ↦ ∂_η Φ(t, M(t), y)`. -/
def pamGD (ν t : ℝ) (M D : Mat3) (y : ℝ × ℝ) : ℝ :=
  pamDerivVal (Real.exp (-(sq2 y) / (4 * ageA ν t)))
    ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2)
    (ageA ν t)⁻¹ (-ν / (ageA ν t) ^ 2) (pamRe M y) (pamRe D y) (pamSe M y) (pamSe D y)

theorem pam_psiPhiD_e2 (ν t : ℝ) (M : Mat3) (y : ℝ × ℝ) :
    psiPhiD ν t M y (0, 1) = Real.exp (-(sq2 y) / (4 * ageA ν t)) *
      ((ageA ν t)⁻¹ * (ageA ν t)⁻¹ * pamRe M y
        + (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * pamSe M y) := by
  by_cases ha : ageA ν t = 0
  · simp [psiPhiD, ha]
  · unfold psiPhiD pamRe pamSe merApply merTrace
    dsimp only
    field_simp
    ring

theorem pam_pamRe_hasDerivAt (y : ℝ × ℝ) {M : ℝ → Mat3} {D : Mat3} {t : ℝ}
    (h : HasDerivAt M D t) : HasDerivAt (fun τ => pamRe (M τ) y) (pamRe D y) t := by
  have h22 := sp_entry_hasDerivAt h 2 2
  have h00 := sp_entry_hasDerivAt h 0 0
  have h02 := sp_entry_hasDerivAt h 0 2
  have h20 := sp_entry_hasDerivAt h 2 0
  have H := ((h00.sub h22).const_mul y.2).sub ((h02.add h20).const_mul y.1)
  unfold pamRe
  exact H.congr_deriv (by ring)

theorem pam_pamSe_hasDerivAt (y : ℝ × ℝ) {M : ℝ → Mat3} {D : Mat3} {t : ℝ}
    (h : HasDerivAt M D t) : HasDerivAt (fun τ => pamSe (M τ) y) (pamSe D y) t := by
  have h22 := sp_entry_hasDerivAt h 2 2
  have h00 := sp_entry_hasDerivAt h 0 0
  have h02 := sp_entry_hasDerivAt h 0 2
  have h20 := sp_entry_hasDerivAt h 2 0
  have hq := ((h00.mul_const (y.1 ^ 2)).add (((h02.add h20).mul_const y.1).mul_const y.2)).add
    (h22.mul_const (y.2 ^ 2))
  have H := (hq.const_mul y.2).div_const 2
  unfold pamSe
  exact H.congr_deriv (by ring)

theorem pam_G_hasDerivAt (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (y : ℝ × ℝ) {M : ℝ → Mat3}
    {D : Mat3} (hM : HasDerivAt M D t) :
    HasDerivAt (fun τ => psiPhiD ν τ (M τ) y (0, 1)) (pamGD ν t (M t) D y) t := by
  have hfun : (fun τ => psiPhiD ν τ (M τ) y (0, 1)) = fun τ =>
      Real.exp (-(sq2 y) / (4 * ageA ν τ)) *
        ((ageA ν τ)⁻¹ * (ageA ν τ)⁻¹ * pamRe (M τ) y
          + (ageA ν τ)⁻¹ * (ageA ν τ)⁻¹ * (ageA ν τ)⁻¹ * pamSe (M τ) y) :=
    funext fun τ => pam_psiPhiD_e2 ν τ (M τ) y
  rw [hfun]
  have ha : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
  have hA : HasDerivAt (fun τ => ageA ν τ) ν t := by
    unfold ageA
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have hu : HasDerivAt (fun τ => (ageA ν τ)⁻¹) (-ν / (ageA ν t) ^ 2) t := hA.inv ha.ne'
  have hne : 4 * ageA ν t ≠ 0 := (by linarith : (0:ℝ) < 4 * ageA ν t).ne'
  have hg : HasDerivAt (fun τ => -(sq2 y) / (4 * ageA ν τ))
      ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2) t :=
    (hasDerivAt_const t (-(sq2 y))).div (hA.const_mul 4) hne
  have hw := hg.exp
  have hR := pam_pamRe_hasDerivAt y hM
  have hS := pam_pamSe_hasDerivAt y hM
  have H := hw.mul (((hu.mul hu).mul hR).add (((hu.mul hu).mul hu).mul hS))
  unfold pamGD
  refine H.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  unfold pamDerivVal
  ring

theorem pam_w_bound (ν a : ℝ) (y : ℝ × ℝ) (hν : 0 ≤ ν) (ha : 1 ≤ a) :
    0 ≤ (0 * (4 * a) - (-(sq2 y)) * (4 * ν)) / (4 * a) ^ 2 ∧
      (0 * (4 * a) - (-(sq2 y)) * (4 * ν)) / (4 * a) ^ 2 ≤ ν * ‖y‖ ^ 2 / 2 := by
  have hc0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hcR : sq2 y ≤ 2 * ‖y‖ ^ 2 := by
    have e1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg y.1) (abs_fst_le' y) 2
      rwa [sq_abs] at this
    have e2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg y.2) (abs_snd_le' y) 2
      rwa [sq_abs] at this
    unfold sq2
    linarith
  have hpos : 0 < (4 * a) ^ 2 := by
    have : 0 < 4 * a := by linarith
    positivity
  have e : 0 * (4 * a) - (-(sq2 y)) * (4 * ν) = 4 * ν * sq2 y := by ring
  rw [e]
  refine ⟨div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hν) hc0) hpos.le, ?_⟩
  rw [div_le_iff₀ hpos]
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  nlinarith [mul_le_mul_of_nonneg_left hcR (by linarith : (0:ℝ) ≤ 4 * ν),
    mul_nonneg (mul_nonneg hν (sq_nonneg ‖y‖)) (sub_nonneg.2 ha2)]

theorem pam_pamRe_le (M : Mat3) (y : ℝ × ℝ) (K : ℝ) (hM : ∀ i j, |M i j| ≤ K) :
    |pamRe M y| ≤ 4 * K * ‖y‖ := by
  unfold pamRe
  have h1 : |y.2| ≤ ‖y‖ := abs_snd_le' y
  have h2 : |y.1| ≤ ‖y‖ := abs_fst_le' y
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hM 0 0)
  have hr : 0 ≤ ‖y‖ := norm_nonneg y
  have a1 : |M 0 0 - M 2 2| ≤ 2 * K := (abs_sub _ _).trans (by linarith [hM 0 0, hM 2 2])
  have a2 : |M 0 2 + M 2 0| ≤ 2 * K := (abs_add_le _ _).trans (by linarith [hM 0 2, hM 2 0])
  calc |y.2 * (M 0 0 - M 2 2) - y.1 * (M 0 2 + M 2 0)|
      ≤ |y.2 * (M 0 0 - M 2 2)| + |y.1 * (M 0 2 + M 2 0)| := abs_sub _ _
    _ = |y.2| * |M 0 0 - M 2 2| + |y.1| * |M 0 2 + M 2 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖y‖ * (2 * K) + ‖y‖ * (2 * K) :=
        add_le_add (mul_le_mul h1 a1 (abs_nonneg _) hr) (mul_le_mul h2 a2 (abs_nonneg _) hr)
    _ = 4 * K * ‖y‖ := by ring

theorem pam_pamSe_le (M : Mat3) (y : ℝ × ℝ) (K : ℝ) (hM : ∀ i j, |M i j| ≤ K) :
    |pamSe M y| ≤ 2 * K * ‖y‖ ^ 3 := by
  unfold pamSe
  have h1 : |y.2| ≤ ‖y‖ := abs_snd_le' y
  have h2 : |y.1| ≤ ‖y‖ := abs_fst_le' y
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hM 0 0)
  have hr : 0 ≤ ‖y‖ := norm_nonneg y
  have a2 : |M 0 2 + M 2 0| ≤ 2 * K := (abs_add_le _ _).trans (by linarith [hM 0 2, hM 2 0])
  have t1 : |M 0 0 * y.1 ^ 2| ≤ K * ‖y‖ ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hM 0 0) (pow_le_pow_left₀ (abs_nonneg _) h2 2) (by positivity) hK
  have t2 : |(M 0 2 + M 2 0) * y.1 * y.2| ≤ 2 * K * ‖y‖ * ‖y‖ := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul a2 h2 (abs_nonneg _) (by linarith))
      h1 (abs_nonneg _) (mul_nonneg (by linarith) hr)
  have t3 : |M 2 2 * y.2 ^ 2| ≤ K * ‖y‖ ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hM 2 2) (pow_le_pow_left₀ (abs_nonneg _) h1 2) (by positivity) hK
  have hZ : |M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2 + M 2 2 * y.2 ^ 2|
      ≤ 4 * K * ‖y‖ ^ 2 := by
    have s1 := abs_add_le (M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2) (M 2 2 * y.2 ^ 2)
    have s2 := abs_add_le (M 0 0 * y.1 ^ 2) ((M 0 2 + M 2 0) * y.1 * y.2)
    nlinarith
  have hmul : |y.2 * (M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2 + M 2 2 * y.2 ^ 2)|
      ≤ ‖y‖ * (4 * K * ‖y‖ ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul h1 hZ (abs_nonneg _) hr
  rw [abs_div, abs_two]
  have : |y.2 * (M 0 0 * y.1 ^ 2 + (M 0 2 + M 2 0) * y.1 * y.2 + M 2 2 * y.2 ^ 2)| / 2
      ≤ ‖y‖ * (4 * K * ‖y‖ ^ 2) / 2 := by gcongr
  nlinarith

theorem pam_deriv_real (E w u u' R R' S S' r K1 K2 ν : ℝ) (hE : 0 ≤ E) (hw0 : 0 ≤ w)
    (hw : w ≤ ν * r ^ 2 / 2) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu' : |u'| ≤ ν)
    (hR : |R| ≤ 4 * K1 * r) (hR' : |R'| ≤ 4 * K2 * r) (hS : |S| ≤ 2 * K1 * r ^ 3)
    (hS' : |S'| ≤ 2 * K2 * r ^ 3) (hr : 0 ≤ r) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hν : 0 ≤ ν) :
    |pamDerivVal E w u u' R R' S S'| ≤ E * (20 * (1 + ν) * (K1 + K2) * (1 + r) ^ 5) := by
  have hu'a := abs_le.mp hu'
  have hu2' : 0 ≤ u * u := mul_nonneg hu0 hu0
  have hu2 : u * u ≤ 1 := by nlinarith
  have hu3' : 0 ≤ u * u * u := mul_nonneg hu2' hu0
  have hu3 : u * u * u ≤ 1 := by nlinarith
  have k1 : |u * u| ≤ 1 := by rw [abs_of_nonneg hu2']; exact hu2
  have k2 : |u * u * u| ≤ 1 := by rw [abs_of_nonneg hu3']; exact hu3
  have k3 : |u' * u + u * u'| ≤ 2 * ν := abs_le.mpr
    ⟨by nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ u' + ν), mul_nonneg hν (sub_nonneg.2 hu1)],
     by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu'a.2), mul_nonneg hν (sub_nonneg.2 hu1)]⟩
  have k4 : |(u' * u + u * u') * u + u * u * u'| ≤ 3 * ν := abs_le.mpr
    ⟨by nlinarith [mul_nonneg hu2' (by linarith : (0:ℝ) ≤ u' + ν), mul_nonneg hν (sub_nonneg.2 hu2)],
     by nlinarith [mul_nonneg hu2' (sub_nonneg.2 hu'a.2), mul_nonneg hν (sub_nonneg.2 hu2)]⟩
  have hX : |u * u * R + u * u * u * S| ≤ |R| + |S| := by
    calc |u * u * R + u * u * u * S| ≤ |u * u * R| + |u * u * u * S| := abs_add_le _ _
      _ = |u * u| * |R| + |u * u * u| * |S| := by simp only [abs_mul]
      _ ≤ 1 * |R| + 1 * |S| := by gcongr
      _ = |R| + |S| := by ring
  have hY : |(u' * u + u * u') * R + u * u * R' + ((u' * u + u * u') * u + u * u * u') * S
      + u * u * u * S'| ≤ 2 * ν * |R| + |R'| + 3 * ν * |S| + |S'| := by
    have t1 := abs_add_le ((u' * u + u * u') * R + u * u * R' + ((u' * u + u * u') * u + u * u * u') * S)
      (u * u * u * S')
    have t2 := abs_add_le ((u' * u + u * u') * R + u * u * R') (((u' * u + u * u') * u + u * u * u') * S)
    have t3 := abs_add_le ((u' * u + u * u') * R) (u * u * R')
    have e1 : |(u' * u + u * u') * R| = |u' * u + u * u'| * |R| := abs_mul _ _
    have e2 : |u * u * R'| = |u * u| * |R'| := abs_mul _ _
    have e3 : |((u' * u + u * u') * u + u * u * u') * S| = |(u' * u + u * u') * u + u * u * u'| * |S| :=
      abs_mul _ _
    have e4 : |u * u * u * S'| = |u * u * u| * |S'| := abs_mul _ _
    have b1 : |u' * u + u * u'| * |R| ≤ 2 * ν * |R| := mul_le_mul_of_nonneg_right k3 (abs_nonneg _)
    have b2 : |u * u| * |R'| ≤ |R'| := mul_le_of_le_one_left (abs_nonneg _) k1
    have b3 : |(u' * u + u * u') * u + u * u * u'| * |S| ≤ 3 * ν * |S| :=
      mul_le_mul_of_nonneg_right k4 (abs_nonneg _)
    have b4 : |u * u * u| * |S'| ≤ |S'| := mul_le_of_le_one_left (abs_nonneg _) k2
    linarith
  have hXb : |u * u * R + u * u * u * S| ≤ 4 * K1 * r + 2 * K1 * r ^ 3 := by linarith
  have hYb : |(u' * u + u * u') * R + u * u * R' + ((u' * u + u * u') * u + u * u * u') * S
      + u * u * u * S'| ≤ 2 * ν * (4 * K1 * r) + 4 * K2 * r + 3 * ν * (2 * K1 * r ^ 3)
        + 2 * K2 * r ^ 3 := by
    have c1 := mul_le_mul_of_nonneg_left hR (by linarith : (0:ℝ) ≤ 2 * ν)
    have c2 := mul_le_mul_of_nonneg_left hS (by linarith : (0:ℝ) ≤ 3 * ν)
    linarith
  have hP : ∀ k : ℕ, k ≤ 5 → r ^ k ≤ (1 + r) ^ 5 := fun k hk =>
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) k).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) hk)
  have hP1 : r ^ 1 ≤ (1 + r) ^ 5 := hP 1 (by norm_num)
  have hP3 : r ^ 3 ≤ (1 + r) ^ 5 := hP 3 (by norm_num)
  have hP5 : r ^ 5 ≤ (1 + r) ^ 5 := hP 5 (by norm_num)
  have hP0 : 0 ≤ (1 + r) ^ 5 := pow_nonneg (by linarith) 5
  have key : ν * K1 * (r ^ 5 + 8 * r ^ 3 + 8 * r) + K2 * (4 * r + 2 * r ^ 3)
      ≤ 20 * (1 + ν) * (K1 + K2) * (1 + r) ^ 5 := by
    have hA : r ^ 5 + 8 * r ^ 3 + 8 * r ≤ 17 * (1 + r) ^ 5 := by
      simp only [pow_one] at hP1; linarith
    have hB : 4 * r + 2 * r ^ 3 ≤ 6 * (1 + r) ^ 5 := by
      simp only [pow_one] at hP1; linarith
    have hC : 0 ≤ 20 * K1 + 14 * K2 + 3 * ν * K1 + 20 * ν * K2 := by
      nlinarith [mul_nonneg hν hK1, mul_nonneg hν hK2]
    nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hν hK1),
      mul_le_mul_of_nonneg_left hB hK2, mul_nonneg hC hP0]
  have hEw : 0 ≤ E * w := mul_nonneg hE hw0
  have ha' : E * w * |u * u * R + u * u * u * S|
      ≤ E * (ν * r ^ 2 / 2) * (4 * K1 * r + 2 * K1 * r ^ 3) := by
    calc E * w * |u * u * R + u * u * u * S|
        ≤ E * (ν * r ^ 2 / 2) * |u * u * R + u * u * u * S| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hE) (abs_nonneg _)
      _ ≤ E * (ν * r ^ 2 / 2) * (4 * K1 * r + 2 * K1 * r ^ 3) :=
          mul_le_mul_of_nonneg_left hXb (mul_nonneg hE (div_nonneg (mul_nonneg hν (sq_nonneg r))
            (by norm_num)))
  unfold pamDerivVal
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hEw, abs_mul, abs_of_nonneg hE]
  refine (add_le_add ha' (mul_le_mul_of_nonneg_left hYb hE)).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left key hE]

theorem pam_val_real (E u R S r K1 K2 ν : ℝ) (hE : 0 ≤ E) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hR : |R| ≤ 4 * K1 * r) (hS : |S| ≤ 2 * K1 * r ^ 3) (hr : 0 ≤ r) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (hν : 0 ≤ ν) :
    |E * (u * u * R + u * u * u * S)| ≤ E * (20 * (1 + ν) * (K1 + K2) * (1 + r) ^ 5) := by
  have hu2' : 0 ≤ u * u := mul_nonneg hu0 hu0
  have hu2 : u * u ≤ 1 := by nlinarith
  have hu3' : 0 ≤ u * u * u := mul_nonneg hu2' hu0
  have hu3 : u * u * u ≤ 1 := by nlinarith
  have k1 : |u * u| ≤ 1 := by rw [abs_of_nonneg hu2']; exact hu2
  have k2 : |u * u * u| ≤ 1 := by rw [abs_of_nonneg hu3']; exact hu3
  have hX : |u * u * R + u * u * u * S| ≤ |R| + |S| := by
    calc |u * u * R + u * u * u * S| ≤ |u * u * R| + |u * u * u * S| := abs_add_le _ _
      _ = |u * u| * |R| + |u * u * u| * |S| := by simp only [abs_mul]
      _ ≤ 1 * |R| + 1 * |S| := by gcongr
      _ = |R| + |S| := by ring
  have hP : ∀ k : ℕ, k ≤ 5 → r ^ k ≤ (1 + r) ^ 5 := fun k hk =>
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) k).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) hk)
  have hP1 : r ^ 1 ≤ (1 + r) ^ 5 := hP 1 (by norm_num)
  have hP3 : r ^ 3 ≤ (1 + r) ^ 5 := hP 3 (by norm_num)
  have hP0 : 0 ≤ (1 + r) ^ 5 := pow_nonneg (by linarith) 5
  simp only [pow_one] at hP1
  have key2 : 4 * K1 * r + 2 * K1 * r ^ 3 ≤ 20 * (1 + ν) * (K1 + K2) * (1 + r) ^ 5 := by
    have hC : 0 ≤ 14 * K1 + 20 * K2 + 20 * ν * K1 + 20 * ν * K2 := by
      nlinarith [mul_nonneg hν hK1, mul_nonneg hν hK2]
    nlinarith [mul_le_mul_of_nonneg_left hP1 hK1, mul_le_mul_of_nonneg_left hP3 hK1,
      mul_nonneg hC hP0]
  have h1 : |u * u * R + u * u * u * S| ≤ 4 * K1 * r + 2 * K1 * r ^ 3 := by linarith
  rw [abs_mul, abs_of_nonneg hE]
  exact (mul_le_mul_of_nonneg_left h1 hE).trans (mul_le_mul_of_nonneg_left key2 hE)

theorem pam_poly5_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h5 := gp_gauss_pow_summable t α c hα hc 5
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ 5 := pow_nonneg (by linarith [abs_nonneg t]) 5
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add h5).mul_left (16 * (1 + |t| + c) ^ 5))
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
    have := add_pow_le (by norm_num : (0:ℝ) ≤ 1) hz 5
    norm_num at this
    linarith
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  calc (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ 5 * (1 + |(j : ℝ)|) ^ 5) * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ ≤ ((1 + |t| + c) ^ 5 * (16 * (1 + |(j : ℝ)| ^ 5))) *
          Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK) hE
    _ = 16 * (1 + |t| + c) ^ 5 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

theorem pam_G_bound (ν t : ℝ) (hν : 0 ≤ ν) (ha1 : 1 ≤ ageA ν t) (K1 K2 : ℝ) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (M : Mat3) (y : ℝ × ℝ) (hM : ∀ i j, |M i j| ≤ K1) :
    |psiPhiD ν t M y (0, 1)| ≤
      Real.exp (-(sq2 y) / (4 * ageA ν t)) * (20 * (1 + ν) * (K1 + K2) * (1 + ‖y‖) ^ 5) := by
  rw [pam_psiPhiD_e2]
  have hu0 : 0 ≤ (ageA ν t)⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  exact pam_val_real (Real.exp (-(sq2 y) / (4 * ageA ν t))) ((ageA ν t)⁻¹) (pamRe M y) (pamSe M y)
    ‖y‖ K1 K2 ν (Real.exp_pos _).le hu0 hu1 (pam_pamRe_le M y K1 hM) (pam_pamSe_le M y K1 hM)
    (norm_nonneg y) hK1 hK2 hν

theorem pam_GD_bound (ν t : ℝ) (hν : 0 ≤ ν) (ha1 : 1 ≤ ageA ν t) (K1 K2 : ℝ) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (M D : Mat3) (y : ℝ × ℝ) (hM : ∀ i j, |M i j| ≤ K1)
    (hD : ∀ i j, |D i j| ≤ K2) :
    |pamGD ν t M D y| ≤
      Real.exp (-(sq2 y) / (4 * ageA ν t)) * (20 * (1 + ν) * (K1 + K2) * (1 + ‖y‖) ^ 5) := by
  unfold pamGD
  have ha0 : 0 ≤ ageA ν t := by linarith
  obtain ⟨hw0, hw⟩ := pam_w_bound ν (ageA ν t) y hν ha1
  have hu0 : 0 ≤ (ageA ν t)⁻¹ := inv_nonneg.mpr ha0
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have hu' : |-ν / (ageA ν t) ^ 2| ≤ ν := by
    rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg hν (sq_nonneg _))]
    exact div_le_self hν (one_le_pow₀ ha1)
  exact pam_deriv_real (Real.exp (-(sq2 y) / (4 * ageA ν t))) _ _ _ (pamRe M y) (pamRe D y)
    (pamSe M y) (pamSe D y) ‖y‖ K1 K2 ν (Real.exp_pos _).le hw0 hw hu0 hu1 hu'
    (pam_pamRe_le M y K1 hM) (pam_pamRe_le D y K2 hD) (pam_pamSe_le M y K1 hM)
    (pam_pamSe_le D y K2 hD) (norm_nonneg y) hK1 hK2 hν

theorem pam_dom (C0 ν s t : ℝ) (hC0 : 0 ≤ C0) (ha1 : 1 ≤ ageA ν t)
    (hPm : ageA ν t ≤ 1 + ν * (2 * s)) (x : ℝ × ℝ) (n : ℤ) :
    Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) * (C0 * (1 + ‖xj ν n x‖) ^ 5)
      ≤ C0 * (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
  have hE := sp_exp_le ν t (1 + ν * (2 * s)) (xj ν n x) ha1 hPm
  have hxj : (xj ν n x).1 = x.1 - (n : ℝ) * cOf ν := rfl
  rw [hxj] at hE
  have hp : (1 + ‖xj ν n x‖) ^ 5 ≤ (1 + |x.2|) ^ 5 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [norm_nonneg (xj ν n x)]) (gp_one_add_norm ν n x) 5
  calc Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) * (C0 * (1 + ‖xj ν n x‖) ^ 5)
      ≤ Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2) *
          (C0 * ((1 + |x.2|) ^ 5 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5)) :=
        mul_le_mul hE (mul_le_mul_of_nonneg_left hp hC0) (mul_nonneg hC0 (by positivity))
          (Real.exp_pos _).le
    _ = C0 * (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by ring

theorem pam_fderiv (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (M : Mat3) (x v : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => ∑' j : ℤ, psiPhi ν s M (xj ν j z)) x v
      = ∑' j : ℤ, psiPhiD ν s M (xj ν j x) v := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hu := ubd_summable ν s ha1 x M hν
  have hval : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 → ∀ w : ℝ × ℝ,
      ‖psiPhiD ν s M (xj ν j z) w‖ ≤ ubd ν s x M j * ‖w‖ := by
    intro j z hz w
    have h1 := psiPhiD_bound ν s ha1 M (xj ν j z) w
    have h2 := ball_geom ν s ha1 x z hz j
    have hn := norm_nonneg w
    have h6 : 0 ≤ 6 * Kmat M := by have := Kmat_nonneg M; linarith
    have h3 : 6 * Kmat M * ‖w‖ * ((1 + ‖xj ν j z‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)))
        ≤ 6 * Kmat M * ‖w‖ * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
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
    intro w
    rw [fderiv_term]
    exact hval j z hz w
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
  have hd : fderiv ℝ (fun z : ℝ × ℝ => ∑' j : ℤ, psiPhi ν s M (xj ν j z)) x
      = ∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x := key.fderiv
  rw [hd]
  have hsum' : Summable (fun n : ℤ => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) :=
    Summable.of_norm_bounded hu (fun n => hfb n x (by simp))
  calc (∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) v
      = ∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x v :=
        (ContinuousLinearMap.apply ℝ ℝ v).map_tsum hsum'
    _ = ∑' n : ℤ, psiPhiD ν s M (xj ν n x) v := tsum_congr fun n => fderiv_term ν s M n x v

theorem psipAMixedS (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipAMixedS as χf := by
  unfold PsipAMixedS
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
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC0 : 0 ≤ 20 * (1 + ν) * (K1 + K2) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hsum : Summable (fun n : ℤ => 20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (pam_poly5_summable x.1 _ (cOf ν) hα hc).mul_left (20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5)
  have hbdG : ∀ (n : ℤ) (t : ℝ), t ∈ Icc (s / 2) (2 * s) →
      |psiPhiD ν t (Ay ν χf A t) (xj ν n x) (0, 1)| ≤
        20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n t ht
    have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith [mul_pos hν (hJpos t ht)]
    refine (pam_G_bound ν t hν.le ha1 K1 K2 hK1nn hK2nn (Ay ν χf A t) (xj ν n x) (hMb t ht)).trans ?_
    exact pam_dom (20 * (1 + ν) * (K1 + K2)) ν s t hC0 ha1 (hPm t ht) x n
  have hbdGD : ∀ (n : ℤ) (t : ℝ), t ∈ Icc (s / 2) (2 * s) →
      ‖pamGD ν t (Ay ν χf A t) (deriv (Ay ν χf A) t) (xj ν n x)‖ ≤
        20 * (1 + ν) * (K1 + K2) * (1 + |x.2|) ^ 5 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n t ht
    have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith [mul_pos hν (hJpos t ht)]
    rw [Real.norm_eq_abs]
    refine (pam_GD_bound ν t hν.le ha1 K1 K2 hK1nn hK2nn (Ay ν χf A t) (deriv (Ay ν χf A) t)
      (xj ν n x) (hMb t ht) (hDb t ht)).trans ?_
    exact pam_dom (20 * (1 + ν) * (K1 + K2)) ν s t hC0 ha1 (hPm t ht) x n
  have hg0 : Summable (fun n : ℤ => psiPhiD ν s (Ay ν χf A s) (xj ν n x) (0, 1)) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hbdG n s hsJ)
  have key := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 20 * (1 + ν) * (K1 + K2) *
      (1 + |x.2|) ^ 5 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 5 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (g := fun n τ => psiPhiD ν τ (Ay ν χf A τ) (xj ν n x) (0, 1))
    (g' := fun n τ => pamGD ν τ (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (xj ν n x))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s) hsum isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => pam_G_hasDerivAt ν τ hν (hJpos τ (Ioo_subset_Icc_self hτ)) (xj ν n x)
      ((hMd τ (hJpos τ (Ioo_subset_Icc_self hτ))).hasDerivAt))
    (fun n τ hτ => hbdGD n τ (Ioo_subset_Icc_self hτ))
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hfd : ∀ t : ℝ, 0 < t → fderiv ℝ (psipA ν χf A t) x (0, 1)
      = ∑' n : ℤ, psiPhiD ν t (Ay ν χf A t) (xj ν n x) (0, 1) := by
    intro t ht
    have ha : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
    have hfun : psipA ν χf A t = fun z => ∑' j : ℤ, psiPhi ν t (Ay ν χf A t) (xj ν j z) :=
      funext fun z => psipA_eq_phi ν χf A t z ha
    rw [hfun]
    exact pam_fderiv ν t hν ht (Ay ν χf A t) x (0, 1)
  have hev : (fun s' => fderiv ℝ (psipA ν χf A s') x (0, 1)) =ᶠ[𝓝 s]
      (fun s' => ∑' n : ℤ, psiPhiD ν s' (Ay ν χf A s') (xj ν n x) (0, 1)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    exact hfd τ (by linarith [hτ.1])
  have hd : DifferentiableAt ℝ
      (fun s' => ∑' n : ℤ, psiPhiD ν s' (Ay ν χf A s') (xj ν n x) (0, 1)) s := key.differentiableAt
  have hei : ei 1 = ((0:ℝ), (1:ℝ)) := rfl
  rw [hei]
  exact hd.congr_of_eventuallyEq hev

end UnforcedLeray.Short.PartIIIb.Concrete
