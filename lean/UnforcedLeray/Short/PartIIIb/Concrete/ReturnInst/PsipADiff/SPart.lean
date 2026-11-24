import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart

/-!
# `C/inst/5` s-part: differentiability of `s' ↦ ψ^p_A(s', x)` at `s > 0` (source 4978, 4741-4745)

Each lattice term `s' ↦ ψ_j(s')` is differentiable with a derivative bounded by a summable
Gaussian majorant, uniformly on `[s/2, 2s]`, because `A^y = χ_f A` is `C^1` on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sp_entry_le (M : Mat3) (i j : Fin 3) : |M i j| ≤ ‖M‖ := by
  have h1 := norm_le_pi_norm M i
  have h2 := norm_le_pi_norm (M i) j
  rw [Real.norm_eq_abs] at h2
  linarith

theorem sp_entry_hasDerivAt {M : ℝ → Mat3} {D : Mat3} {t : ℝ} (h : HasDerivAt M D t)
    (i j : Fin 3) : HasDerivAt (fun τ => M τ i j) (D i j) t :=
  (hasDerivAt_pi.mp ((hasDerivAt_pi.mp h) i)) j

theorem sp_Q_bound (a00 a02 a20 a22 y1 y2 K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (h00 : |a00| ≤ K) (h02 : |a02| ≤ K) (h20 : |a20| ≤ K) (h22 : |a22| ≤ K)
    (hy1 : |y1| ≤ R) (hy2 : |y2| ≤ R) :
    |2 * y1 * (a00 * y1 + a02 * y2) + 2 * y2 * (a20 * y1 + a22 * y2)| ≤ 8 * K * R ^ 2 := by
  have m1 : |a00 * y1 + a02 * y2| ≤ 2 * K * R := by
    have t1 := abs_add_le (a00 * y1) (a02 * y2)
    rw [abs_mul, abs_mul] at t1
    have e1 := mul_le_mul h00 hy1 (abs_nonneg _) hK
    have e2 := mul_le_mul h02 hy2 (abs_nonneg _) hK
    nlinarith
  have m2 : |a20 * y1 + a22 * y2| ≤ 2 * K * R := by
    have t1 := abs_add_le (a20 * y1) (a22 * y2)
    rw [abs_mul, abs_mul] at t1
    have e1 := mul_le_mul h20 hy1 (abs_nonneg _) hK
    have e2 := mul_le_mul h22 hy2 (abs_nonneg _) hK
    nlinarith
  have n1 : |2 * y1 * (a00 * y1 + a02 * y2)| ≤ 4 * K * R ^ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hy1 m1 (abs_nonneg _) hR
    nlinarith
  have n2 : |2 * y2 * (a20 * y1 + a22 * y2)| ≤ 4 * K * R ^ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hy2 m2 (abs_nonneg _) hR
    nlinarith
  have := abs_add_le (2 * y1 * (a00 * y1 + a02 * y2)) (2 * y2 * (a20 * y1 + a22 * y2))
  linarith

theorem sp_Pr_bound (a K1 R T Q : ℝ) (ha : 1 ≤ a) (hK1 : 0 ≤ K1) (hR : 0 ≤ R)
    (hT : |T| ≤ 2 * K1) (hQ : |Q| ≤ 8 * K1 * R ^ 2) :
    |T + Q / (4 * a)| ≤ 2 * K1 * (1 + R ^ 2) := by
  have h4 : 0 < 4 * a := by linarith
  have hd : |Q / (4 * a)| ≤ 2 * K1 * R ^ 2 := by
    rw [abs_div, abs_of_pos h4, div_le_iff₀ h4]
    nlinarith [mul_nonneg (mul_nonneg hK1 (sq_nonneg R)) (sub_nonneg.2 ha)]
  calc |T + Q / (4 * a)| ≤ |T| + |Q / (4 * a)| := abs_add_le _ _
    _ ≤ 2 * K1 + 2 * K1 * R ^ 2 := add_le_add hT hd
    _ = 2 * K1 * (1 + R ^ 2) := by ring

theorem sp_Prd_bound (a ν K1 K2 R T' Q Q' : ℝ) (ha : 1 ≤ a) (hν : 0 ≤ ν) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (hR : 0 ≤ R) (hT' : |T'| ≤ 2 * K2) (hQ : |Q| ≤ 8 * K1 * R ^ 2)
    (hQ' : |Q'| ≤ 8 * K2 * R ^ 2) :
    |T' + (Q' * (4 * a) - Q * (4 * ν)) / (4 * a) ^ 2|
      ≤ 2 * K2 + 2 * K2 * R ^ 2 + 2 * K1 * ν * R ^ 2 := by
  have h4 : 0 < 4 * a := by linarith
  have h4' : 0 < 4 * a ^ 2 := by
    have : (1:ℝ) ≤ a ^ 2 := one_le_pow₀ ha
    linarith
  have ha2 : (1:ℝ) ≤ a ^ 2 := one_le_pow₀ ha
  have e : (Q' * (4 * a) - Q * (4 * ν)) / (4 * a) ^ 2 = Q' / (4 * a) - Q * ν / (4 * a ^ 2) := by
    field_simp
  have h1 : |Q' / (4 * a)| ≤ 2 * K2 * R ^ 2 := by
    rw [abs_div, abs_of_pos h4, div_le_iff₀ h4]
    nlinarith [mul_nonneg (mul_nonneg hK2 (sq_nonneg R)) (sub_nonneg.2 ha)]
  have h2 : |Q * ν / (4 * a ^ 2)| ≤ 2 * K1 * ν * R ^ 2 := by
    rw [abs_div, abs_of_pos h4', abs_mul, abs_of_nonneg hν, div_le_iff₀ h4']
    nlinarith [mul_le_mul_of_nonneg_right hQ hν,
      mul_nonneg (mul_nonneg (mul_nonneg hK1 (sq_nonneg R)) hν) (sub_nonneg.2 ha2)]
  calc |T' + (Q' * (4 * a) - Q * (4 * ν)) / (4 * a) ^ 2|
      = |T' + (Q' / (4 * a) - Q * ν / (4 * a ^ 2))| := by rw [e]
    _ ≤ |T'| + |Q' / (4 * a) - Q * ν / (4 * a ^ 2)| := abs_add_le _ _
    _ ≤ |T'| + (|Q' / (4 * a)| + |Q * ν / (4 * a ^ 2)|) := by
        linarith [abs_sub (Q' / (4 * a)) (Q * ν / (4 * a ^ 2))]
    _ ≤ 2 * K2 + 2 * K2 * R ^ 2 + 2 * K1 * ν * R ^ 2 := by linarith

theorem sp_gD_bound (a c ν R : ℝ) (ha : 1 ≤ a) (hν : 0 ≤ ν) (hc0 : 0 ≤ c)
    (hcR : c ≤ 2 * R ^ 2) :
    |(0 * (4 * a) - (-c) * (4 * ν)) / (4 * a) ^ 2| ≤ ν * R ^ 2 / 2 := by
  have e : (0 * (4 * a) - (-c) * (4 * ν)) / (4 * a) ^ 2 = c * ν / (4 * a ^ 2) := by ring
  have ha2 : (1:ℝ) ≤ a ^ 2 := one_le_pow₀ ha
  have hpos : 0 < 4 * a ^ 2 := by linarith
  rw [e, abs_of_nonneg (div_nonneg (mul_nonneg hc0 hν) hpos.le), div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_right hcR hν,
    mul_nonneg (mul_nonneg hν (sq_nonneg R)) (sub_nonneg.2 ha2)]

theorem sp_K_bound (a : ℝ) (ha : 1 ≤ a) : |-2 * a⁻¹| ≤ 2 := by
  have hi : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have hp : 0 < a⁻¹ := inv_pos.mpr (by linarith)
  rw [abs_of_neg (by linarith)]
  linarith

theorem sp_K'_bound (a ν : ℝ) (ha : 1 ≤ a) (hν : 0 ≤ ν) : |-2 * (-ν / a ^ 2)| ≤ 2 * ν := by
  have ha2 : (1:ℝ) ≤ a ^ 2 := one_le_pow₀ ha
  have e : -2 * (-ν / a ^ 2) = 2 * (ν / a ^ 2) := by ring
  have h0 : 0 ≤ ν / a ^ 2 := div_nonneg hν (by linarith)
  have h1 : ν / a ^ 2 ≤ ν := div_le_self hν ha2
  rw [e, abs_of_nonneg (by linarith)]
  linarith

/-- The pieces of `s' ↦ Φ_{M(s')}(y)`: the explicit derivative value. -/
def sV (ν : ℝ) (y : ℝ × ℝ) (Mt D : Mat3) (t : ℝ) : ℝ :=
  (-2 * (ageA ν t)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν t))) *
      ((D 0 0 + D 2 2) +
        ((2 * y.1 * (D 0 0 * y.1 + D 0 2 * y.2) + 2 * y.2 * (D 2 0 * y.1 + D 2 2 * y.2))
            * (4 * ageA ν t)
          - (2 * y.1 * (Mt 0 0 * y.1 + Mt 0 2 * y.2) + 2 * y.2 * (Mt 2 0 * y.1 + Mt 2 2 * y.2))
            * (4 * ν)) / (4 * ageA ν t) ^ 2)
    + (-2 * (-ν / (ageA ν t) ^ 2) * Real.exp (-(sq2 y) / (4 * ageA ν t))
        + (-2 * (ageA ν t)⁻¹) * (Real.exp (-(sq2 y) / (4 * ageA ν t)) *
            ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2))) *
      ((Mt 0 0 + Mt 2 2) +
        (2 * y.1 * (Mt 0 0 * y.1 + Mt 0 2 * y.2) + 2 * y.2 * (Mt 2 0 * y.1 + Mt 2 2 * y.2))
          / (4 * ageA ν t))

theorem sdiff_real (K K' E E' Pr Pr' R ν K1 K2 : ℝ) (hK : |K| ≤ 2) (hK' : |K'| ≤ 2 * ν)
    (hE : 0 ≤ E) (hE' : |E'| ≤ E * (ν * R ^ 2 / 2)) (hPr : |Pr| ≤ 2 * K1 * (1 + R ^ 2))
    (hPr' : |Pr'| ≤ 2 * K2 + 2 * K2 * R ^ 2 + 2 * K1 * ν * R ^ 2)
    (hν : 0 ≤ ν) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hR : 0 ≤ R) :
    |K * E * Pr' + (K' * E + K * E') * Pr| ≤ (10 * ν * K1 + 8 * K2) * (1 + R) ^ 4 * E := by
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have p1 : 1 + R ^ 2 ≤ (1 + R) ^ 4 := by nlinarith [mul_nonneg hR hR, pow_nonneg hR 3]
  have p2 : R ^ 2 ≤ (1 + R) ^ 4 := by nlinarith [mul_nonneg hR hR, pow_nonneg hR 3]
  have p3 : R ^ 2 * (1 + R ^ 2) ≤ (1 + R) ^ 4 := by
    nlinarith [mul_nonneg hR hR, pow_nonneg hR 3, pow_nonneg hR 4]
  have t1 : |K * E * Pr'| ≤ E * (4 * K2 + 4 * K2 * R ^ 2 + 4 * K1 * ν * R ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hE]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hK hE) hPr' (abs_nonneg _)
      (mul_nonneg (by norm_num) hE)
    calc |K| * E * |Pr'| ≤ 2 * E * (2 * K2 + 2 * K2 * R ^ 2 + 2 * K1 * ν * R ^ 2) := h
      _ = E * (4 * K2 + 4 * K2 * R ^ 2 + 4 * K1 * ν * R ^ 2) := by ring
  have s1 : |K' * E + K * E'| ≤ E * (2 * ν + ν * R ^ 2) := by
    calc |K' * E + K * E'| ≤ |K' * E| + |K * E'| := abs_add_le _ _
      _ = |K'| * E + |K| * |E'| := by rw [abs_mul, abs_mul, abs_of_nonneg hE]
      _ ≤ 2 * ν * E + 2 * (E * (ν * R ^ 2 / 2)) :=
          add_le_add (mul_le_mul_of_nonneg_right hK' hE) (mul_le_mul hK hE' (abs_nonneg _) (by norm_num))
      _ = E * (2 * ν + ν * R ^ 2) := by ring
  have t2 : |(K' * E + K * E') * Pr| ≤ E * (2 * ν + ν * R ^ 2) * (2 * K1 * (1 + R ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul s1 hPr (abs_nonneg _) (mul_nonneg hE (by nlinarith [mul_nonneg hν hR2]))
  have hsum := (abs_add_le (K * E * Pr') ((K' * E + K * E') * Pr))
  have a1 : K2 * E * (1 + R ^ 2) ≤ K2 * E * (1 + R) ^ 4 :=
    mul_le_mul_of_nonneg_left p1 (mul_nonneg hK2 hE)
  have a2 : K2 * E * R ^ 2 ≤ K2 * E * (1 + R) ^ 4 :=
    mul_le_mul_of_nonneg_left p2 (mul_nonneg hK2 hE)
  have a3 : K1 * ν * E * R ^ 2 ≤ K1 * ν * E * (1 + R) ^ 4 :=
    mul_le_mul_of_nonneg_left p2 (mul_nonneg (mul_nonneg hK1 hν) hE)
  have a4 : ν * K1 * E * (1 + R ^ 2) ≤ ν * K1 * E * (1 + R) ^ 4 :=
    mul_le_mul_of_nonneg_left p1 (mul_nonneg (mul_nonneg hν hK1) hE)
  have a5 : ν * K1 * E * (R ^ 2 * (1 + R ^ 2)) ≤ ν * K1 * E * (1 + R) ^ 4 :=
    mul_le_mul_of_nonneg_left p3 (mul_nonneg (mul_nonneg hν hK1) hE)
  have t2' : E * (2 * ν + ν * R ^ 2) * (2 * K1 * (1 + R ^ 2))
      = 4 * ν * K1 * E * (1 + R ^ 2) + 2 * ν * K1 * E * (R ^ 2 * (1 + R ^ 2)) := by ring
  nlinarith [hsum, t1, t2, a1, a2, a3, a4, a5, t2']


theorem sV_hasDerivAt (ν : ℝ) (hν : 0 < ν) (y : ℝ × ℝ) (M : ℝ → Mat3) (D : Mat3) (t : ℝ)
    (ht : 0 < t) (hM : HasDerivAt M D t) :
    HasDerivAt (fun τ => psiPhi ν τ (M τ) y) (sV ν y (M t) D t) t := by
  have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith
  have ha0 : 0 < ageA ν t := by linarith
  have hA : HasDerivAt (fun τ => ageA ν τ) ν t := by
    unfold ageA
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have hK : HasDerivAt (fun τ => -2 * (ageA ν τ)⁻¹) (-2 * (-ν / (ageA ν t) ^ 2)) t :=
    (hA.inv ha0.ne').const_mul (-2)
  have hne : 4 * ageA ν t ≠ 0 := by linarith
  have hg : HasDerivAt (fun τ => -(sq2 y) / (4 * ageA ν τ))
      ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2) t :=
    (hasDerivAt_const t (-(sq2 y))).div (hA.const_mul 4) hne
  have hE := hg.exp
  have hT : HasDerivAt (fun τ => M τ 0 0 + M τ 2 2) (D 0 0 + D 2 2) t :=
    (sp_entry_hasDerivAt hM 0 0).add (sp_entry_hasDerivAt hM 2 2)
  have hQ : HasDerivAt (fun τ => 2 * y.1 * (M τ 0 0 * y.1 + M τ 0 2 * y.2)
        + 2 * y.2 * (M τ 2 0 * y.1 + M τ 2 2 * y.2))
      (2 * y.1 * (D 0 0 * y.1 + D 0 2 * y.2) + 2 * y.2 * (D 2 0 * y.1 + D 2 2 * y.2)) t := by
    have h1 := ((sp_entry_hasDerivAt hM 0 0).mul_const y.1).add
      ((sp_entry_hasDerivAt hM 0 2).mul_const y.2)
    have h2 := ((sp_entry_hasDerivAt hM 2 0).mul_const y.1).add
      ((sp_entry_hasDerivAt hM 2 2).mul_const y.2)
    exact (h1.const_mul (2 * y.1)).add (h2.const_mul (2 * y.2))
  have hQd := hQ.div (hA.const_mul 4) hne
  have hPr := hT.add hQd
  have hKE := hK.mul hE
  have hF := hKE.mul hPr
  have efun : (fun τ => psiPhi ν τ (M τ) y) = fun τ =>
      (-2 * (ageA ν τ)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν τ))) *
        ((M τ 0 0 + M τ 2 2) +
          (2 * y.1 * (M τ 0 0 * y.1 + M τ 0 2 * y.2) + 2 * y.2 * (M τ 2 0 * y.1 + M τ 2 2 * y.2))
            / (4 * ageA ν τ)) := by
    funext τ
    simp only [psiPhi, merApply, merTrace]
    ring
  rw [efun]
  unfold sV
  exact hF.congr_deriv (by simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply]; ring)

theorem sV_bound (ν : ℝ) (hν : 0 < ν) (y : ℝ × ℝ) (K1 K2 : ℝ) (Mt D : Mat3) (t : ℝ)
    (ht : 0 < t) (hMb : ∀ i j, |Mt i j| ≤ K1) (hDb : ∀ i j, |D i j| ≤ K2) :
    |sV ν y Mt D t| ≤ (10 * ν * K1 + 8 * K2) * (1 + ‖y‖) ^ 4 *
      Real.exp (-(sq2 y) / (4 * ageA ν t)) := by
  have ha1 : 1 ≤ ageA ν t := by unfold ageA; nlinarith
  have hK1 : 0 ≤ K1 := le_trans (abs_nonneg _) (hMb 0 0)
  have hK2 : 0 ≤ K2 := le_trans (abs_nonneg _) (hDb 0 0)
  have hR : 0 ≤ ‖y‖ := norm_nonneg y
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
  have hT : |Mt 0 0 + Mt 2 2| ≤ 2 * K1 :=
    (abs_add_le _ _).trans (by linarith [hMb 0 0, hMb 2 2])
  have hTD : |D 0 0 + D 2 2| ≤ 2 * K2 :=
    (abs_add_le _ _).trans (by linarith [hDb 0 0, hDb 2 2])
  have hQ := sp_Q_bound (Mt 0 0) (Mt 0 2) (Mt 2 0) (Mt 2 2) y.1 y.2 K1 ‖y‖ hK1 hR
    (hMb 0 0) (hMb 0 2) (hMb 2 0) (hMb 2 2) (abs_fst_le' y) (abs_snd_le' y)
  have hQ' := sp_Q_bound (D 0 0) (D 0 2) (D 2 0) (D 2 2) y.1 y.2 K2 ‖y‖ hK2 hR
    (hDb 0 0) (hDb 0 2) (hDb 2 0) (hDb 2 2) (abs_fst_le' y) (abs_snd_le' y)
  have hPr := sp_Pr_bound (ageA ν t) K1 ‖y‖ (Mt 0 0 + Mt 2 2)
    (2 * y.1 * (Mt 0 0 * y.1 + Mt 0 2 * y.2) + 2 * y.2 * (Mt 2 0 * y.1 + Mt 2 2 * y.2))
    ha1 hK1 hR hT hQ
  have hPr' := sp_Prd_bound (ageA ν t) ν K1 K2 ‖y‖ (D 0 0 + D 2 2)
    (2 * y.1 * (Mt 0 0 * y.1 + Mt 0 2 * y.2) + 2 * y.2 * (Mt 2 0 * y.1 + Mt 2 2 * y.2))
    (2 * y.1 * (D 0 0 * y.1 + D 0 2 * y.2) + 2 * y.2 * (D 2 0 * y.1 + D 2 2 * y.2))
    ha1 hν.le hK1 hK2 hR hTD hQ hQ'
  have hE' : |Real.exp (-(sq2 y) / (4 * ageA ν t)) *
      ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2)|
        ≤ Real.exp (-(sq2 y) / (4 * ageA ν t)) * (ν * ‖y‖ ^ 2 / 2) := by
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (sp_gD_bound (ageA ν t) (sq2 y) ν ‖y‖ ha1 hν.le hc0 hcR)
      (Real.exp_pos _).le
  have hK := sp_K_bound (ageA ν t) ha1
  have hK' := sp_K'_bound (ageA ν t) ν ha1 hν.le
  unfold sV
  exact sdiff_real _ _ _ _ _ _ _ _ _ _ hK hK' (Real.exp_pos _).le hE' hPr hPr' hν.le hK1 hK2 hR

theorem sp_exp_le (ν t Pm : ℝ) (y : ℝ × ℝ) (ha1 : 1 ≤ ageA ν t) (hPm : ageA ν t ≤ Pm) :
    Real.exp (-(sq2 y) / (4 * ageA ν t)) ≤ Real.exp (-(1 / (4 * Pm)) * y.1 ^ 2) := by
  apply Real.exp_le_exp.mpr
  have ha0 : 0 < ageA ν t := by linarith
  have hPm0 : 0 < Pm := by linarith
  have hsq : y.1 ^ 2 ≤ sq2 y := by unfold sq2; nlinarith [sq_nonneg y.2]
  have hle : 1 / (4 * Pm) ≤ 1 / (4 * ageA ν t) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h1 : (1 / (4 * Pm)) * y.1 ^ 2 ≤ (1 / (4 * ageA ν t)) * sq2 y :=
    (mul_le_mul_of_nonneg_right hle (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (by positivity))
  have e : -(sq2 y) / (4 * ageA ν t) = -((1 / (4 * ageA ν t)) * sq2 y) := by ring
  rw [e]
  linarith

theorem sp_poly4_summable (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have h4 := gp_gauss_pow_summable t α c hα hc 4
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ 4 := pow_nonneg (by linarith [abs_nonneg t]) 4
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add h4).mul_left (8 * (1 + |t| + c) ^ 4))
  have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |t| + c) * (1 + |(j : ℝ)|) := by
    have h1 : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
      have h2 := abs_sub t ((j : ℝ) * c)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg t, mul_nonneg hz hc.le, mul_nonneg (abs_nonneg t) hz]
  have h1 : (1 + |t - (j : ℝ) * c|) ^ 4 ≤ (1 + |t| + c) ^ 4 * (1 + |(j : ℝ)|) ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu 4
  have h2 : (1 + |(j : ℝ)|) ^ 4 ≤ 8 * (1 + |(j : ℝ)| ^ 4) := by
    have hq : 0 ≤ 7 * |(j : ℝ)| ^ 2 + 10 * |(j : ℝ)| + 7 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (|(j : ℝ)| - 1)) hq]
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  calc (1 + |t - (j : ℝ) * c|) ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ 4 * (8 * (1 + |(j : ℝ)| ^ 4))) *
          Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hK)) hE
    _ = 8 * (1 + |t| + c) ^ 4 * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ 4 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring


theorem sp_major (ν t Pm C1 c : ℝ) (x : ℝ × ℝ) (n : ℤ) (ha1 : 1 ≤ ageA ν t)
    (hPm : ageA ν t ≤ Pm) (hc0 : 0 ≤ c) (hcC : c ≤ C1) (hC1 : 0 ≤ C1) :
    c * (1 + ‖xj ν n x‖) ^ 4 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) ≤
      C1 * (1 + |x.2|) ^ 4 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
  have hy := gp_one_add_norm ν n x
  have hR0 : 0 ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
  have hpow : (1 + ‖xj ν n x‖) ^ 4 ≤ (1 + |x.2|) ^ 4 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hR0 hy 4
  have hexp := sp_exp_le ν t Pm (xj ν n x) ha1 hPm
  have hxj : (xj ν n x).1 = x.1 - (n : ℝ) * cOf ν := rfl
  rw [hxj] at hexp
  have hE0 := (Real.exp_pos (-(sq2 (xj ν n x)) / (4 * ageA ν t))).le
  have s1 : c * (1 + ‖xj ν n x‖) ^ 4 ≤ C1 * ((1 + |x.2|) ^ 4 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4) :=
    mul_le_mul hcC hpow (pow_nonneg hR0 4) hC1
  calc c * (1 + ‖xj ν n x‖) ^ 4 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t))
      ≤ (C1 * ((1 + |x.2|) ^ 4 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4)) *
          Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul s1 hexp hE0 (mul_nonneg hC1 (by positivity))
    _ = C1 * (1 + |x.2|) ^ 4 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
          Real.exp (-(1 / (4 * Pm)) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by ring

theorem psipASDiff (as : ℝ) (χf : ℝ → ℝ) : PsipASDiff as χf := by
  unfold PsipASDiff
  intro hχ ν hν A hA s hs x
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
  have hC1nn : 0 ≤ 10 * ν * K1 + 8 * K2 + 8 * K1 := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hν.le) hK1nn
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK2nn
    have h3 := mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK1nn
    linarith
  have hu : Summable (fun n : ℤ => (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (sp_poly4_summable x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      ((10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4)
  have hbound : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      ‖sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ‖ ≤
        (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ hτ
    have hτJ : τ ∈ Icc (s / 2) (2 * s) := ⟨hτ.1.le, hτ.2.le⟩
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 := sV_bound ν hν (xj ν n x) K1 K2 (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ hτ0
      (hMb τ hτJ) (hDb τ hτJ)
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    have ha1τ : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν hτ0]
    exact sp_major ν τ (1 + ν * (2 * s)) (10 * ν * K1 + 8 * K2 + 8 * K1) (10 * ν * K1 + 8 * K2)
      x n ha1τ (hPm τ hτJ) (by nlinarith [mul_nonneg hν.le hK1nn, mul_nonneg hν.le hK2nn])
      (by linarith) hC1nn
  have hdiff : ∀ (n : ℤ) (τ : ℝ), τ ∈ Ioo (s / 2) (2 * s) →
      HasDerivAt (fun τ' => psiPhi ν τ' (Ay ν χf A τ') (xj ν n x))
        (sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ) τ := by
    intro n τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact sV_hasDerivAt ν hν (xj ν n x) (Ay ν χf A) (deriv (Ay ν χf A) τ) τ hτ0
      (hMd τ hτ0).hasDerivAt
  have hg0 : Summable (fun n : ℤ => psiPhi ν s (Ay ν χf A s) (xj ν n x)) := by
    refine Summable.of_norm_bounded hu (fun n => ?_)
    rw [Real.norm_eq_abs]
    have h1 := psiPhi_abs_le ν s ha1s (Ay ν χf A s) (xj ν n x)
    have hKm : 2 * Kmat (Ay ν χf A s) ≤ 8 * K1 := by
      unfold Kmat
      linarith [hMb s hsJ 0 0, hMb s hsJ 0 2, hMb s hsJ 2 0, hMb s hsJ 2 2]
    have hR1 : (1:ℝ) ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
    have hR3 : (1 + ‖xj ν n x‖) ^ 3 ≤ (1 + ‖xj ν n x‖) ^ 4 :=
      pow_le_pow_right₀ hR1 (by norm_num)
    have hE : 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    have hM := sp_major ν s (1 + ν * (2 * s)) (10 * ν * K1 + 8 * K2 + 8 * K1) (8 * K1) x n ha1s
      (hPm s hsJ) (by linarith)
      (by nlinarith [mul_nonneg hν.le hK1nn, mul_nonneg hν.le hK2nn]) hC1nn
    calc |psiPhi ν s (Ay ν χf A s) (xj ν n x)|
        ≤ 2 * Kmat (Ay ν χf A s) * ((1 + ‖xj ν n x‖) ^ 3 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := h1
      _ ≤ 8 * K1 * ((1 + ‖xj ν n x‖) ^ 3 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_right hKm (mul_nonneg (pow_nonneg (by linarith [norm_nonneg (xj ν n x)]) 3) hE)
      _ ≤ 8 * K1 * ((1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR3 hE) (by linarith)
      _ = 8 * K1 * (1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := by ring
      _ ≤ _ := hM
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun n τ => psiPhi ν τ (Ay ν χf A τ) (xj ν n x))
    (g' := fun n τ => sV ν (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) τ)
    (u := fun n : ℤ => (10 * ν * K1 + 8 * K2 + 8 * K1) * (1 + |x.2|) ^ 4 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 4 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n τ hτ => hdiff n τ hτ) (fun n τ hτ => hbound n τ hτ)
    ⟨by linarith, by linarith⟩ hg0 ⟨by linarith, by linarith⟩
  have hd : DifferentiableAt ℝ (fun τ => ∑' n : ℤ, psiPhi ν τ (Ay ν χf A τ) (xj ν n x)) s :=
    key.differentiableAt
  have hev : Filter.EventuallyEq (nhds s) (fun τ => psipA ν χf A τ x)
      (fun τ => ∑' n : ℤ, psiPhi ν τ (Ay ν χf A τ) (xj ν n x)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact psipA_eq_phi ν χf A τ x (by unfold ageA; nlinarith [mul_pos hν hτ0])
  exact hd.congr_of_eventuallyEq hev

end UnforcedLeray.Short.PartIIIb.Concrete
