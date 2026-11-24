import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2

/-!
# `PartIII-b:C/grad/2/6`: the second `s`-derivative of `ψ^p_A(s, x)` exists at `s > 0`

Source `the November 2 reference manuscript` lines 4973-4980 (`ψ^p_A = Σ_j Φ(x_j)`,
sums and `s`-derivatives converge by Gaussian decay), 4741-4745 (`A` is `C^6`).

Closed form of one lattice term: `Φ = E·A`, `E = exp(-|y|²/(4a))`, `a = 1+νs`, `u = a⁻¹`,
`A = -2u·T(M) - (u²/2)·Q_y(M)`, `T(M) = M₀₀+M₂₂`, `Q_y(M) = 2y·My`.
Its first `s`-derivative is `E·W·A + E·B`, its second is `E·((W²+W')A + 2WB + B')`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

def p2TT (M : Mat3) : ℝ := M 0 0 + M 2 2

def p2QQ (y : ℝ × ℝ) (M : Mat3) : ℝ :=
  2 * y.1 * (M 0 0 * y.1 + M 0 2 * y.2) + 2 * y.2 * (M 2 0 * y.1 + M 2 2 * y.2)

def p2U (ν t : ℝ) : ℝ := (ageA ν t)⁻¹

def p2E (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) : ℝ := Real.exp (-(sq2 y) / (4 * ageA ν t))

/-- `W = E'/E`. -/
def p2W (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) : ℝ := (ν * sq2 y) * (p2U ν t * p2U ν t) / 4

/-- `W'`. -/
def p2Wd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) : ℝ :=
  -(ν * ν * sq2 y) * (p2U ν t * p2U ν t * p2U ν t) / 2

/-- The bracket `A` of one lattice term. -/
def p2A (u T Q : ℝ) : ℝ := -2 * u * T + -(u * u) / 2 * Q

/-- `A'`. -/
def p2B (ν u T Q TD QD : ℝ) : ℝ :=
  2 * ν * (u * u) * T + ν * (u * u * u) * Q + -2 * u * TD + -(u * u) / 2 * QD

/-- `B'`. -/
def p2Bd (ν u T Q TD QD TDD QDD : ℝ) : ℝ :=
  -4 * ν ^ 2 * (u * u * u) * T + -3 * ν ^ 2 * (u * u * u * u) * Q
    + 2 * (2 * ν * (u * u)) * TD + 2 * (ν * (u * u * u)) * QD + -2 * u * TDD
    + -(u * u) / 2 * QDD

/-- First derivative of `E·A`. -/
def p2Phi1 (ν t : ℝ) (y : ℝ × ℝ) (M D : Mat3) : ℝ :=
  p2E ν y t * p2W ν y t * p2A (p2U ν t) (p2TT M) (p2QQ y M)
    + p2E ν y t * p2B ν (p2U ν t) (p2TT M) (p2QQ y M) (p2TT D) (p2QQ y D)

/-- Second derivative of `E·A`. -/
def p2Phi2 (ν t : ℝ) (y : ℝ × ℝ) (M D D2 : Mat3) : ℝ :=
  p2E ν y t * ((p2W ν y t * p2W ν y t + p2Wd ν y t) * p2A (p2U ν t) (p2TT M) (p2QQ y M)
    + 2 * p2W ν y t * p2B ν (p2U ν t) (p2TT M) (p2QQ y M) (p2TT D) (p2QQ y D)
    + p2Bd ν (p2U ν t) (p2TT M) (p2QQ y M) (p2TT D) (p2QQ y D) (p2TT D2) (p2QQ y D2))

theorem p2_psiPhi_eq (ν t : ℝ) (M : Mat3) (y : ℝ × ℝ) :
    psiPhi ν t M y = p2E ν y t * p2A (p2U ν t) (p2TT M) (p2QQ y M) := by
  by_cases ha : ageA ν t = 0
  · simp [psiPhi, p2E, p2A, p2U, p2TT, p2QQ, ha]
  · unfold psiPhi p2E p2A p2U p2TT p2QQ merTrace merApply
    dsimp only
    field_simp
    ring

theorem p2_TT_hd {F : ℝ → Mat3} {G : Mat3} {t : ℝ} (h : HasDerivAt F G t) :
    HasDerivAt (fun τ => p2TT (F τ)) (p2TT G) t := by
  unfold p2TT
  exact (sp_entry_hasDerivAt h 0 0).add (sp_entry_hasDerivAt h 2 2)

theorem p2_QQ_hd (y : ℝ × ℝ) {F : ℝ → Mat3} {G : Mat3} {t : ℝ} (h : HasDerivAt F G t) :
    HasDerivAt (fun τ => p2QQ y (F τ)) (p2QQ y G) t := by
  have h00 := sp_entry_hasDerivAt h 0 0
  have h02 := sp_entry_hasDerivAt h 0 2
  have h20 := sp_entry_hasDerivAt h 2 0
  have h22 := sp_entry_hasDerivAt h 2 2
  have H := (((h00.mul_const y.1).add (h02.mul_const y.2)).const_mul (2 * y.1)).add
    (((h20.mul_const y.1).add (h22.mul_const y.2)).const_mul (2 * y.2))
  unfold p2QQ
  exact H.congr_deriv (by ring)

theorem p2_U_hd (ν t : ℝ) (ht : 0 < t) (hν : 0 < ν) :
    HasDerivAt (fun τ => p2U ν τ) (-ν * (p2U ν t * p2U ν t)) t := by
  have ha : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
  have hA : HasDerivAt (fun τ => ageA ν τ) ν t := by
    unfold ageA
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have H := hA.inv ha.ne'
  unfold p2U
  exact H.congr_deriv (by ring)

theorem p2_E_hd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    HasDerivAt (fun τ => p2E ν y τ) (p2E ν y t * p2W ν y t) t := by
  have ha : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht]
  have hA : HasDerivAt (fun τ => ageA ν τ) ν t := by
    unfold ageA
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have hne : 4 * ageA ν t ≠ 0 := (by linarith : (0:ℝ) < 4 * ageA ν t).ne'
  have hg : HasDerivAt (fun τ => -(sq2 y) / (4 * ageA ν τ))
      ((0 * (4 * ageA ν t) - (-(sq2 y)) * (4 * ν)) / (4 * ageA ν t) ^ 2) t :=
    (hasDerivAt_const t (-(sq2 y))).div (hA.const_mul 4) hne
  have H := hg.exp
  unfold p2E p2W p2U
  refine H.congr_deriv ?_
  have ha0 : ageA ν t ≠ 0 := ha.ne'
  congr 1
  field_simp
  ring

theorem p2_W_hd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    HasDerivAt (fun τ => p2W ν y τ) (p2Wd ν y t) t := by
  have hU := p2_U_hd ν t ht hν
  have H := ((hU.mul hU).const_mul (ν * sq2 y)).div_const 4
  unfold p2W p2Wd
  refine H.congr_deriv ?_
  (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply])
  ring

theorem p2_A_hd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 < ν) (ht : 0 < t) {M : ℝ → Mat3}
    {D : Mat3} (hM : HasDerivAt M D t) :
    HasDerivAt (fun τ => p2A (p2U ν τ) (p2TT (M τ)) (p2QQ y (M τ)))
      (p2B ν (p2U ν t) (p2TT (M t)) (p2QQ y (M t)) (p2TT D) (p2QQ y D)) t := by
  have hU := p2_U_hd ν t ht hν
  have hT := p2_TT_hd hM
  have hQ := p2_QQ_hd y hM
  have H := ((hU.const_mul (-2)).mul hT).add ((((hU.mul hU).neg).div_const 2).mul hQ)
  unfold p2A p2B
  refine H.congr_deriv ?_
  (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply])
  ring

theorem p2_B_hd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 < ν) (ht : 0 < t) {M D : ℝ → Mat3}
    {D2 : Mat3} (hM : HasDerivAt M (D t) t) (hD : HasDerivAt D D2 t) :
    HasDerivAt (fun τ => p2B ν (p2U ν τ) (p2TT (M τ)) (p2QQ y (M τ)) (p2TT (D τ)) (p2QQ y (D τ)))
      (p2Bd ν (p2U ν t) (p2TT (M t)) (p2QQ y (M t)) (p2TT (D t)) (p2QQ y (D t)) (p2TT D2)
        (p2QQ y D2)) t := by
  have hU := p2_U_hd ν t ht hν
  have hT := p2_TT_hd hM
  have hQ := p2_QQ_hd y hM
  have hTD := p2_TT_hd hD
  have hQD := p2_QQ_hd y hD
  have H := ((((hU.mul hU).const_mul (2 * ν)).mul hT).add
      ((((hU.mul hU).mul hU).const_mul ν).mul hQ)).add ((hU.const_mul (-2)).mul hTD) |>.add
      ((((hU.mul hU).neg).div_const 2).mul hQD)
  unfold p2B p2Bd
  refine H.congr_deriv ?_
  (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply])
  ring

theorem p2_L1 (ν t : ℝ) (y : ℝ × ℝ) (hν : 0 < ν) (ht : 0 < t) {M : ℝ → Mat3} {D : Mat3}
    (hM : HasDerivAt M D t) :
    HasDerivAt (fun τ => p2E ν y τ * p2A (p2U ν τ) (p2TT (M τ)) (p2QQ y (M τ)))
      (p2Phi1 ν t y (M t) D) t :=
  (p2_E_hd ν y t hν ht).mul (p2_A_hd ν y t hν ht hM)

theorem p2_L2 (ν t : ℝ) (y : ℝ × ℝ) (hν : 0 < ν) (ht : 0 < t) {M D : ℝ → Mat3} {D2 : Mat3}
    (hM : HasDerivAt M (D t) t) (hD : HasDerivAt D D2 t) :
    HasDerivAt (fun τ => p2Phi1 ν τ y (M τ) (D τ)) (p2Phi2 ν t y (M t) (D t) D2) t := by
  have hE := p2_E_hd ν y t hν ht
  have hW := p2_W_hd ν y t hν ht
  have hA := p2_A_hd ν y t hν ht hM
  have hB := p2_B_hd ν y t hν ht hM hD
  have H := ((hE.mul hW).mul hA).add (hE.mul hB)
  unfold p2Phi2 p2Phi1
  refine H.congr_deriv ?_
  (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, Pi.div_apply])
  ring

theorem p2_absmul {a b c d : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ d) (hc : 0 ≤ c) : |a * b| ≤ c * d := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hc

theorem p2_sq_le (y : ℝ × ℝ) : sq2 y ≤ 2 * ‖y‖ ^ 2 := by
  have e1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y.1) (abs_fst_le' y) 2
    rwa [sq_abs] at this
  have e2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y.2) (abs_snd_le' y) 2
    rwa [sq_abs] at this
  unfold sq2
  linarith

theorem p2_A_bd (u T Q K1 r : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hK1 : 0 ≤ K1)
    (hT : |T| ≤ 2 * K1) (hQ : |Q| ≤ 8 * K1 * r ^ 2) :
    |p2A u T Q| ≤ 4 * K1 * (1 + r ^ 2) := by
  unfold p2A
  have hu2 : u * u ≤ 1 := by nlinarith
  have hu2' : 0 ≤ u * u := mul_nonneg hu0 hu0
  have ha : |-2 * u| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |-(u * u) / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have t1 := abs_add_le (-2 * u * T) (-(u * u) / 2 * Q)
  have e1 := p2_absmul ha hT (by norm_num : (0:ℝ) ≤ 2)
  have e2 := p2_absmul hb hQ (by norm_num : (0:ℝ) ≤ 1 / 2)
  linarith

theorem p2_B_bd (ν u T Q TD QD K1 K2 r : ℝ) (hν : 0 ≤ ν) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hT : |T| ≤ 2 * K1) (hQ : |Q| ≤ 8 * K1 * r ^ 2)
    (hTD : |TD| ≤ 2 * K2) (hQD : |QD| ≤ 8 * K2 * r ^ 2) :
    |p2B ν u T Q TD QD| ≤ 4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2 := by
  unfold p2B
  have hu2 : u * u ≤ 1 := by nlinarith
  have hu2' : 0 ≤ u * u := mul_nonneg hu0 hu0
  have hu3 : u * u * u ≤ 1 := by nlinarith
  have hu3' : 0 ≤ u * u * u := mul_nonneg hu2' hu0
  have c1 : |2 * ν * (u * u)| ≤ 2 * ν :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg hν hu2'], by nlinarith [mul_nonneg hν (sub_nonneg.2 hu2)]⟩
  have c2 : |ν * (u * u * u)| ≤ ν :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg hν hu3'], by nlinarith [mul_nonneg hν (sub_nonneg.2 hu3)]⟩
  have c3 : |-2 * u| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have c4 : |-(u * u) / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have e1 := p2_absmul c1 hT (by linarith : (0:ℝ) ≤ 2 * ν)
  have e2 := p2_absmul c2 hQ hν
  have e3 := p2_absmul c3 hTD (by norm_num : (0:ℝ) ≤ 2)
  have e4 := p2_absmul c4 hQD (by norm_num : (0:ℝ) ≤ 1 / 2)
  have t1 := abs_add_le (2 * ν * (u * u) * T + ν * (u * u * u) * Q + -2 * u * TD) (-(u * u) / 2 * QD)
  have t2 := abs_add_le (2 * ν * (u * u) * T + ν * (u * u * u) * Q) (-2 * u * TD)
  have t3 := abs_add_le (2 * ν * (u * u) * T) (ν * (u * u * u) * Q)
  linarith

theorem p2_Bd_bd (ν u T Q TD QD TDD QDD K1 K2 K3 r : ℝ) (hν : 0 ≤ ν) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hT : |T| ≤ 2 * K1) (hQ : |Q| ≤ 8 * K1 * r ^ 2) (hTD : |TD| ≤ 2 * K2)
    (hQD : |QD| ≤ 8 * K2 * r ^ 2) (hTDD : |TDD| ≤ 2 * K3) (hQDD : |QDD| ≤ 8 * K3 * r ^ 2) :
    |p2Bd ν u T Q TD QD TDD QDD| ≤
      8 * ν ^ 2 * K1 + 24 * ν ^ 2 * K1 * r ^ 2 + 8 * ν * K2 + 16 * ν * K2 * r ^ 2
        + 4 * K3 + 4 * K3 * r ^ 2 := by
  unfold p2Bd
  have hu2 : u * u ≤ 1 := by nlinarith
  have hu2' : 0 ≤ u * u := mul_nonneg hu0 hu0
  have hu3 : u * u * u ≤ 1 := by nlinarith
  have hu3' : 0 ≤ u * u * u := mul_nonneg hu2' hu0
  have hu4 : u * u * u * u ≤ 1 := by nlinarith
  have hu4' : 0 ≤ u * u * u * u := mul_nonneg hu3' hu0
  have c1 : |-4 * ν ^ 2 * (u * u * u)| ≤ 4 * ν ^ 2 :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg (sq_nonneg ν) (sub_nonneg.2 hu3)],
      by nlinarith [mul_nonneg (sq_nonneg ν) hu3']⟩
  have c2 : |-3 * ν ^ 2 * (u * u * u * u)| ≤ 3 * ν ^ 2 :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg (sq_nonneg ν) (sub_nonneg.2 hu4)],
      by nlinarith [mul_nonneg (sq_nonneg ν) hu4']⟩
  have c3 : |2 * (2 * ν * (u * u))| ≤ 4 * ν :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg hν hu2'], by nlinarith [mul_nonneg hν (sub_nonneg.2 hu2)]⟩
  have c4 : |2 * (ν * (u * u * u))| ≤ 2 * ν :=
    abs_le.mpr ⟨by nlinarith [mul_nonneg hν hu3'], by nlinarith [mul_nonneg hν (sub_nonneg.2 hu3)]⟩
  have c5 : |-2 * u| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have c6 : |-(u * u) / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have e1 := p2_absmul c1 hT (by positivity : (0:ℝ) ≤ 4 * ν ^ 2)
  have e2 := p2_absmul c2 hQ (by positivity : (0:ℝ) ≤ 3 * ν ^ 2)
  have e3 := p2_absmul c3 hTD (by linarith : (0:ℝ) ≤ 4 * ν)
  have e4 := p2_absmul c4 hQD (by linarith : (0:ℝ) ≤ 2 * ν)
  have e5 := p2_absmul c5 hTDD (by norm_num : (0:ℝ) ≤ 2)
  have e6 := p2_absmul c6 hQDD (by norm_num : (0:ℝ) ≤ 1 / 2)
  have s5 := abs_add_le (-4 * ν ^ 2 * (u * u * u) * T + -3 * ν ^ 2 * (u * u * u * u) * Q
    + 2 * (2 * ν * (u * u)) * TD + 2 * (ν * (u * u * u)) * QD + -2 * u * TDD) (-(u * u) / 2 * QDD)
  have s4 := abs_add_le (-4 * ν ^ 2 * (u * u * u) * T + -3 * ν ^ 2 * (u * u * u * u) * Q
    + 2 * (2 * ν * (u * u)) * TD + 2 * (ν * (u * u * u)) * QD) (-2 * u * TDD)
  have s3 := abs_add_le (-4 * ν ^ 2 * (u * u * u) * T + -3 * ν ^ 2 * (u * u * u * u) * Q
    + 2 * (2 * ν * (u * u)) * TD) (2 * (ν * (u * u * u)) * QD)
  have s2 := abs_add_le (-4 * ν ^ 2 * (u * u * u) * T + -3 * ν ^ 2 * (u * u * u * u) * Q)
    (2 * (2 * ν * (u * u)) * TD)
  have s1 := abs_add_le (-4 * ν ^ 2 * (u * u * u) * T) (-3 * ν ^ 2 * (u * u * u * u) * Q)
  linarith

theorem p2_W_bd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 ≤ ν) (ha1 : 1 ≤ ageA ν t) :
    0 ≤ p2W ν y t ∧ p2W ν y t ≤ ν * ‖y‖ ^ 2 / 2 := by
  unfold p2W p2U
  have hsq0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hcR := p2_sq_le y
  have hu0 : 0 ≤ (ageA ν t)⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have huu0 : 0 ≤ (ageA ν t)⁻¹ * (ageA ν t)⁻¹ := mul_nonneg hu0 hu0
  have huu1 : (ageA ν t)⁻¹ * (ageA ν t)⁻¹ ≤ 1 := by nlinarith
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg hν hsq0) huu0) (by norm_num)
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [mul_nonneg (mul_nonneg hν hsq0) (sub_nonneg.2 huu1), mul_le_mul_of_nonneg_left hcR hν]

theorem p2_Wd_bd (ν : ℝ) (y : ℝ × ℝ) (t : ℝ) (hν : 0 ≤ ν) (ha1 : 1 ≤ ageA ν t) :
    |p2Wd ν y t| ≤ ν ^ 2 * ‖y‖ ^ 2 := by
  unfold p2Wd p2U
  have hsq0 : 0 ≤ sq2 y := by unfold sq2; positivity
  have hcR := p2_sq_le y
  have hu0 : 0 ≤ (ageA ν t)⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : (ageA ν t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  have huu0 : 0 ≤ (ageA ν t)⁻¹ * (ageA ν t)⁻¹ := mul_nonneg hu0 hu0
  have huuu0 : 0 ≤ (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹ := mul_nonneg huu0 hu0
  have huuu1 : (ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹ ≤ 1 := by nlinarith
  have h0 : 0 ≤ ν * ν * sq2 y * ((ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹) :=
    mul_nonneg (mul_nonneg (mul_nonneg hν hν) hsq0) huuu0
  have h1 : ν * ν * sq2 y * ((ageA ν t)⁻¹ * (ageA ν t)⁻¹ * (ageA ν t)⁻¹)
      ≤ ν * ν * sq2 y := mul_le_of_le_one_right (mul_nonneg (mul_nonneg hν hν) hsq0) huuu1
  have h2 : ν * ν * sq2 y ≤ ν * ν * (2 * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left hcR (mul_nonneg hν hν)
  rw [abs_le]
  constructor <;> nlinarith

theorem p2_dom (C0 ν s t : ℝ) (hC0 : 0 ≤ C0) (ha1 : 1 ≤ ageA ν t)
    (hPm : ageA ν t ≤ 1 + ν * (2 * s)) (x : ℝ × ℝ) (n : ℤ) :
    Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) * (C0 * (1 + ‖xj ν n x‖) ^ 6)
      ≤ C0 * (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
  have hE := sp_exp_le ν t (1 + ν * (2 * s)) (xj ν n x) ha1 hPm
  have hxj : (xj ν n x).1 = x.1 - (n : ℝ) * cOf ν := rfl
  rw [hxj] at hE
  have hp : (1 + ‖xj ν n x‖) ^ 6 ≤ (1 + |x.2|) ^ 6 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [norm_nonneg (xj ν n x)]) (gp_one_add_norm ν n x) 6
  calc Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν t)) * (C0 * (1 + ‖xj ν n x‖) ^ 6)
      ≤ Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2) *
          (C0 * ((1 + |x.2|) ^ 6 * (1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6)) :=
        mul_le_mul hE (mul_le_mul_of_nonneg_left hp hC0) (mul_nonneg hC0 (by positivity))
          (Real.exp_pos _).le
    _ = C0 * (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by ring

theorem p2_polyk_summable (k : ℕ) (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |t - (j : ℝ) * c|) ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have h0 := gp_gauss_summable t α c hα hc
  have hk := gp_gauss_pow_summable t α c hα hc k
  have hK : (0:ℝ) ≤ (1 + |t| + c) ^ k := pow_nonneg (by linarith [abs_nonneg t]) k
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((h0.add hk).mul_left (2 ^ (k - 1) * (1 + |t| + c) ^ k))
  have hz : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hu : 1 + |t - (j : ℝ) * c| ≤ (1 + |t| + c) * (1 + |(j : ℝ)|) := by
    have h1 : |t - (j : ℝ) * c| ≤ |t| + |(j : ℝ)| * c := by
      have h2 := abs_sub t ((j : ℝ) * c)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg t, mul_nonneg hz hc.le, mul_nonneg (abs_nonneg t) hz]
  have h1 : (1 + |t - (j : ℝ) * c|) ^ k ≤ (1 + |t| + c) ^ k * (1 + |(j : ℝ)|) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu k
  have h2 : (1 + |(j : ℝ)|) ^ k ≤ 2 ^ (k - 1) * (1 + |(j : ℝ)| ^ k) := by
    have := add_pow_le (by norm_num : (0:ℝ) ≤ 1) hz k
    simpa only [one_pow] using this
  have hE : 0 ≤ Real.exp (-α * (t - (j : ℝ) * c) ^ 2) := (Real.exp_pos _).le
  calc (1 + |t - (j : ℝ) * c|) ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
      ≤ ((1 + |t| + c) ^ k * (1 + |(j : ℝ)|) ^ k) * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ ≤ ((1 + |t| + c) ^ k * (2 ^ (k - 1) * (1 + |(j : ℝ)| ^ k)))
          * Real.exp (-α * (t - (j : ℝ) * c) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK) hE
    _ = 2 ^ (k - 1) * (1 + |t| + c) ^ k * (Real.exp (-α * (t - (j : ℝ) * c) ^ 2)
          + |(j : ℝ)| ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by ring

theorem p2_L0_bd (E A ν r K1 K2 K3 : ℝ) (hE : 0 ≤ E) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hν : 0 ≤ ν) (hr : 0 ≤ r) (hA : |A| ≤ 4 * K1 * (1 + r ^ 2)) :
    |E * A| ≤ E * (60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6) := by
  rw [abs_mul, abs_of_nonneg hE]
  have hP0 : 0 ≤ (1 + r) ^ 6 := pow_nonneg (by linarith) 6
  have hr2 : r ^ 2 ≤ (1 + r) ^ 6 :=
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) 2).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) (by norm_num))
  have h1P : (1:ℝ) ≤ (1 + r) ^ 6 := one_le_pow₀ (by linarith)
  have hC8 : 8 * K1 ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) := by
    nlinarith [mul_nonneg hν hK1, mul_nonneg hν hK2, mul_nonneg hν hK3,
      mul_nonneg (mul_nonneg hν hν) hK1, mul_nonneg (mul_nonneg hν hν) hK2,
      mul_nonneg (mul_nonneg hν hν) hK3]
  have key : 4 * K1 * (1 + r ^ 2) ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hr2 hK1, mul_le_mul_of_nonneg_left h1P hK1,
      mul_le_mul_of_nonneg_right hC8 hP0]
  exact (mul_le_mul_of_nonneg_left hA hE).trans (mul_le_mul_of_nonneg_left key hE)

theorem p2_L1_bd (E W A B ν r K1 K2 K3 : ℝ) (hE : 0 ≤ E) (hW0 : 0 ≤ W)
    (hWle : W ≤ ν * r ^ 2 / 2) (hν : 0 ≤ ν) (hr : 0 ≤ r) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hA : |A| ≤ 4 * K1 * (1 + r ^ 2))
    (hB : |B| ≤ 4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2) :
    |E * W * A + E * B| ≤ E * (60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6) := by
  have t := abs_add_le (E * W * A) (E * B)
  have e1 : |E * W * A| = E * W * |A| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hE, abs_of_nonneg hW0]
  have e2 : |E * B| = E * |B| := by rw [abs_mul, abs_of_nonneg hE]
  have h1 : E * W * |A| ≤ E * (ν * r ^ 2 / 2) * (4 * K1 * (1 + r ^ 2)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hWle hE) hA (abs_nonneg _)
      (mul_nonneg hE (div_nonneg (mul_nonneg hν (sq_nonneg r)) (by norm_num)))
  have h2 : E * |B| ≤ E * (4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2) :=
    mul_le_mul_of_nonneg_left hB hE
  have hP0 : 0 ≤ (1 + r) ^ 6 := pow_nonneg (by linarith) 6
  have hr2 : r ^ 2 ≤ (1 + r) ^ 6 :=
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) 2).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) (by norm_num))
  have hr4 : r ^ 4 ≤ (1 + r) ^ 6 :=
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) 4).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) (by norm_num))
  have h1P : (1:ℝ) ≤ (1 + r) ^ 6 := one_le_pow₀ (by linarith)
  have hC : 16 * ν * K1 + 8 * K2 ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) := by
    nlinarith [mul_nonneg hν hK1, mul_nonneg hν hK2, mul_nonneg hν hK3,
      mul_nonneg (mul_nonneg hν hν) hK1, mul_nonneg (mul_nonneg hν hν) hK2,
      mul_nonneg (mul_nonneg hν hν) hK3]
  have key : (ν * r ^ 2 / 2) * (4 * K1 * (1 + r ^ 2))
      + (4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2)
      ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hr4 (mul_nonneg hν hK1),
      mul_le_mul_of_nonneg_left hr2 (mul_nonneg hν hK1),
      mul_le_mul_of_nonneg_left h1P (mul_nonneg hν hK1),
      mul_le_mul_of_nonneg_left hr2 hK2, mul_le_mul_of_nonneg_left h1P hK2,
      mul_le_mul_of_nonneg_right hC hP0]
  have key2 := mul_le_mul_of_nonneg_left key hE
  nlinarith [t, e1, e2, h1, h2, key2]

theorem p2_L2_bd (E W Wd A B Bd ν r K1 K2 K3 : ℝ) (hE : 0 ≤ E) (hW0 : 0 ≤ W)
    (hWle : W ≤ ν * r ^ 2 / 2) (hWd : |Wd| ≤ ν ^ 2 * r ^ 2) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hA : |A| ≤ 4 * K1 * (1 + r ^ 2))
    (hB : |B| ≤ 4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2)
    (hBd : |Bd| ≤ 8 * ν ^ 2 * K1 + 24 * ν ^ 2 * K1 * r ^ 2 + 8 * ν * K2 + 16 * ν * K2 * r ^ 2
        + 4 * K3 + 4 * K3 * r ^ 2) :
    |E * ((W * W + Wd) * A + 2 * W * B + Bd)|
      ≤ E * (60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6) := by
  have hνr : 0 ≤ ν * r ^ 2 := mul_nonneg hν (sq_nonneg r)
  have hWW : |W * W + Wd| ≤ ν ^ 2 * r ^ 4 / 4 + ν ^ 2 * r ^ 2 := by
    have h1 : 0 ≤ W * W := mul_nonneg hW0 hW0
    have h2 : W * W ≤ (ν * r ^ 2 / 2) * (ν * r ^ 2 / 2) :=
      mul_le_mul hWle hWle hW0 (div_nonneg hνr (by norm_num))
    have h3 := abs_add_le (W * W) Wd
    rw [abs_of_nonneg h1] at h3
    nlinarith
  have hX : |(W * W + Wd) * A + 2 * W * B + Bd|
      ≤ (ν ^ 2 * r ^ 4 / 4 + ν ^ 2 * r ^ 2) * (4 * K1 * (1 + r ^ 2))
        + ν * r ^ 2 * (4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2)
        + (8 * ν ^ 2 * K1 + 24 * ν ^ 2 * K1 * r ^ 2 + 8 * ν * K2 + 16 * ν * K2 * r ^ 2
          + 4 * K3 + 4 * K3 * r ^ 2) := by
    have t1 := abs_add_le ((W * W + Wd) * A + 2 * W * B) Bd
    have t2 := abs_add_le ((W * W + Wd) * A) (2 * W * B)
    have e1 := p2_absmul hWW hA (by positivity)
    have hW2 : |2 * W| ≤ ν * r ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e2 := p2_absmul hW2 hB hνr
    linarith
  have hP0 : 0 ≤ (1 + r) ^ 6 := pow_nonneg (by linarith) 6
  have hPk : ∀ k : ℕ, k ≤ 6 → r ^ k ≤ (1 + r) ^ 6 := fun k hk =>
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) k).trans
      (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + r) hk)
  have r6 := hPk 6 (by norm_num)
  have r4 := hPk 4 (by norm_num)
  have r2 := hPk 2 (by norm_num)
  have h1P : (1:ℝ) ≤ (1 + r) ^ 6 := one_le_pow₀ (by linarith)
  have hC : 54 * ν ^ 2 * K1 + 32 * ν * K2 + 8 * K3 ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) := by
    nlinarith [mul_nonneg hν hK1, mul_nonneg hν hK2, mul_nonneg hν hK3,
      mul_nonneg (mul_nonneg hν hν) hK1, mul_nonneg (mul_nonneg hν hν) hK2,
      mul_nonneg (mul_nonneg hν hν) hK3]
  have key : (ν ^ 2 * r ^ 4 / 4 + ν ^ 2 * r ^ 2) * (4 * K1 * (1 + r ^ 2))
        + ν * r ^ 2 * (4 * ν * K1 + 8 * ν * K1 * r ^ 2 + 4 * K2 + 4 * K2 * r ^ 2)
        + (8 * ν ^ 2 * K1 + 24 * ν ^ 2 * K1 * r ^ 2 + 8 * ν * K2 + 16 * ν * K2 * r ^ 2
          + 4 * K3 + 4 * K3 * r ^ 2)
      ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + r) ^ 6 := by
    have a1 : 0 ≤ ν ^ 2 * K1 := mul_nonneg (sq_nonneg ν) hK1
    have a2 : 0 ≤ ν * K2 := mul_nonneg hν hK2
    nlinarith [mul_le_mul_of_nonneg_left r6 a1, mul_le_mul_of_nonneg_left r4 a1,
      mul_le_mul_of_nonneg_left r2 a1, mul_le_mul_of_nonneg_left h1P a1,
      mul_le_mul_of_nonneg_left r4 a2, mul_le_mul_of_nonneg_left r2 a2,
      mul_le_mul_of_nonneg_left h1P a2, mul_le_mul_of_nonneg_left r2 hK3,
      mul_le_mul_of_nonneg_left h1P hK3, mul_le_mul_of_nonneg_right hC hP0]
  rw [abs_mul, abs_of_nonneg hE]
  exact (mul_le_mul_of_nonneg_left hX hE).trans (mul_le_mul_of_nonneg_left key hE)

theorem psipASSecond (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipASSecond as χf := by
  unfold PsipASSecond
  intro ν hν A hA s hs x
  have hν0 : 0 ≤ ν := hν.le
  have hMd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (Ay ν χf A) t :=
    fun t ht => ayDiffAt as χf hχ ν A hA t ht
  have hC3 : ContDiffOn ℝ 3 (Ay ν χf A) (Ioi 0) := by
    have hc : ContDiffOn ℝ 3 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
      ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffOn).of_le (by norm_num)
    have ha : ContDiffOn ℝ 3 A (Ioi 0) := hA.smooth.of_le (by norm_num)
    unfold Ay
    exact hc.smul ha
  have hC2D : ContDiffOn ℝ 2 (deriv (Ay ν χf A)) (Ioi 0) :=
    hC3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDD : ContinuousOn (deriv (deriv (Ay ν χf A))) (Ioi 0) :=
    hC2D.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDDif : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (deriv (Ay ν χf A)) t := fun t ht =>
    (hC2D.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds ht)
  have hJ : ∀ t ∈ Icc (s / 2) (2 * s), 0 < t := fun t ht => by linarith [ht.1]
  have hsJ : s ∈ Icc (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := Ay ν χf A) (fun t ht => (hMd t (hJ t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (Ay ν χf A)) (fun t ht => (hDDif t (hJ t ht)).continuousAt.continuousWithinAt)
  obtain ⟨K3, hK3⟩ := (isCompact_Icc (a := s / 2) (b := 2 * s)).exists_bound_of_continuousOn
    (f := deriv (deriv (Ay ν χf A))) (hDD.mono (fun t ht => hJ t ht))
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 s hsJ)
  have hK2nn : 0 ≤ K2 := (norm_nonneg _).trans (hK2 s hsJ)
  have hK3nn : 0 ≤ K3 := (norm_nonneg _).trans (hK3 s hsJ)
  have hMb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |Ay ν χf A t i j| ≤ K1 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK1 t ht)
  have hDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (Ay ν χf A) t i j| ≤ K2 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK2 t ht)
  have hDDb : ∀ t ∈ Icc (s / 2) (2 * s), ∀ i j, |deriv (deriv (Ay ν χf A)) t i j| ≤ K3 :=
    fun t ht i j => (sp_entry_le _ i j).trans (hK3 t ht)
  have hPm : ∀ t ∈ Icc (s / 2) (2 * s), ageA ν t ≤ 1 + ν * (2 * s) := by
    intro t ht
    unfold ageA
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hν0]
  have hα : 0 < 1 / (4 * (1 + ν * (2 * s))) := by
    have := mul_pos hν hs
    exact div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hC0 : 0 ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) :=
    mul_nonneg (by positivity) (by linarith)
  have hsum : Summable (fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
      ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
        Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2))) :=
    (p2_polyk_summable 6 x.1 (1 / (4 * (1 + ν * (2 * s)))) (cOf ν) hα hc).mul_left
      (60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6)
  -- bounds on the three levels
  have hL0 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      |p2E ν (xj ν n x) τ * p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))|
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hL := p2_L0_bd (p2E ν (xj ν n x) τ) _ ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hK1nn
      hK2nn hK3nn hν0 (norm_nonneg _) hA'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  have hL1 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      ‖p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)‖
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    rw [Real.norm_eq_abs]
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDb : |p2TT (deriv (Ay ν χf A) τ)| ≤ 2 * K2 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDb τ ht 0 0, hDb τ ht 2 2])
    have hQDb : |p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)| ≤ 8 * K2 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K2 _ hK2nn (norm_nonneg _) (hDb τ ht 0 0) (hDb τ ht 0 2)
        (hDb τ ht 2 0) (hDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hB' := p2_B_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)) K1 K2
      ‖xj ν n x‖ hν0 hu0 hu1 hK1nn hK2nn hTb hQb hTDb hQDb
    obtain ⟨hW0, hWle⟩ := p2_W_bd ν (xj ν n x) τ hν0 ha1
    have hL := p2_L1_bd (p2E ν (xj ν n x) τ) (p2W ν (xj ν n x) τ)
      (p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)))
      (p2B ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)))
      ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hW0 hWle hν0 (norm_nonneg _) hK1nn hK2nn hK3nn
      hA' hB'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  have hL2 : ∀ (n : ℤ) (τ : ℝ), τ ∈ Icc (s / 2) (2 * s) →
      ‖p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ) (deriv (deriv (Ay ν χf A)) τ)‖
        ≤ 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) * (1 + |x.2|) ^ 6 *
          ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
            Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)) := by
    intro n τ ht
    rw [Real.norm_eq_abs]
    have ht0 := hJ τ ht
    have ha1 : 1 ≤ ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht0]
    have hu0 : 0 ≤ p2U ν τ := by unfold p2U; exact inv_nonneg.mpr (by linarith)
    have hu1 : p2U ν τ ≤ 1 := by unfold p2U; exact inv_le_one_of_one_le₀ ha1
    have hTb : |p2TT (Ay ν χf A τ)| ≤ 2 * K1 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hMb τ ht 0 0, hMb τ ht 2 2])
    have hQb : |p2QQ (xj ν n x) (Ay ν χf A τ)| ≤ 8 * K1 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K1 _ hK1nn (norm_nonneg _) (hMb τ ht 0 0) (hMb τ ht 0 2)
        (hMb τ ht 2 0) (hMb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDb : |p2TT (deriv (Ay ν χf A) τ)| ≤ 2 * K2 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDb τ ht 0 0, hDb τ ht 2 2])
    have hQDb : |p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)| ≤ 8 * K2 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K2 _ hK2nn (norm_nonneg _) (hDb τ ht 0 0) (hDb τ ht 0 2)
        (hDb τ ht 2 0) (hDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hTDDb : |p2TT (deriv (deriv (Ay ν χf A)) τ)| ≤ 2 * K3 := by
      unfold p2TT
      exact (abs_add_le _ _).trans (by linarith [hDDb τ ht 0 0, hDDb τ ht 2 2])
    have hQDDb : |p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ)| ≤ 8 * K3 * ‖xj ν n x‖ ^ 2 := by
      unfold p2QQ
      exact sp_Q_bound _ _ _ _ _ _ K3 _ hK3nn (norm_nonneg _) (hDDb τ ht 0 0) (hDDb τ ht 0 2)
        (hDDb τ ht 2 0) (hDDb τ ht 2 2) (abs_fst_le' _) (abs_snd_le' _)
    have hA' := p2_A_bd (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) K1
      ‖xj ν n x‖ hu0 hu1 hK1nn hTb hQb
    have hB' := p2_B_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)) K1 K2
      ‖xj ν n x‖ hν0 hu0 hu1 hK1nn hK2nn hTb hQb hTDb hQDb
    have hBd' := p2_Bd_bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
      (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ))
      (p2TT (deriv (deriv (Ay ν χf A)) τ)) (p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ))
      K1 K2 K3 ‖xj ν n x‖ hν0 hu0 hu1 hTb hQb hTDb hQDb hTDDb hQDDb
    obtain ⟨hW0, hWle⟩ := p2_W_bd ν (xj ν n x) τ hν0 ha1
    have hWd := p2_Wd_bd ν (xj ν n x) τ hν0 ha1
    have hL := p2_L2_bd (p2E ν (xj ν n x) τ) (p2W ν (xj ν n x) τ) (p2Wd ν (xj ν n x) τ)
      (p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)))
      (p2B ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ)))
      (p2Bd ν (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ))
        (p2TT (deriv (Ay ν χf A) τ)) (p2QQ (xj ν n x) (deriv (Ay ν χf A) τ))
        (p2TT (deriv (deriv (Ay ν χf A)) τ)) (p2QQ (xj ν n x) (deriv (deriv (Ay ν χf A)) τ)))
      ν ‖xj ν n x‖ K1 K2 K3 (Real.exp_pos _).le hW0 hWle hWd hν0 (norm_nonneg _) hK1nn hK2nn
      hK3nn hA' hB' hBd'
    exact hL.trans (p2_dom _ ν s τ hC0 ha1 (hPm τ ht) x n)
  -- derivative pieces
  have hD1 : ∀ (n : ℤ) (τ : ℝ), 0 < τ →
      HasDerivAt (fun σ => p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
          (p2QQ (xj ν n x) (Ay ν χf A σ)))
        (p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)) τ :=
    fun n τ ht => p2_L1 ν τ (xj ν n x) hν ht ((hMd τ ht).hasDerivAt)
  have hD2 : ∀ (n : ℤ) (τ : ℝ), 0 < τ →
      HasDerivAt (fun σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
        (p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
          (deriv (deriv (Ay ν χf A)) τ)) τ :=
    fun n τ ht => p2_L2 ν τ (xj ν n x) hν ht ((hMd τ ht).hasDerivAt) ((hDDif τ ht).hasDerivAt)
  have hsP : ∀ τ : ℝ, 0 < τ → psipA ν χf A τ x = ∑' n : ℤ,
      p2E ν (xj ν n x) τ * p2A (p2U ν τ) (p2TT (Ay ν χf A τ)) (p2QQ (xj ν n x) (Ay ν χf A τ)) := by
    intro τ ht
    have ha : 0 < ageA ν τ := by unfold ageA; nlinarith [mul_pos hν ht]
    rw [psipA_eq_phi ν χf A τ x ha]
    exact tsum_congr fun n => p2_psiPhi_eq ν τ (Ay ν χf A τ) (xj ν n x)
  -- first derivative of the sum
  have hg0A : Summable (fun n : ℤ => p2E ν (xj ν n x) s * p2A (p2U ν s) (p2TT (Ay ν χf A s))
      (p2QQ (xj ν n x) (Ay ν χf A s))) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hL0 n s hsJ)
  have keyA : ∀ τ ∈ Ioo (s / 2) (2 * s), HasDerivAt
      (fun σ => ∑' n : ℤ, p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
        (p2QQ (xj ν n x) (Ay ν χf A σ)))
      (∑' n : ℤ, p2Phi1 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)) τ := fun τ hτ =>
    hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) *
        (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
      (g := fun n σ => p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ))
        (p2QQ (xj ν n x) (Ay ν χf A σ)))
      (g' := fun n σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := τ) hsum isOpen_Ioo isPreconnected_Ioo
      (fun n σ hσ => hD1 n σ (hJ σ (Ioo_subset_Icc_self hσ)))
      (fun n σ hσ => hL1 n σ (Ioo_subset_Icc_self hσ))
      ⟨by linarith, by linarith⟩ hg0A hτ
  have hev1 : (fun σ => psipA ν χf A σ x) =ᶠ[𝓝 s] (fun σ => ∑' n : ℤ,
      p2E ν (xj ν n x) σ * p2A (p2U ν σ) (p2TT (Ay ν χf A σ)) (p2QQ (xj ν n x) (Ay ν χf A σ))) := by
    filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with σ hσ
    exact hsP σ (by linarith [hσ.1])
  have hev2 : (fun σ => deriv (fun σ' => psipA ν χf A σ' x) σ) =ᶠ[𝓝 s]
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) := by
    have e2 := hev1.deriv
    have e3 : (fun σ => deriv (fun σ' => ∑' n : ℤ,
        p2E ν (xj ν n x) σ' * p2A (p2U ν σ') (p2TT (Ay ν χf A σ'))
          (p2QQ (xj ν n x) (Ay ν χf A σ'))) σ) =ᶠ[𝓝 s]
        (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) := by
      filter_upwards [Ioo_mem_nhds (by linarith : s / 2 < s) (by linarith : s < 2 * s)] with σ hσ
      exact (keyA σ hσ).deriv
    exact e2.trans e3
  -- second derivative of the sum
  have hg0B : Summable (fun n : ℤ => p2Phi1 ν s (xj ν n x) (Ay ν χf A s) (deriv (Ay ν χf A) s)) :=
    Summable.of_norm_bounded hsum (fun n => by
      rw [Real.norm_eq_abs]; exact hL1 n s hsJ)
  have keyB : ∀ τ ∈ Ioo (s / 2) (2 * s), HasDerivAt
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (∑' n : ℤ, p2Phi2 ν τ (xj ν n x) (Ay ν χf A τ) (deriv (Ay ν χf A) τ)
        (deriv (deriv (Ay ν χf A)) τ)) τ := fun τ hτ =>
    hasDerivAt_tsum_of_isPreconnected (u := fun n : ℤ => 60 * (1 + ν) ^ 2 * (K1 + K2 + K3) *
        (1 + |x.2|) ^ 6 * ((1 + |x.1 - (n : ℝ) * cOf ν|) ^ 6 *
          Real.exp (-(1 / (4 * (1 + ν * (2 * s)))) * (x.1 - (n : ℝ) * cOf ν) ^ 2)))
      (g := fun n σ => p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ))
      (g' := fun n σ => p2Phi2 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)
        (deriv (deriv (Ay ν χf A)) σ))
      (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := τ) hsum isOpen_Ioo isPreconnected_Ioo
      (fun n σ hσ => hD2 n σ (hJ σ (Ioo_subset_Icc_self hσ)))
      (fun n σ hσ => hL2 n σ (Ioo_subset_Icc_self hσ))
      ⟨by linarith, by linarith⟩ hg0B hτ
  have hdiffB : DifferentiableAt ℝ
      (fun σ => ∑' n : ℤ, p2Phi1 ν σ (xj ν n x) (Ay ν χf A σ) (deriv (Ay ν χf A) σ)) s :=
    (keyB s ⟨by linarith, by linarith⟩).differentiableAt
  exact hdiffB.congr_of_eventuallyEq hev2

end UnforcedLeray.Short.PartIIIb.Concrete
