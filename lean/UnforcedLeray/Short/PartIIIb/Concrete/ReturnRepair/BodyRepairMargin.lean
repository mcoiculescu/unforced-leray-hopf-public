import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq

/-!
# The body repair margin on the gain band (source 5557-5562, 5617)

`BodyRepairMargin` (the gain band `e^{-(19γ/66 - 3m₀/2)/ν}`) follows from `BodyError`
(`R⁻¹‖f_r‖_{Y_2} ≤ P_ν|N_ν|G(w)(ε^{85/22}e^{m₀/ν} + ε^{52/11}e^{2m₀/ν})`):
`|N_ν| = e^{γ/ν}ν^{-Re κ}`, `ε = C_*ν^r e^{-(γ/3)/ν}` (`retEps_eq_form`), so
`e^{γ/ν}ε^{85/22}e^{m₀/ν} ≤ P_ν e^{-(19γ/66 - m₀)/ν}` and
`e^{γ/ν}ε^{52/11}e^{2m₀/ν} ≤ P_ν e^{-(19γ/33 - 2m₀)/ν}`, both bounded by
`P_ν e^{-(19γ/66 - 3m₀/2)/ν}` since `0 < m₀ < γ/1000`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

private theorem rpow_le_inv_pow_body (p : ℝ) :
    ∃ j : ℕ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ν ^ p ≤ ν⁻¹ ^ j := by
  refine ⟨⌈-p⌉₊, fun ν hν0 hν1 => ?_⟩
  have h1 : ν ^ p ≤ ν ^ (-((⌈-p⌉₊ : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by linarith [Nat.le_ceil (-p)])
  rw [Real.rpow_neg hν0.le, Real.rpow_natCast, ← inv_pow] at h1
  exact h1

private theorem gaugeN_eq_body (Pl : PlanarData) (L : ReturnLevel) :
    gaugeN Pl L = Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re) := by
  unfold gaugeN Nnu
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos L.ν_pos,
    Complex.div_ofReal_re, Complex.neg_re]

private theorem term1_le_gain_body (γ m0 c r ν : ℝ) (hν : 0 < ν) (hc : 0 < c) (hm0 : 0 ≤ m0)
    (j : ℕ) (hj : ν ^ (r * (85 / 22 : ℝ)) ≤ ν⁻¹ ^ j) :
    Real.exp (γ / ν) * ((c * ν ^ r * Real.exp (-(γ / 3) / ν)) ^ (85 / 22 : ℝ) * Real.exp (m0 / ν)) ≤
      c ^ (85 / 22 : ℝ) * ν⁻¹ ^ j * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
  have hνr : 0 ≤ ν ^ r := Real.rpow_nonneg hν.le _
  have hE : 0 ≤ Real.exp (-(γ / 3) / ν) := (Real.exp_pos _).le
  rw [Real.mul_rpow (mul_nonneg hc.le hνr) hE, Real.mul_rpow hc.le hνr, ← Real.rpow_mul hν.le,
    ← Real.exp_mul]
  have hexp : Real.exp (γ / ν) * Real.exp (-(γ / 3) / ν * (85 / 22 : ℝ)) * Real.exp (m0 / ν) ≤
      Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have key : γ / ν + -(γ / 3) / ν * (85 / 22 : ℝ) + m0 / ν = -((19 * γ / 66 - m0) / ν) := by ring
    rw [key, neg_div]
    have h : (19 * γ / 66 - 3 * m0 / 2) / ν ≤ (19 * γ / 66 - m0) / ν :=
      div_le_div_of_nonneg_right (by linarith) hν.le
    linarith
  have hX : 0 ≤ c ^ (85 / 22 : ℝ) := Real.rpow_nonneg hc.le _
  calc Real.exp (γ / ν) *
        (c ^ (85 / 22 : ℝ) * ν ^ (r * (85 / 22 : ℝ)) * Real.exp (-(γ / 3) / ν * (85 / 22 : ℝ)) *
          Real.exp (m0 / ν))
      = (c ^ (85 / 22 : ℝ) * ν ^ (r * (85 / 22 : ℝ))) *
          (Real.exp (γ / ν) * Real.exp (-(γ / 3) / ν * (85 / 22 : ℝ)) * Real.exp (m0 / ν)) := by
        ring
    _ ≤ (c ^ (85 / 22 : ℝ) * ν⁻¹ ^ j) * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hj hX) hexp (by positivity)
          (mul_nonneg hX (pow_nonneg (inv_nonneg.2 hν.le) _))

private theorem term2_le_gain_body (γ m0 c r ν : ℝ) (hν : 0 < ν) (hc : 0 < c) (hγ : 0 < γ)
    (hm0 : m0 < γ / 1000) (j : ℕ) (hj : ν ^ (r * (52 / 11 : ℝ)) ≤ ν⁻¹ ^ j) :
    Real.exp (γ / ν) * ((c * ν ^ r * Real.exp (-(γ / 3) / ν)) ^ (52 / 11 : ℝ) *
      Real.exp (2 * m0 / ν)) ≤
      c ^ (52 / 11 : ℝ) * ν⁻¹ ^ j * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
  have hνr : 0 ≤ ν ^ r := Real.rpow_nonneg hν.le _
  have hE : 0 ≤ Real.exp (-(γ / 3) / ν) := (Real.exp_pos _).le
  rw [Real.mul_rpow (mul_nonneg hc.le hνr) hE, Real.mul_rpow hc.le hνr, ← Real.rpow_mul hν.le,
    ← Real.exp_mul]
  have hexp : Real.exp (γ / ν) * Real.exp (-(γ / 3) / ν * (52 / 11 : ℝ)) * Real.exp (2 * m0 / ν) ≤
      Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have key : γ / ν + -(γ / 3) / ν * (52 / 11 : ℝ) + 2 * m0 / ν =
        -((19 * γ / 33 - 2 * m0) / ν) := by ring
    rw [key, neg_div]
    have h : (19 * γ / 66 - 3 * m0 / 2) / ν ≤ (19 * γ / 33 - 2 * m0) / ν :=
      div_le_div_of_nonneg_right (by linarith) hν.le
    linarith
  have hX : 0 ≤ c ^ (52 / 11 : ℝ) := Real.rpow_nonneg hc.le _
  calc Real.exp (γ / ν) *
        (c ^ (52 / 11 : ℝ) * ν ^ (r * (52 / 11 : ℝ)) * Real.exp (-(γ / 3) / ν * (52 / 11 : ℝ)) *
          Real.exp (2 * m0 / ν))
      = (c ^ (52 / 11 : ℝ) * ν ^ (r * (52 / 11 : ℝ))) *
          (Real.exp (γ / ν) * Real.exp (-(γ / 3) / ν * (52 / 11 : ℝ)) *
            Real.exp (2 * m0 / ν)) := by ring
    _ ≤ (c ^ (52 / 11 : ℝ) * ν⁻¹ ^ j) * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hj hX) hexp (by positivity)
          (mul_nonneg hX (pow_nonneg (inv_nonneg.2 hν.le) _))

private theorem core_body_margin (γ m0 C c r κre ν ε G t X : ℝ) (k j0 j1 j2 : ℕ)
    (hγ : 0 < γ) (hm0 : 0 ≤ m0) (hm0s : m0 < γ / 1000) (hc : 0 < c) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hεpos : 0 < ε) (ht : 0 ≤ t)
    (hj0 : ν ^ (-κre) ≤ ν⁻¹ ^ j0)
    (hj1 : ν ^ (r * (85 / 22 : ℝ)) ≤ ν⁻¹ ^ j1)
    (hj2 : ν ^ (r * (52 / 11 : ℝ)) ≤ ν⁻¹ ^ j2)
    (hG : G = Real.exp (γ / ν) * ν ^ (-κre))
    (hεform : ε = c * ν ^ r * Real.exp (-(γ / 3) / ν))
    (hX : X ≤ C * ν⁻¹ ^ k * G *
      (ε ^ (85 / 22 : ℝ) * Real.exp (m0 / ν) + ε ^ (52 / 11 : ℝ) * Real.exp (2 * m0 / ν)) * t) :
    X ≤ |C| * (c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (k + j0 + (j1 + j2)) *
      Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) * t := by
  have hNi : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
  have hN1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1
  have hE0 : 0 ≤ Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := (Real.exp_pos _).le
  set S : ℝ := ε ^ (85 / 22 : ℝ) * Real.exp (m0 / ν) + ε ^ (52 / 11 : ℝ) * Real.exp (2 * m0 / ν)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hν0.le _)
  have ht1 : Real.exp (γ / ν) * (ε ^ (85 / 22 : ℝ) * Real.exp (m0 / ν)) ≤
      c ^ (85 / 22 : ℝ) * ν⁻¹ ^ j1 * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
    rw [hεform]
    exact term1_le_gain_body γ m0 c r ν hν0 hc hm0 j1 hj1
  have ht2 : Real.exp (γ / ν) * (ε ^ (52 / 11 : ℝ) * Real.exp (2 * m0 / ν)) ≤
      c ^ (52 / 11 : ℝ) * ν⁻¹ ^ j2 * Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
    rw [hεform]
    exact term2_le_gain_body γ m0 c r ν hν0 hc hγ hm0s j2 hj2
  have hNJ1 : ν⁻¹ ^ j1 ≤ ν⁻¹ ^ (j1 + j2) := pow_le_pow_right₀ hN1 (by omega)
  have hNJ2 : ν⁻¹ ^ j2 ≤ ν⁻¹ ^ (j1 + j2) := pow_le_pow_right₀ hN1 (by omega)
  have hc1 : 0 ≤ c ^ (85 / 22 : ℝ) := Real.rpow_nonneg hc.le _
  have hc2 : 0 ≤ c ^ (52 / 11 : ℝ) := Real.rpow_nonneg hc.le _
  have hES : Real.exp (γ / ν) * S ≤
      (c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (j1 + j2) *
        Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
    have h1 : Real.exp (γ / ν) * S ≤
        (c ^ (85 / 22 : ℝ) * ν⁻¹ ^ j1 + c ^ (52 / 11 : ℝ) * ν⁻¹ ^ j2) *
          Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) := by
      dsimp [S]
      linarith [ht1, ht2]
    have h2 : c ^ (85 / 22 : ℝ) * ν⁻¹ ^ j1 + c ^ (52 / 11 : ℝ) * ν⁻¹ ^ j2 ≤
        (c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (j1 + j2) := by
      linarith [mul_le_mul_of_nonneg_left hNJ1 hc1, mul_le_mul_of_nonneg_left hNJ2 hc2]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hE0)
  have hGS : G * S ≤
      ν⁻¹ ^ j0 * ((c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (j1 + j2) *
        Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν)) := by
    rw [hG]
    calc Real.exp (γ / ν) * ν ^ (-κre) * S
        = ν ^ (-κre) * (Real.exp (γ / ν) * S) := by ring
      _ ≤ ν⁻¹ ^ j0 * ((c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (j1 + j2) *
            Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν)) :=
          mul_le_mul hj0 hES (mul_nonneg (Real.exp_pos _).le hS0) (pow_nonneg hNi _)
  have habs : C * ν⁻¹ ^ k * G * S * t ≤ |C| * ν⁻¹ ^ k * (G * S) * t := by
    have h1 : C ≤ |C| := le_abs_self C
    have h2 : 0 ≤ ν⁻¹ ^ k * (G * S) * t :=
      mul_nonneg (mul_nonneg (pow_nonneg hNi _) (mul_nonneg hG0 hS0)) ht
    calc C * ν⁻¹ ^ k * G * S * t = C * (ν⁻¹ ^ k * (G * S) * t) := by ring
      _ ≤ |C| * (ν⁻¹ ^ k * (G * S) * t) := mul_le_mul_of_nonneg_right h1 h2
      _ = |C| * ν⁻¹ ^ k * (G * S) * t := by ring
  calc X ≤ C * ν⁻¹ ^ k * G * S * t := hX
    _ ≤ |C| * ν⁻¹ ^ k * (G * S) * t := habs
    _ ≤ |C| * ν⁻¹ ^ k * (ν⁻¹ ^ j0 * ((c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (j1 + j2) *
          Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν))) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGS (mul_nonneg (abs_nonneg C) (pow_nonneg hNi _))) ht
    _ = |C| * (c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)) * ν⁻¹ ^ (k + j0 + (j1 + j2)) *
          Real.exp (-(19 * γ / 66 - 3 * m0 / 2) / ν) * t := by
        rw [pow_add, pow_add]
        ring

theorem bodyRepairMargin (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h : D.BodyError) : D.BodyRepairMargin := by
  obtain ⟨C, k, hB⟩ := h
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  have hm0 : 0 ≤ D.K.m0 := hst.m0_pos.le
  have hm0s : D.K.m0 < gRate D.Pl / 1000 := hst.m0_small
  have h2c : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  set c : ℝ := (2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ))
  set r : ℝ := (D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3
  have hc0 : 0 < c := Real.rpow_pos_of_pos h2c _
  obtain ⟨j0, hj0⟩ := rpow_le_inv_pow_body (-D.Pl.kappa.re)
  obtain ⟨j1, hj1⟩ := rpow_le_inv_pow_body (r * (85 / 22 : ℝ))
  obtain ⟨j2, hj2⟩ := rpow_le_inv_pow_body (r * (52 / 11 : ℝ))
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hst.omega_ne).eventually_lt_const one_pos).mono fun n hn => hn.le
  refine ⟨|C| * (c ^ (85 / 22 : ℝ) + c ^ (52 / 11 : ℝ)), k + j0 + (j1 + j2), ?_⟩
  filter_upwards [hB, hν1] with n hBn hν1n
  intro z hz w
  have hBz := hBn z hz w
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  exact core_body_margin (gRate D.Pl) D.K.m0 C c r D.Pl.kappa.re (D.level n).ν (D.level n).ε
    (gaugeN D.Pl (D.level n)) ‖w‖ _ k j0 j1 j2 hγ hm0 hm0s hc0 hν0 hν1n hεpos (norm_nonneg w)
    (hj0 _ hν0 hν1n) (hj1 _ hν0 hν1n) (hj2 _ hν0 hν1n) (gaugeN_eq_body D.Pl (D.level n))
    (retEps_eq_form D.coeff_ne n) hBz

end UnforcedLeray.Short.PartIIIb.Concrete
