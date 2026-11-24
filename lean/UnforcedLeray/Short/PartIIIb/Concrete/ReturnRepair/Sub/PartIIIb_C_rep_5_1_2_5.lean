import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4Org

/-!
# `PartIII-b:C/rep/5/1/2/5`: the output cut is a polynomial times the `ω_b` growth

Source `the November 2 reference manuscript` 5594-5600 ("up to a fixed polynomial in
`S`"), 5928-5945 (`ε³ = e^{-γ/ν}ν^{Re κ-5-2σ₀}/(2|𝒞(σ₀)|)`): `S^{3/4} = ε^{-3b/4} ≤ C ν^{-k} e^{(bγ/3)/ν}`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scutPowBound (D : SeqData) {dm dp : ℝ} (h : D.RepairStanding dm dp) : D.ScutPowBound := by
  set N : ℝ := 2 * ‖D.Pl.signedCoeff D.σ₀‖ with hN
  have hN0 : 0 < N := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  set r : ℝ := D.Pl.kappa.re - 5 - 2 * D.σ₀ with hr
  set q : ℝ := D.K.b / 4 with hq
  have hb0 := h.b_pos
  have hb1 := h.b_lt
  have hγ := h.gamma_pos
  have hq0 : 0 < q := by rw [hq]; positivity
  obtain ⟨k, hk⟩ := exists_nat_ge (|r| * q)
  have hle := retNu_retEps_eventually_le_one h.omega_ne h.gamma_pos D.coeff_ne
  refine ⟨N ^ q, k, ?_⟩
  filter_upwards [hle] with n ⟨hν1, _⟩
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν1
  have hlv : (D.level n).ν = retNu D.Pl D.σ₀ n := rfl
  have hle' : (D.level n).ε = retEps D.Pl D.σ₀ n := rfl
  set ν := (D.level n).ν with hν
  have hA : 0 < Real.exp (-(gRate D.Pl / ν)) * ν ^ r / N := by positivity
  -- S^(3/4) = (A⁻¹)^q
  have hS : ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) =
      (Real.exp (gRate D.Pl / ν) * (ν⁻¹) ^ r * N) ^ q := by
    have e1 : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
    have e2 : (D.level n).ε = (Real.exp (-(gRate D.Pl / ν)) * ν ^ r / N) ^ (1 / 3 : ℝ) := by
      rw [hle']; unfold retEps; rfl
    rw [e1, e2, ← Real.rpow_mul hA.le, ← Real.rpow_mul hA.le]
    have e3 : (Real.exp (-(gRate D.Pl / ν)) * ν ^ r / N)⁻¹ =
        Real.exp (gRate D.Pl / ν) * (ν⁻¹) ^ r * N := by
      rw [Real.inv_rpow hνp.le, Real.exp_neg]
      field_simp
    have e4 : (1 / 3 : ℝ) * -D.K.b * (3 / 4) = -q := by rw [hq]; ring
    rw [e4, Real.rpow_neg hA.le, ← Real.inv_rpow hA.le, e3]
  rw [hS]
  have hx : 0 ≤ Real.exp (gRate D.Pl / ν) := (Real.exp_pos _).le
  have hy : 0 ≤ (ν⁻¹) ^ r := Real.rpow_nonneg (inv_nonneg.2 hνp.le) _
  rw [Real.mul_rpow (mul_nonneg hx hy) hN0.le, Real.mul_rpow hx hy, ← Real.exp_mul]
  have hi : 1 ≤ ν⁻¹ := (one_le_inv₀ hνp).2 hν1'
  have h2 : ((ν⁻¹) ^ r) ^ q ≤ ν⁻¹ ^ k := by
    rw [← Real.rpow_mul (inv_nonneg.2 hνp.le), ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hi ?_
    nlinarith [le_abs_self r]
  have h3 : Real.exp (gRate D.Pl / ν * q) ≤ Real.exp ((D.K.b * (gRate D.Pl / 3)) / ν) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hνp]
    rw [hq]; nlinarith
  have hN' : 0 ≤ N ^ q := Real.rpow_nonneg hN0.le _
  have hz : 0 ≤ Real.exp (gRate D.Pl / ν * q) := (Real.exp_pos _).le
  calc Real.exp (gRate D.Pl / ν * q) * ((ν⁻¹) ^ r) ^ q * N ^ q
      ≤ Real.exp ((D.K.b * (gRate D.Pl / 3)) / ν) * ν⁻¹ ^ k * N ^ q := by
        gcongr
    _ = N ^ q * ν⁻¹ ^ k * Real.exp ((D.K.b * (gRate D.Pl / 3)) / ν) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
