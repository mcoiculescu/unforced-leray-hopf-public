import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# `PartIII-b:C/asrc/ra/8/1/6` : leaf (B3) `VjGaussBound`

Source of record: `the November 2 reference manuscript` (73 pages), 4963, 4978.

The Gaussian bound of `V_j` and of its first derivative by the lattice majorant `bkMaj` with
`a = ageA ν s`, with the constant `K = 2`. The value is `‖V_j‖ = (a²)⁻¹ e ‖x_j‖` and the derivative
satisfies `‖DV_j[v]‖ ≤ (a²)⁻¹ e (1 + ‖x_j‖²/a) ‖v‖` (`gp_Vj_norm_eq`, `gp_fderiv_Vj_norm`).
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The value bound: `‖V_j(z)‖ ≤ 2 bkMaj`. -/
lemma bkB3_value_le (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (k : ℤ) (z : ℝ × ℝ) :
    ‖Vj ν s k z‖ ≤ 2 * bkMaj ν (ageA ν s) k z := by
  have ha1 : 1 ≤ ageA ν s := bk_one_le_ageA hν hs
  have hA : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hE : 0 ≤ Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hw : ‖xj ν k z‖ ≤ (1 + ‖xj ν k z‖) ^ 6 := by
    have h16 : (1 + ‖xj ν k z‖) ^ 1 ≤ (1 + ‖xj ν k z‖) ^ 6 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg (xj ν k z)]) (by norm_num)
    rw [pow_one] at h16
    linarith
  rw [gp_Vj_norm_eq]
  unfold bkMaj
  calc (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) * ‖xj ν k z‖
      ≤ 1 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) * ‖xj ν k z‖ := by gcongr
    _ ≤ 1 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) * (1 + ‖xj ν k z‖) ^ 6 := by gcongr
    _ ≤ 2 * ((1 + ‖xj ν k z‖) ^ 6 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))) := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖xj ν k z‖) ^ 6) hE]

/-- The derivative bound: `‖DV_j(z)‖ ≤ 2 bkMaj`. -/
lemma bkB3_fderiv_le (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (k : ℤ) (z : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s k) z‖ ≤ 2 * bkMaj ν (ageA ν s) k z := by
  have ha1 : 1 ≤ ageA ν s := bk_one_le_ageA hν hs
  have ha0 : 0 < ageA ν s := by linarith
  have hA : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hE : 0 ≤ Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hsq : 1 + ‖xj ν k z‖ ^ 2 ≤ (1 + ‖xj ν k z‖) ^ 6 := by
    have h2 : (1 + ‖xj ν k z‖) ^ 2 ≤ (1 + ‖xj ν k z‖) ^ 6 :=
      pow_le_pow_right₀ (by linarith [norm_nonneg (xj ν k z)]) (by norm_num)
    nlinarith [norm_nonneg (xj ν k z)]
  have hB : 1 + ‖xj ν k z‖ ^ 2 / ageA ν s ≤ (1 + ‖xj ν k z‖) ^ 6 := by
    have hd : ‖xj ν k z‖ ^ 2 / ageA ν s ≤ ‖xj ν k z‖ ^ 2 :=
      div_le_self (sq_nonneg _) ha1
    linarith
  have hP : (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))
      * (1 + ‖xj ν k z‖ ^ 2 / ageA ν s)
      ≤ 2 * ((1 + ‖xj ν k z‖) ^ 6 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))) := by
    calc (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))
          * (1 + ‖xj ν k z‖ ^ 2 / ageA ν s)
        ≤ 1 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s)) * (1 + ‖xj ν k z‖) ^ 6 := by
          gcongr
      _ ≤ 2 * ((1 + ‖xj ν k z‖) ^ 6 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))) := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖xj ν k z‖) ^ 6) hE]
  have hbk : 0 ≤ 2 * bkMaj ν (ageA ν s) k z := by
    have := bkMaj_nonneg ν (ageA ν s) k z
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith [bkMaj_nonneg ν (ageA ν s) k z])
    (fun v => ?_)
  have h := gp_fderiv_Vj_norm ν s ha0 k z v
  unfold bkMaj
  calc ‖fderiv ℝ (Vj ν s k) z v‖
      ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))
          * (1 + ‖xj ν k z‖ ^ 2 / ageA ν s) * ‖v‖ := h
    _ ≤ 2 * ((1 + ‖xj ν k z‖) ^ 6 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg v)
    _ = 2 * ((1 + ‖xj ν k z‖) ^ 6 * Real.exp (-(sq2 (xj ν k z)) / (4 * ageA ν s))) * ‖v‖ := rfl

/-- **(B3)** Gaussian bound of `V_j` and its first derivative (source 4963, 4978). -/
theorem vjGaussBound : VjGaussBound := by
  intro ν s hν hs
  refine ⟨2, fun k z => ⟨?_, ?_⟩⟩
  · exact bkB3_value_le ν s hν hs k z
  · exact bkB3_fderiv_le ν s hν hs k z

end UnforcedLeray.Short.PartIIIb.Concrete
