import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B0.Bound

/-!
# `RawD1Bound2`: the `j = 2` bound of the raw ring derivative (`PartIII-b:C/rep/8/2/1/2/9`)

Source `the November 2 reference manuscript`, lines 2073-2077 and 5462-5476.
`∂_η b = ∂_η v + ε ∂_η H e_z` and `flatDir 2 = (0,1)`, so the difference is `s ε ∂_η H e_z`,
with `∂_η H = -η ψ_ηη - 2 s ψ_sη` (`Core.lean`: `rawH_deriv_le`), bounded by `4 ε s 𝔴₃`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawD1Bound2 : UnforcedLeray.Short.PartIIIb.Concrete.RawD1Bound2 := by
  refine ⟨4, fun L hε p hp => ?_⟩
  have hε0 : 0 < L.ε := L.ε_pos
  have hw3 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hHe := rawH_deriv_le L (Real.log p.1, p.2) hw3
  have hS0 := ringS_nonneg L (Real.log p.1, p.2)
  have ha1 : 1 + |p.2.2| ≤ (1 + |p.2.2|) ^ 3 :=
    le_self_pow₀ (by linarith [abs_nonneg p.2.2]) (by norm_num)
  have hk1 : (1 + |p.2.2|) * ringS L (Real.log p.1, p.2) ≤
      (1 + |p.2.2|) ^ 3 * ringS L (Real.log p.1, p.2) :=
    mul_le_mul_of_nonneg_right ha1 hS0
  have hB : |fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (0, 1))| ≤
      4 * ((1 + |p.2.2|) ^ 3 * ringS L (Real.log p.1, p.2)) := by
    linarith [mul_nonneg (abs_nonneg p.2.2) hS0]
  rw [rawD1_dEta L hp, rawD1_flat2 L hp, ← smul_sub, ← merSp_sub', add_sub_cancel_left]
  have hn : ‖(L.ε * fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (0, 1))) • rawE1‖ =
      L.ε * |fderiv ℝ (rawH L) (Real.log p.1, p.2) (0, (0, 1))| := by
    rw [norm_smul, rawE1_norm, mul_one, norm_mul, Real.norm_of_nonneg hε0.le, Real.norm_eq_abs]
  rw [norm_smul, Real.norm_of_nonneg hp.le, merSp_norm, hn]
  have htw : trainWeight 3 L p = (1 + |p.2.2|) ^ 3 * ringS L (Real.log p.1, p.2) := rfl
  rw [htw]
  have key := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hε0.le) hp.le
  linarith [key]

end UnforcedLeray.Short.PartIIIb.Concrete
