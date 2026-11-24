import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.NearInst
  UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem fmNsSymTv4 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmNsSymTv4 := by
  refine ⟨2, by norm_num, fun T => ?_⟩
  have hn : ‖tv4 T‖ ^ 2 = T (0, 0) ^ 2 + symRZ T ^ 2 + T (2, 2) ^ 2 + T (1, 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [tv4, Fin.sum_univ_four, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i, ∑ j, nsSym T i j ^ 2
      = T (0, 0) ^ 2 + T (1, 1) ^ 2 + T (2, 2) ^ 2 + 2 * symRZ T ^ 2 := by
    simp [nsSym, Fin.sum_univ_three]
    ring
  have hreal : UnforcedLeray.Short.IIIa.tensorNorm (nsSym T) ≤ 2 * ‖tv4 T‖ := by
    unfold UnforcedLeray.Short.IIIa.tensorNorm
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [hsum]
    nlinarith [sq_nonneg (T (0, 0)), sq_nonneg (T (1, 1)), sq_nonneg (T (2, 2)),
      sq_nonneg (symRZ T), hn]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hreal
