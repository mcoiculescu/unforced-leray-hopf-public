import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OpBoundOfBox

/-!
# `zsumL` and the complex transport have norm at most `√c` (item `PartIII-b:C/near/delta/8/2/4/2`)

Source of record `the November 2 reference manuscript` 1641-1646, 2676-2679, 3564-3571.
`‖zsumL X‖_{H_T} ≤ ‖X‖_Z` (`ob_zsumL_norm_le`), `‖tv4 T‖ ≤ ‖T‖` on `Ten3` (the components of
`tv4` are a subset of the entries of `T`, with `rz` symmetrised), and the transport `cplxT` has
norm `≤ √c` (the `LpToLpOfMeasureLeSMul` bound `c^{1/2}` for `map cellPt μ_HT = c • s^{-1/2}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- A linear isometry, as a continuous linear map, preserves norms. -/
theorem lie_toCLM_norm_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E →ₗᵢ[ℝ] F) (x : E) :
    ‖e.toContinuousLinearMap x‖ = ‖x‖ :=
  e.norm_map x

/-- The pointwise dictionary `tv4` does not increase the norm on `Ten3`. -/
theorem norm_tv4_le_aux (T : Ten3) : ‖tv4 T‖ ≤ ‖T‖ := by
  have hT : ‖T‖ ^ 2 = ∑ p : Fin 3 × Fin 3, (T p) ^ 2 := EuclideanSpace.real_norm_sq_eq T
  have hV : ‖tv4 T‖ ^ 2 = (T (0, 0)) ^ 2 + (symRZ T) ^ 2 + (T (2, 2)) ^ 2 + (T (1, 1)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [tv4, Fin.sum_univ_four, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum : ∑ p : Fin 3 × Fin 3, (T p) ^ 2 =
      (T (0, 0)) ^ 2 + (T (0, 1)) ^ 2 + (T (0, 2)) ^ 2 + (T (1, 0)) ^ 2 + (T (1, 1)) ^ 2
        + (T (1, 2)) ^ 2 + (T (2, 0)) ^ 2 + (T (2, 1)) ^ 2 + (T (2, 2)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three]
    ring
  have hS : (symRZ T) ^ 2 ≤ (T (0, 2)) ^ 2 + (T (2, 0)) ^ 2 := by
    unfold symRZ
    nlinarith [sq_nonneg (T (0, 2) - T (2, 0)), sq_nonneg (T (0, 2) + T (2, 0))]
  have hsq : ‖tv4 T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [hV, hT, hsum]
    nlinarith [hS, sq_nonneg (T (0, 1)), sq_nonneg (T (1, 0)), sq_nonneg (T (1, 2)),
      sq_nonneg (T (2, 1)), sq_nonneg (T (0, 0)), sq_nonneg (T (1, 1)), sq_nonneg (T (2, 2))]
  nlinarith [norm_nonneg (tv4 T), norm_nonneg T, hsq]

/-- The operator norm of `tv4L` is at most one. -/
theorem norm_tv4L_le_aux : ‖Masked.tv4L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
  rw [one_mul]
  exact norm_tv4_le_aux T

/-- `√` of the `c^{1/2}` bound of `LpToLpOfMeasureLeSMul` (the case `c ≤ 0` is trivial). -/
theorem toReal_pow_half_le_sqrt_aux (c : ℝ) :
    (ENNReal.ofReal c).toReal ^ (1 / (2 : ℝ≥0∞)).toReal ≤ Real.sqrt c := by
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h2]
  rcases le_total 0 c with hc | hc
  · rw [ENNReal.toReal_ofReal hc, Real.sqrt_eq_rpow]
  · rw [ENNReal.ofReal_of_nonpos hc, Real.sqrt_eq_zero_of_nonpos hc, ENNReal.toReal_zero,
      Real.zero_rpow (by norm_num)]

/-- `‖cplxT T‖ ≤ √c ‖T‖` on `H_T` (source 1641-1646). -/
theorem cplxT_norm_le_sqrt_aux (c : ℝ) (h : Masked.CellPtHT c) (T : HTsp c) :
    ‖Masked.cplxT c h T‖ ≤ Real.sqrt c * ‖T‖ := by
  have hiso : ‖Masked.cplxT c h T‖ =
      ‖(Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le)
        (Masked.tv4L.compLpL 2 (ageμ c (-1 / 2)) T)‖ := by
    unfold Masked.cplxT
    rw [ContinuousLinearMap.comp_apply]
    exact lie_toCLM_norm_aux _ _
  have hY : ‖(Masked.tv4L.compLpL 2 (ageμ c (-1 / 2))) T‖ ≤ ‖T‖ := by
    have h1 := ContinuousLinearMap.le_opNorm (Masked.tv4L.compLpL 2 (ageμ c (-1 / 2))) T
    have h2 := ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := ageμ c (-1 / 2)) Masked.tv4L
    have h3 : ‖Masked.tv4L.compLpL 2 (ageμ c (-1 / 2))‖ ≤ 1 := h2.trans norm_tv4L_le_aux
    calc ‖(Masked.tv4L.compLpL 2 (ageμ c (-1 / 2))) T‖
        ≤ ‖Masked.tv4L.compLpL 2 (ageμ c (-1 / 2))‖ * ‖T‖ := h1
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = ‖T‖ := one_mul _
  have hL := (Lp.norm_LpToLpOfMeasureLeSMul_le (E := UnforcedLeray.Short.PartIIa.TensorVal) (p := 2)
    ENNReal.ofReal_ne_top h.le).trans (toReal_pow_half_le_sqrt_aux c)
  have hop := ContinuousLinearMap.le_opNorm (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le)
    (Masked.tv4L.compLpL 2 (ageμ c (-1 / 2)) T)
  rw [hiso]
  exact hop.trans (mul_le_mul hL hY (norm_nonneg _) (Real.sqrt_nonneg c))

theorem zsumTransportNorm_proof : ZsumTransportNorm := by
  intro c mZ ρb hT hmZ hρ hρ1 X
  have h1 := cplxT_norm_le_sqrt_aux c hT (Masked.zsumL c mZ ρb hmZ hρ X)
  have h2 := Masked.ob_zsumL_norm_le hmZ hρ hρ1 X
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg c))

theorem zsumTransportNorm : ZsumTransportNorm := zsumTransportNorm_proof

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
