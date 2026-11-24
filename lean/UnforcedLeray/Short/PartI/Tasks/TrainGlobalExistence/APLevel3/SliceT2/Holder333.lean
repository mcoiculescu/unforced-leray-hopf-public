import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2

/-!
# Part I, `PartI:T04/10/2/2/3`: the `(3,3,3)` Hölder step `Holder333`

Source of record: `the November 2 reference manuscript`, lines 285-288.
Route: `F (G F)` in `L¹` by `MemLp.mul` (`(3, 3/2, 1)`), with `G F ∈ L^{3/2}` from
`(3, 3, 3/2)`; Hölder `(3, 3/2)` gives `T³ ≤ P S²` with `P = ∫F³`, `S = ∫(GF)^{3/2}`;
Cauchy-Schwarz on `G^{3/2}, F^{3/2}` gives `S² ≤ (∫G³)(∫F³)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

/-- Conjugacy `(2, 2)` as real exponents. -/
theorem holder333_conj22 : (2:ℝ).HolderConjugate (2:ℝ) := by
  rw [Real.holderConjugate_iff]; norm_num

/-- `ENNReal` triple `(3, 3, 3/2)`. -/
theorem holder333_triple : ENNReal.HolderTriple (ENNReal.ofReal 3) (ENNReal.ofReal 3)
    (ENNReal.ofReal (3/2)) := by
  rw [ENNReal.holderTriple_iff]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3/2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- Square-root cancellation `(x^{1/2})² = x` for `x ≥ 0`. -/
theorem holder333_sq_half (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1:ℝ)/2)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- **Target `holder333`.** -/
theorem holder333 : Holder333 := by
  intro μ F G hF0 hG0 hF hG
  -- `G F ∈ L^{3/2}`
  have hGF : MemLp (fun z => G z * F z) (ENNReal.ofReal (3/2)) μ := by
    haveI := holder333_triple
    exact MemLp.mul (r := ENNReal.ofReal (3/2)) hF hG
  -- `F (G F) ∈ L¹`, hence integrable
  have hT_mem : MemLp (fun z => F z * (G z * F z)) 1 μ := by
    haveI := sl_triple3
    exact MemLp.mul (r := 1) hGF hF
  refine ⟨memLp_one_iff_integrable.1 hT_mem, ?_⟩
  -- Hölder `(3, 3/2)`
  have hT := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 3) (q := 3/2) sl_conj_32
    (f := F) (g := fun z => G z * F z)
    (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall fun z => mul_nonneg (hG0 z) (hF0 z)) hF hGF
  have e : (1:ℝ) / (3/2) = 2/3 := by norm_num
  rw [e] at hT
  have hTn : 0 ≤ ∫ z, F z * (G z * F z) ∂μ :=
    integral_nonneg fun z => mul_nonneg (hF0 z) (mul_nonneg (hG0 z) (hF0 z))
  have hP0 : 0 ≤ ∫ z, F z ^ (3:ℝ) ∂μ := integral_nonneg fun z => Real.rpow_nonneg (hF0 z) _
  have hS0 : 0 ≤ ∫ z, (G z * F z) ^ (3/2:ℝ) ∂μ :=
    integral_nonneg fun z => Real.rpow_nonneg (mul_nonneg (hG0 z) (hF0 z)) _
  have hA0 : 0 ≤ ∫ z, G z ^ (3:ℝ) ∂μ := integral_nonneg fun z => Real.rpow_nonneg (hG0 z) _
  have hT3 := sl_cube_holder hTn hP0 hS0 hT
  -- `G^{3/2} ∈ L²` and `F^{3/2} ∈ L²`
  have hG32 : MemLp (fun z => G z ^ (3/2:ℝ)) (ENNReal.ofReal 2) μ := by
    have h := hG.norm_rpow_div (ENNReal.ofReal (3/2))
    rw [ENNReal.toReal_ofReal (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
      show (3:ℝ) / (3/2) = 2 by norm_num] at h
    simpa only [Real.norm_of_nonneg (hG0 _)] using h
  have hF32 : MemLp (fun z => F z ^ (3/2:ℝ)) (ENNReal.ofReal 2) μ := by
    have h := hF.norm_rpow_div (ENNReal.ofReal (3/2))
    rw [ENNReal.toReal_ofReal (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
      show (3:ℝ) / (3/2) = 2 by norm_num] at h
    simpa only [Real.norm_of_nonneg (hF0 _)] using h
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) holder333_conj22
    (f := fun z => G z ^ (3/2:ℝ)) (g := fun z => F z ^ (3/2:ℝ))
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (hG0 z) _)
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (hF0 z) _) hG32 hF32
  have eG : ∫ z, (G z ^ (3/2:ℝ)) ^ (2:ℝ) ∂μ = ∫ z, G z ^ (3:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [← Real.rpow_mul (hG0 z)]; norm_num)
  have eF : ∫ z, (F z ^ (3/2:ℝ)) ^ (2:ℝ) ∂μ = ∫ z, F z ^ (3:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [← Real.rpow_mul (hF0 z)]; norm_num)
  have eP : ∫ z, (G z * F z) ^ (3/2:ℝ) ∂μ = ∫ z, G z ^ (3/2:ℝ) * F z ^ (3/2:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => Real.mul_rpow (hG0 z) (hF0 z))
  rw [eG, eF, ← eP] at hCS
  -- `S² ≤ (∫G³)(∫F³)`
  have hS2 : (∫ z, (G z * F z) ^ (3/2:ℝ) ∂μ) ^ 2 ≤
      (∫ z, G z ^ (3:ℝ) ∂μ) * (∫ z, F z ^ (3:ℝ) ∂μ) := by
    have h1 := pow_le_pow_left₀ hS0 hCS 2
    have h2 : ((∫ z, G z ^ (3:ℝ) ∂μ) ^ ((1:ℝ)/2) * (∫ z, F z ^ (3:ℝ) ∂μ) ^ ((1:ℝ)/2)) ^ 2 =
        (∫ z, G z ^ (3:ℝ) ∂μ) * (∫ z, F z ^ (3:ℝ) ∂μ) := by
      rw [mul_pow, holder333_sq_half _ hA0, holder333_sq_half _ hP0]
    linarith
  calc (∫ z, F z * (G z * F z) ∂μ) ^ 3
      ≤ (∫ z, F z ^ (3:ℝ) ∂μ) * (∫ z, (G z * F z) ^ (3/2:ℝ) ∂μ) ^ 2 := hT3
    _ ≤ (∫ z, F z ^ (3:ℝ) ∂μ) * ((∫ z, G z ^ (3:ℝ) ∂μ) * (∫ z, F z ^ (3:ℝ) ∂μ)) :=
        mul_le_mul_of_nonneg_left hS2 hP0
    _ = (∫ z, G z ^ (3:ℝ) ∂μ) * (∫ z, F z ^ (3:ℝ) ∂μ) ^ 2 := by ring

end UnforcedLeray.Short.PartI
