import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT1.Helpers

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Hölder conjugacy `(3, 3/2)` as real exponents. -/
theorem sl_conj_32 : (3:ℝ).HolderConjugate (3/2:ℝ) := by
  rw [Real.holderConjugate_iff]; norm_num

/-- Hölder conjugacy `(4/3, 4)`. -/
theorem sl_conj_43 : (4/3:ℝ).HolderConjugate (4:ℝ) := by
  rw [Real.holderConjugate_iff]; norm_num

/-- `ENNReal` triple `(6, 2, 3/2)` for multiplying an `L²` and an `L⁶` function into `L^{3/2}`. -/
theorem sl_triple : ENNReal.HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal 2) (ENNReal.ofReal (3/2)) := by
  rw [ENNReal.holderTriple_iff]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 6),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3/2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- First Hölder step: `∫ F (G H) ≤ ...`, cubed. -/
theorem sl_holder_T {μ : Measure Plane} {F G H : Plane → ℝ}
    (hF0 : ∀ z, 0 ≤ F z) (hG0 : ∀ z, 0 ≤ G z) (hH0 : ∀ z, 0 ≤ H z)
    (hF : MemLp F (ENNReal.ofReal 3) μ) (hG : MemLp G (ENNReal.ofReal 2) μ)
    (hH : MemLp H (ENNReal.ofReal 6) μ) :
    (∫ z, F z * (G z * H z) ∂μ) ^ 3 ≤
      (∫ z, F z ^ (3:ℝ) ∂μ) * (∫ z, (G z * H z) ^ (3/2:ℝ) ∂μ) ^ 2 := by
  have hHG : MemLp (fun z => G z * H z) (ENNReal.ofReal (3/2)) μ := by
    have e : (fun z => G z * H z) = (fun z => H z * G z) := funext fun z => mul_comm _ _
    rw [e]
    haveI : ENNReal.HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal 2) (ENNReal.ofReal (3/2)) :=
      sl_triple
    exact MemLp.mul (r := ENNReal.ofReal (3/2)) hG hH
  have hT := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 3) (q := 3/2) sl_conj_32
    (f := F) (g := fun z => G z * H z)
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall fun z => mul_nonneg (hG0 z) (hH0 z))
    (by rw [show ENNReal.ofReal (3:ℝ) = ENNReal.ofReal 3 from rfl]; exact hF) hHG
  have e : (1:ℝ) / (3/2) = 2/3 := by norm_num
  rw [e] at hT
  have hTn : 0 ≤ ∫ z, F z * (G z * H z) ∂μ :=
    integral_nonneg fun z => mul_nonneg (hF0 z) (mul_nonneg (hG0 z) (hH0 z))
  exact sl_cube_holder hTn
    (integral_nonneg fun z => Real.rpow_nonneg (hF0 z) _)
    (integral_nonneg fun z => Real.rpow_nonneg (mul_nonneg (hG0 z) (hH0 z)) _) hT

/-- Second Hölder step: `∫ (G H)^{3/2} ≤ (∫ G²)^{3/4} (∫ H⁶)^{1/4}`. -/
theorem sl_holder_S {μ : Measure Plane} {G H : Plane → ℝ}
    (hG0 : ∀ z, 0 ≤ G z) (hH0 : ∀ z, 0 ≤ H z)
    (hG : MemLp G (ENNReal.ofReal 2) μ) (hH : MemLp H (ENNReal.ofReal 6) μ) :
    ∫ z, (G z * H z) ^ (3/2:ℝ) ∂μ ≤
      (∫ z, G z ^ (2:ℝ) ∂μ) ^ (3/4:ℝ) * (∫ z, H z ^ (6:ℝ) ∂μ) ^ (1/4:ℝ) := by
  have hf : MemLp (fun z => G z ^ (3/2:ℝ)) (ENNReal.ofReal (4/3)) μ := by
    have h := hG.norm_rpow_div (ENNReal.ofReal (3/2))
    rw [ENNReal.toReal_ofReal (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
      show (2:ℝ) / (3/2) = 4/3 by norm_num] at h
    simpa only [Real.norm_of_nonneg (hG0 _)] using h
  have hg : MemLp (fun z => H z ^ (3/2:ℝ)) (ENNReal.ofReal 4) μ := by
    have h := hH.norm_rpow_div (ENNReal.ofReal (3/2))
    rw [ENNReal.toReal_ofReal (by norm_num), ← ENNReal.ofReal_div_of_pos (by norm_num),
      show (6:ℝ) / (3/2) = 4 by norm_num] at h
    simpa only [Real.norm_of_nonneg (hH0 _)] using h
  have hH' := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 4/3) (q := 4) sl_conj_43
    (f := fun z => G z ^ (3/2:ℝ)) (g := fun z => H z ^ (3/2:ℝ))
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (hG0 z) _)
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (hH0 z) _) hf hg
  have e1 : ∫ z, (G z ^ (3/2:ℝ)) ^ (4/3:ℝ) ∂μ = ∫ z, G z ^ (2:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [← Real.rpow_mul (hG0 z)]; norm_num)
  have e2 : ∫ z, (H z ^ (3/2:ℝ)) ^ (4:ℝ) ∂μ = ∫ z, H z ^ (6:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [← Real.rpow_mul (hH0 z)]; norm_num)
  have e3 : ∫ z, (G z * H z) ^ (3/2:ℝ) ∂μ =
      ∫ z, G z ^ (3/2:ℝ) * H z ^ (3/2:ℝ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => Real.mul_rpow (hG0 z) (hH0 z))
  have e4 : (1:ℝ) / (4/3) = 3/4 := by norm_num
  rw [e3]
  refine hH'.trans (le_of_eq ?_)
  rw [e1, e2, e4]

/-- The product `G H` of an `L²` and an `L⁶` function lies in `L^{3/2}`. -/
theorem sl_memLp_GH {μ : Measure Plane} {G H : Plane → ℝ}
    (hG : MemLp G (ENNReal.ofReal 2) μ) (hH : MemLp H (ENNReal.ofReal 6) μ) :
    MemLp (fun z => G z * H z) (ENNReal.ofReal (3/2)) μ := by
  have e : (fun z => G z * H z) = (fun z => H z * G z) := funext fun z => mul_comm _ _
  rw [e]
  haveI : ENNReal.HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal 2) (ENNReal.ofReal (3/2)) :=
    sl_triple
  exact MemLp.mul (r := ENNReal.ofReal (3/2)) hG hH

/-- Conjugacy `(3, 3/2)` as an `ENNReal` triple with `r = 1`. -/
theorem sl_triple3 : ENNReal.HolderTriple (ENNReal.ofReal 3) (ENNReal.ofReal (3/2)) 1 := by
  rw [ENNReal.holderTriple_iff]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3/2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), inv_one, ← ENNReal.ofReal_one]
  congr 1; norm_num

end UnforcedLeray.Short.PartI
