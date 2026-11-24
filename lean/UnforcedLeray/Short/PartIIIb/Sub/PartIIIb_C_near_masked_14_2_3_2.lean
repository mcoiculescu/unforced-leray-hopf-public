import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3

/-!
# Decomposition of `CartSchur` (`PartIII-b:C/near/masked/14/2/3/2`; source 3996-4011)

Source: `the November 2 reference manuscript`.

`CartSchur` for `λ < 1` follows from the `λ = 1` Schur bound `SchurOne` by the scaling `w = λ z`
(proved here: `cartSliceOut_scale`, `lintegral_dilate`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Scaling of Lebesgue measure on `ℝ³`. -/
lemma lintegral_smul_space (l : ℝ) (hl : 0 < l) (F : Space → ℝ≥0∞) :
    ∫⁻ z : Space, F (l • z) = ENNReal.ofReal (l ^ (-3 : ℝ)) * ∫⁻ w : Space, F w := by
  let e : Space ≃ᵐ Space := (Homeomorph.smulOfNeZero l hl.ne').toMeasurableEquiv
  have h := Measure.map_addHaar_smul (volume : Measure Space) hl.ne'
  have h2 : ∫⁻ w, F w ∂(Measure.map (l • ·) (volume : Measure Space)) = ∫⁻ z, F (l • z) := by
    have : (Measure.map (l • ·) (volume : Measure Space)) = Measure.map e volume := rfl
    rw [this, lintegral_map_equiv]
    rfl
  rw [← h2, h, lintegral_smul_measure, smul_eq_mul]
  congr 1
  rw [finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (by positivity)]
  congr 1
  rw [Real.rpow_neg hl.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- Scaling `w = λ z` in the slice (the indicator only gets larger, since `λ < 1`). -/
lemma cartSliceOut_scale (R δ S l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (g : Space → ℝ) (y : Space) :
    cartSliceOut R δ S l g y ≤
      ENNReal.ofReal (l ^ (-3 : ℝ)) *
        cartSliceOut R δ S 1 (fun w => g (l⁻¹ • w)) y := by
  unfold cartSliceOut
  split_ifs with hS
  · set W := ENNReal.ofReal (Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)))⁻¹
    set F : Space → ℝ≥0∞ := fun w =>
      (if Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (w 0 ^ 2 + w 1 ^ 2) then
          ENNReal.ofReal (‖y - (1 : ℝ) • w‖ ^ (-4 : ℝ) * g (l⁻¹ • w)) else 0) with hF
    have hsc := lintegral_smul_space l hl0 F
    rw [mul_left_comm, ← hsc]
    gcongr with z
    simp only [hF]
    have hzz : l⁻¹ • l • z = z := by rw [smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
    rw [hzz, one_smul]
    split_ifs with h1 h2
    · rfl
    · exfalso; apply h2
      refine lt_of_lt_of_le h1 ?_
      have e0 : (l • z) 0 = l * z 0 := rfl
      have e1 : (l • z) 1 = l * z 1 := rfl
      rw [e0, e1]
      by_cases hr : z 0 ^ 2 + z 1 ^ 2 = 0
      · rw [hr]; simp only [div_zero]; positivity
      · have hrp : 0 < z 0 ^ 2 + z 1 ^ 2 :=
          lt_of_le_of_ne (by positivity) (Ne.symm hr)
        have : (l * z 0) ^ 2 + (l * z 1) ^ 2 = l ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by ring
        rw [this]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [sq_nonneg l, mul_pos hl0 hl0, mul_le_mul hl1 hl1 hl0.le zero_le_one]
    · exact bot_le
    · exact bot_le
  · simp

/-- **Hardy/Schur bound at `λ = 1`** (source 3996-4011): the kernel
`|y'| |y - z|^{-4} 1{e^δ |z'|² < |y'|²}` (`|y - z| ≥ (1-e^{-δ/2})|y'|` there) is bounded on `L²(ℝ³)`
(Schur test with a power weight, dyadic shells). -/
def SchurOne : Prop :=
  ∀ (R δ S : ℝ), 0 < R → 0 < δ → 0 < S →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Space → ℝ, Measurable g → (∀ z, 0 ≤ g z) →
      cartOut R δ S 1 g ≤ ENNReal.ofReal C ^ (2 : ℝ) * ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ)

theorem cartSchur_of (h : SchurOne) : CartSchur := by
  intro R δ S hR hδ hS
  obtain ⟨C, hC, hg⟩ := h R δ S hR hδ hS
  refine ⟨C, hC, fun l hl g hgm hg0 => ?_⟩
  obtain ⟨hl0, hl1⟩ := hl
  have hp : (0 : ℝ) < 2 := by norm_num
  set gl : Space → ℝ := fun w => g (l⁻¹ • w) with hgl
  have hglm : Measurable gl := hgm.comp (measurable_const_smul _)
  have hgl0 : ∀ z, 0 ≤ gl z := fun z => hg0 _
  have hdil : ∫⁻ w : Space, ENNReal.ofReal (gl w) ^ (2 : ℝ) =
      ENNReal.ofReal (l ^ (3 : ℝ)) * ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ) := by
    have := lintegral_smul_space l⁻¹ (inv_pos.2 hl0) (fun z => ENNReal.ofReal (g z) ^ (2 : ℝ))
    have e : l⁻¹ ^ (-3 : ℝ) = l ^ (3 : ℝ) := by
      rw [Real.inv_rpow hl0.le, Real.rpow_neg hl0.le, inv_inv]
    rw [this, e]
  calc cartOut R δ S l g
      = ∫⁻ y : Space, (cartSliceOut R δ S l g y) ^ (2 : ℝ) := rfl
    _ ≤ ∫⁻ y : Space, (ENNReal.ofReal (l ^ (-3 : ℝ)) * cartSliceOut R δ S 1 gl y) ^ (2 : ℝ) := by
        refine lintegral_mono fun y => ?_
        exact ENNReal.rpow_le_rpow (cartSliceOut_scale R δ S l hl0 hl1.le g y) hp.le
    _ = ENNReal.ofReal (l ^ (-3 : ℝ)) ^ (2 : ℝ) * cartOut R δ S 1 gl := by
        unfold cartOut
        rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    _ ≤ ENNReal.ofReal (l ^ (-3 : ℝ)) ^ (2 : ℝ) *
          (ENNReal.ofReal C ^ (2 : ℝ) * ∫⁻ w : Space, ENNReal.ofReal (gl w) ^ (2 : ℝ)) := by
        gcongr
        exact hg gl hglm hgl0
    _ = ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) *
          ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ) := by
        rw [hdil]
        have hk : ENNReal.ofReal (l ^ (-3 : ℝ)) ^ (2 : ℝ) * ENNReal.ofReal (l ^ (3 : ℝ)) =
            ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
            ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul hl0.le,
            ← Real.rpow_mul hl0.le, ← Real.rpow_add hl0]
          norm_num
        calc _ = (ENNReal.ofReal (l ^ (-3 : ℝ)) ^ (2 : ℝ) * ENNReal.ofReal (l ^ (3 : ℝ))) *
              (ENNReal.ofReal C ^ (2 : ℝ) * ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ)) := by ring
          _ = _ := by rw [hk]; ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
