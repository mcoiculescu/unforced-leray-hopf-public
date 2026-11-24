import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3

/-!
# Scaling of the heat-Leray kernel (`PartIII-b:IIIb-D2/3/1/1/2/3/2`)

Source `the November 2 reference manuscript`
3600-3610.  `IIIa.heatLerayK t i j = δ_{ij} heatG t + part2 (heatTail t) i j`
(`SeparatedKernels.lean:41-46`); the scaling of `heatG` and `heatTail` is the hypothesis `h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem heatLerayScale_of (h : HeatGTailScale) : HeatLerayScale := by
  intro t ht i j x
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hc : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hsq
  have hcc : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = t⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ht.le]
  have hpow : t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) * t⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) + -1 by norm_num, Real.rpow_add ht, Real.rpow_neg_one]
  have hA : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have hT : ∀ y, IIIa.heatTail t y
      = t ^ (-(1 / 2 : ℝ)) * IIIa.heatTail 1 ((Real.sqrt t)⁻¹ • y) := fun y => (h t ht y).2
  have hG : ∀ y, IIIa.heatG t y
      = t ^ (-(3 / 2 : ℝ)) * IIIa.heatG 1 ((Real.sqrt t)⁻¹ • y) := fun y => (h t ht y).1
  set c : ℝ := (Real.sqrt t)⁻¹ with hc_def
  set A : ℝ := t ^ (-(1 / 2 : ℝ)) with hA_def
  have : Invertible (A * c) := invertibleOfNonzero (mul_pos hA hc).ne'
  have : Invertible A := invertibleOfNonzero hA.ne'
  -- derivative of the scaled tail
  have hfd : ∀ y v, fderiv ℝ (IIIa.heatTail t) y v
      = (A * c) * fderiv ℝ (IIIa.heatTail 1) (c • y) v := by
    intro y v
    have e1 : IIIa.heatTail t = A • (fun z => IIIa.heatTail 1 (c • z)) :=
      funext fun z => hT z
    have e2 : fderiv ℝ (IIIa.heatTail t) y
        = A • fderiv ℝ (fun z => IIIa.heatTail 1 (c • z)) y := by
      rw [e1]
      exact fderiv_const_smul_of_invertible A
    have e3 : fderiv ℝ (fun z => IIIa.heatTail 1 (c • z)) y
        = c • fderiv ℝ (IIIa.heatTail 1) (c • y) :=
      fderiv_comp_smul c
    rw [e2, e3]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- second partial of the scaled tail
  have hpart2 : IIIa.part2 (IIIa.heatTail t) i j x
      = (A * c) * c * IIIa.part2 (IIIa.heatTail 1) i j (c • x) := by
    unfold IIIa.part2
    have e4 : (fun y => fderiv ℝ (IIIa.heatTail t) y (coordinateVector j))
        = (A * c) • (fun y => fderiv ℝ (IIIa.heatTail 1) (c • y) (coordinateVector j)) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hfd y _
    have e5 : fderiv ℝ (fun y => fderiv ℝ (IIIa.heatTail 1) (c • y) (coordinateVector j)) x
        = c • fderiv ℝ (fun w => fderiv ℝ (IIIa.heatTail 1) w (coordinateVector j)) (c • x) :=
      fderiv_comp_smul (f := fun w => fderiv ℝ (IIIa.heatTail 1) w (coordinateVector j)) c
    rw [e4, fderiv_const_smul_of_invertible (A * c), e5]
    simp only [smul_apply, smul_eq_mul]
    ring
  have hite : (if i = j then IIIa.heatG t x else 0)
      = t ^ (-(3 / 2 : ℝ)) * (if i = j then IIIa.heatG 1 (c • x) else 0) := by
    split_ifs
    · exact hG x
    · simp
  have hcoef : t ^ (-(3 / 2 : ℝ)) = (A * c) * c := by
    rw [hpow, ← hcc]
    ring
  unfold IIIa.heatLerayK
  rw [hite, hpart2, hcoef]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
