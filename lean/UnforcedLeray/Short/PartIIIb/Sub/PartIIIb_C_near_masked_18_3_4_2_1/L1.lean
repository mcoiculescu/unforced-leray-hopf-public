import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `heatLerayKGradBound` (`PartIII-b:C/near/masked/18/3/4/2/1/1`)

Source 3594-3610 (`sep:kernel`).  For `|x|² ≥ t` the bound comes from `sepKernelBounds` at order
`0` (`|∇K_t(x)| ≤ C|x|^{-4} ≤ 4C(|x|²+t)^{-2}`).  For `|x|² < t` the parabolic scaling
`K_t(x) = t^{-3/2} K_1(x/√t)` (`heatLerayScale_of`) gives `|∇K_t(x)| = t^{-2}|∇K_1(x/√t)|`, and
`∇K_1` is bounded on the closed unit ball by continuity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open MeasureTheory Set Filter UnforcedLeray.Axi UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.Concrete

theorem heatLerayKGradBound :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.HeatLerayKGradBound := by
  have hS : HeatLerayScale := heatLerayScale_of heatGTailScale
  have hSm : HeatLerayKSmooth := heatLerayKSmooth
  obtain ⟨Cs, hCs⟩ := UnforcedLeray.Short.IIIa.sepKernelBounds 0
  -- bound of the first derivative of `K_1` on the closed unit ball
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space, ‖y‖ ≤ 1 → ∀ i j : Fin 3,
      ‖fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y‖ ≤ M := by
    have hcont : Continuous (fun y : Space => fun i j : Fin 3 =>
        fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (hSm 1 one_pos i j).continuous_fderiv (by norm_num)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun y hy i j => ?_⟩
    have h1 := hM y (by simpa using hy)
    have h2 : ‖fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y‖
        ≤ ‖(fun i j => fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y)‖ := by
      refine le_trans ?_ (norm_le_pi_norm (fun i : Fin 3 =>
        (fun j : Fin 3 => fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y)) i)
      exact norm_le_pi_norm (fun j : Fin 3 => fderiv ℝ (fun x => IIIa.heatLerayK 1 i j x) y) j
    linarith [le_max_left M 0]
  obtain ⟨M, hM0, hM⟩ := hbd
  refine ⟨4 * (|Cs| + M), fun t ht i j k x => ?_⟩
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsq2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hK1 : Differentiable ℝ (fun y => IIIa.heatLerayK 1 i j y) :=
    (hSm 1 one_pos i j).differentiable (by norm_num)
  have hnorm1 : ‖coordinateVector k‖ = 1 := by
    simp [coordinateVector]
  have hX : 0 ≤ ((‖x‖ ^ 2 + t) ^ 2)⁻¹ := by positivity
  by_cases hcase : ‖x‖ ^ 2 < t
  · -- case `|x|² < t`: parabolic scaling and the bound on the unit ball
    have hh : HasFDerivAt (fun y : Space => (Real.sqrt t)⁻¹ • y)
        ((Real.sqrt t)⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
      (ContinuousLinearMap.id ℝ Space).hasFDerivAt.const_smul ((Real.sqrt t)⁻¹)
    have hg : HasFDerivAt (fun y => IIIa.heatLerayK 1 i j y)
        (fderiv ℝ (fun y => IIIa.heatLerayK 1 i j y) ((Real.sqrt t)⁻¹ • x)) ((Real.sqrt t)⁻¹ • x) :=
      (hK1 _).hasFDerivAt
    have hcomp := (hg.comp x hh).const_mul (t ^ (-(3 / 2 : ℝ)))
    have hfun : (fun y => IIIa.heatLerayK t i j y)
        = fun y => t ^ (-(3 / 2 : ℝ)) * ((fun y => IIIa.heatLerayK 1 i j y) ∘
            (fun y : Space => (Real.sqrt t)⁻¹ • y)) y :=
      funext fun y => hS t ht i j y
    have hkey : fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)
        = (t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹) *
          fderiv ℝ (fun y => IIIa.heatLerayK 1 i j y) ((Real.sqrt t)⁻¹ • x) (coordinateVector k) := by
      rw [hfun, hcomp.fderiv]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
      ring
    -- the constant `t^{-3/2} (√t)^{-1} = (t^2)⁻¹`
    have hac : t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹ = (t ^ 2)⁻¹ := by
      have h32 : t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [Real.rpow_neg ht.le, h32]
      rw [show t ^ 2 = t * (Real.sqrt t * Real.sqrt t) by rw [hsq2]; ring]
      field_simp
    have hle : ‖x‖ ≤ Real.sqrt t := by
      calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
        _ ≤ Real.sqrt t := Real.sqrt_le_sqrt hcase.le
    have hy : ‖(Real.sqrt t)⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsq)]
      calc (Real.sqrt t)⁻¹ * ‖x‖ ≤ (Real.sqrt t)⁻¹ * Real.sqrt t :=
            mul_le_mul_of_nonneg_left hle (inv_pos.2 hsq).le
        _ = 1 := inv_mul_cancel₀ hsq.ne'
    have hL : |fderiv ℝ (fun y => IIIa.heatLerayK 1 i j y) ((Real.sqrt t)⁻¹ • x)
        (coordinateVector k)| ≤ M := by
      have h1 := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fun y => IIIa.heatLerayK 1 i j y) ((Real.sqrt t)⁻¹ • x)) (coordinateVector k)
      rw [hnorm1, mul_one] at h1
      have h3 := hM _ hy i j
      rw [← Real.norm_eq_abs]
      linarith
    have hden : (t ^ 2)⁻¹ ≤ 4 * ((‖x‖ ^ 2 + t) ^ 2)⁻¹ := by
      have h1 : (‖x‖ ^ 2 + t) ^ 2 ≤ 4 * t ^ 2 := by
        nlinarith [norm_nonneg x, sq_nonneg ‖x‖]
      have h2 : (4 * t ^ 2)⁻¹ ≤ ((‖x‖ ^ 2 + t) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) h1
      have h4 : (t ^ 2)⁻¹ = 4 * (4 * t ^ 2)⁻¹ := by rw [mul_inv]; ring
      rw [h4]
      linarith
    rw [hkey, abs_mul, hac, abs_of_pos (by positivity : (0 : ℝ) < (t ^ 2)⁻¹)]
    have hfinal : (t ^ 2)⁻¹ * |fderiv ℝ (fun y => IIIa.heatLerayK 1 i j y)
        ((Real.sqrt t)⁻¹ • x) (coordinateVector k)| ≤ (t ^ 2)⁻¹ * M :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have h5 : (t ^ 2)⁻¹ * M ≤ 4 * ((‖x‖ ^ 2 + t) ^ 2)⁻¹ * M :=
      mul_le_mul_of_nonneg_right hden hM0
    nlinarith [abs_nonneg Cs, le_abs_self Cs, mul_nonneg hM0 hX]
  · -- case `|x|² ≥ t`: the order-zero kernel bound
    push Not at hcase
    have hx : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hcase
      nlinarith
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hb := (hCs x hx i j).1 t ht
    rw [zero_add] at hb
    have he : |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)|
        ≤ ‖fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x‖ := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [hnorm1, mul_one]
    have hfd : ‖fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x‖ ≤ |Cs| * ‖x‖ ^ (-4 : ℝ) := by
      rw [← norm_iteratedFDeriv_one]
      refine hb.trans ?_
      have : ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) = ‖x‖ ^ (-4 : ℝ) := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_abs_self Cs) (by positivity)
    have hr4 : ‖x‖ ^ (-4 : ℝ) = (‖x‖ ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]
    have hden : (‖x‖ ^ 4)⁻¹ ≤ 4 * ((‖x‖ ^ 2 + t) ^ 2)⁻¹ := by
      have h1 : (‖x‖ ^ 2 + t) ^ 2 ≤ 4 * ‖x‖ ^ 4 := by nlinarith
      have h2 : (4 * ‖x‖ ^ 4)⁻¹ ≤ ((‖x‖ ^ 2 + t) ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
      have h4 : (‖x‖ ^ 4)⁻¹ = 4 * (4 * ‖x‖ ^ 4)⁻¹ := by rw [mul_inv]; ring
      rw [h4]
      linarith
    have hfin : |Cs| * ‖x‖ ^ (-4 : ℝ) ≤ |Cs| * (4 * ((‖x‖ ^ 2 + t) ^ 2)⁻¹) := by
      rw [hr4]
      exact mul_le_mul_of_nonneg_left hden (abs_nonneg _)
    nlinarith [abs_nonneg Cs, mul_nonneg hM0 hX]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
