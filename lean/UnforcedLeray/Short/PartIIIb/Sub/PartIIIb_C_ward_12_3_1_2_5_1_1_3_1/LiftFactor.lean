import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Homog
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# `LiftFactorJet` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/6`)

Source `the November 2 reference manuscript`,
lines 1212-1216 (`u = (R/r)(v₁ e_r + ...)`). The lift factor is `liftFactor R y = √(age R y) • frameL y`.
Off the axis `√(age R y) = R/ϱ y` (`Axi.sqrt_age`), so the factor is homogeneous of degree `-1`
and axially invariant. Order `0` is the operator-norm bound `‖frameL y‖ ≤ 1`; orders `≥ 1` come
from `homogJets` with `d = -1`, `g = 0`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem liftFactorJet : LiftFactorJet := by
  intro R hR m
  have hR0 : R ≠ 0 := hR.ne'
  -- the age is smooth off the axis
  have hA : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => R ^ 2 / Axi.ϱ y ^ 2) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun y hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
  have hAge : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ := hA
  -- the frame is smooth off the axis
  have hFr : ContDiffOn ℝ ∞ Axi.frameL Axi.axisᶜ := by
    show ContDiffOn ℝ ∞
      (fun y : UnforcedLeray.Space =>
        (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight (Axi.eR y) +
          (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight Axi.e3) Axi.axisᶜ
    exact (contDiffOn_const.smulRight Axi.contDiffOn_eR).add
      (contDiffOn_const.smulRight contDiffOn_const)
  have hf : ContDiffOn ℝ ∞ (liftFactor R) Axi.axisᶜ := by
    have hS : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => √(Axi.age R y)) Axi.axisᶜ :=
      ContDiffOn.sqrt hAge (fun y hy => (Axi.age_pos hR0 hy).ne')
    unfold liftFactor
    exact hS.smul hFr
  -- axial invariance
  have hinv : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ,
      liftFactor R (y + t • Axi.e3) = liftFactor R y := by
    intro y hy t
    have hϱ : Axi.ϱ (y + t • Axi.e3) = Axi.ϱ y := by
      unfold Axi.ϱ
      simp [Axi.e3_apply]
    have hhor : Axi.hor (y + t • Axi.e3) = Axi.hor y := by
      rw [Axi.hor_eq, Axi.hor_eq]
      have h2 : (y + t • Axi.e3) 2 = y 2 + t := by simp [Axi.e3_apply]
      rw [h2]
      module
    have heR : Axi.eR (y + t • Axi.e3) = Axi.eR y := by
      unfold Axi.eR
      rw [hϱ, hhor]
    have hfr : Axi.frameL (y + t • Axi.e3) = Axi.frameL y := by
      unfold Axi.frameL
      rw [heR]
    have hage : Axi.age R (y + t • Axi.e3) = Axi.age R y := by
      unfold Axi.age
      rw [hϱ]
    unfold liftFactor
    rw [hage, hfr]
  -- homogeneity of degree -1
  have hsc : ∀ lam : ℝ, 0 < lam → ∀ z : UnforcedLeray.Space, z ∉ Axi.axis →
      liftFactor R (lam • z) = lam ^ (-1 : ℝ) • liftFactor R z + 0 := by
    intro lam hlam z hz
    have hlz : lam • z ∉ Axi.axis := hjSmulOff hlam hz
    have hz0 : Axi.ϱ z ≠ 0 := Axi.ϱ_ne_zero hz
    have hϱ : Axi.ϱ (lam • z) = lam * Axi.ϱ z := by
      rw [Axi.ϱ_smul, abs_of_pos hlam]
    unfold liftFactor
    rw [Axi.sqrt_age hR hlz, Axi.sqrt_age hR hz, Axi.frameL_smul hlam z, Real.rpow_neg_one,
      add_zero, smul_smul, hϱ]
    congr 1
    field_simp
  -- the order-zero bound
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · refine ⟨R, hR.le, fun y hy => ?_⟩
    subst hm0
    rw [norm_iteratedFDeriv_zero]
    have hop : ‖Axi.frameL y‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
      rw [one_mul, Axi.norm_frameL hy v]
    have hn : ‖liftFactor R y‖ ≤ R / Axi.ϱ y := by
      unfold liftFactor
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), Axi.sqrt_age hR hy]
      calc R / Axi.ϱ y * ‖Axi.frameL y‖ ≤ R / Axi.ϱ y * 1 :=
            mul_le_mul_of_nonneg_left hop (by have := Axi.ϱ_pos hy; positivity)
        _ = R / Axi.ϱ y := mul_one _
    rw [show -(1 + ((0 : ℕ) : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
    calc ‖liftFactor R y‖ ≤ R / Axi.ϱ y := hn
      _ = R * (Axi.ϱ y)⁻¹ := div_eq_mul_inv _ _
  · obtain ⟨C, hC0, hCb⟩ :=
      homogJets (Axi.Merid →L[ℝ] UnforcedLeray.Space) (liftFactor R) (-1) (fun _ => 0) hf hinv
        hsc m hmpos
    refine ⟨C, hC0, fun y hy => ?_⟩
    have h := hCb y hy
    rw [show (-1 : ℝ) - (m : ℝ) = -(1 + (m : ℝ)) by ring] at h
    exact h

end UnforcedLeray.Short.PartIIIb.Concrete
