import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Homog
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# `AgeJet` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/2`)

Source `the November 2 reference manuscript`,
lines 1208-1210: `s = R²/ϱ²`, homogeneous of degree `-2`, axially invariant, smooth off the axis.
Proved by `homogJets` with `f = Axi.age R`, `d = -2`, `g = 0`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageJet : AgeJet := by
  intro R hR m hm
  have hR0 : R ≠ 0 := hR.ne'
  have hf : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ := by
    have hA : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => R ^ 2 / Axi.ϱ y ^ 2) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun y hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
    exact hA
  have hinv : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ,
      Axi.age R (y + t • Axi.e3) = Axi.age R y := by
    intro y hy t
    have hϱ : Axi.ϱ (y + t • Axi.e3) = Axi.ϱ y := by
      unfold Axi.ϱ
      simp [Axi.e3_apply]
    unfold Axi.age
    rw [hϱ]
  have hsc : ∀ lam : ℝ, 0 < lam → ∀ z : UnforcedLeray.Space, z ∉ Axi.axis →
      Axi.age R (lam • z) = lam ^ (-2 : ℝ) • Axi.age R z + 0 := by
    intro lam hlam z hz
    have hz0 : Axi.ϱ z ≠ 0 := Axi.ϱ_ne_zero hz
    have hϱ : Axi.ϱ (lam • z) = lam * Axi.ϱ z := by
      rw [Axi.ϱ_smul, abs_of_pos hlam]
    have hexp : lam ^ (-2 : ℝ) = (lam ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    unfold Axi.age
    rw [hϱ, hexp, add_zero, smul_eq_mul]
    field_simp
  obtain ⟨C, hC0, hCb⟩ := homogJets ℝ (Axi.age R) (-2) (fun _ => 0) hf hinv hsc m hm
  refine ⟨C, hC0, fun y hy => ?_⟩
  have h := hCb y hy
  rw [show (-2 : ℝ) - (m : ℝ) = -(2 + (m : ℝ)) by ring] at h
  exact h

end UnforcedLeray.Short.PartIIIb.Concrete
