import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_swirl_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_swirl_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.BodyError
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.AgeError
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.AgeVelocity
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ThinComplete
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.AffineRemainder
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ThinMoment
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.NearBody
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.BodyRepairMargin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ThinBodyMargin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.AffRemMargin

/-!
# `PartIII-b:IIIb-D4`: `ErrorFamilyBounds` for the concrete return sequence

Source of record: `the November 2 reference manuscript`, lines 5607–5627, 5687–5697.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem errorFamilyBounds_concrete (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
        ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl)
          ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) D.K.m0 := by
  obtain ⟨k₁, hk₁⟩ := ageError Pl σ₀ mZ dm dp
  obtain ⟨k₂, hk₂⟩ := ageVelocity Pl σ₀ mZ dm dp
  refine ⟨k₁ + k₂, fun D hPl hσ₀ hmZ hst G => ?_⟩
  have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) :=
    mul_nonneg hst.b_pos.le (div_nonneg hst.gamma_pos.le (by norm_num))
  have hle₁ : (k₁ : ℝ) * D.K.b * (gRate D.Pl / 3) ≤
      ((k₁ + k₂ : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_add_right k₁ k₂)) hbg
  have hle₂ : (k₂ : ℝ) * D.K.b * (gRate D.Pl / 3) ≤
      ((k₁ + k₂ : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_add_left k₂ k₁)) hbg
  have hωb : 0 ≤ ((k₁ + k₂ : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    rw [mul_assoc]
    exact mul_nonneg (Nat.cast_nonneg _) hbg
  have h4 := D.ageError_mono hle₁ (hk₁ D hPl hσ₀ hmZ hst)
  have h4v := D.ageVelocity_mono hle₂ (hk₂ D hPl hσ₀ hmZ hst)
  have h5 := bodyRepairMargin D hst (bodyError D hst)
  have h6 := thinBodyMargin D hst (thinComplete D hst) (thinMoment D hst)
  have h7 := affRemMargin D hst (affineRemainder D hst) (thinMoment D hst)
  have hB := nearBody D hst
  have hM : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ w : LVel D.Pl (D.level n),
      ThinAziZero D.Pl D.K (D.level n) (multOp D.Pl D.K (D.level n) w) := by
    filter_upwards [hst.pins] with n hp z hz w
    exact multOp_thinAziZero D.Pl D.K (D.level n) (hp z hz).split w
  exact errorFamilyBoundsAzi_of D G hst.gamma_pos.le hωb hst.m0_pos.le hst.omega_ne
    hst.near h4 h4v h5 h6 h7 hB hM

end UnforcedLeray.Short.PartIIIb.Concrete
