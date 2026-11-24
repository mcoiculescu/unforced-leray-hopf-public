import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest.RotEquiv.BoxInt

/-!
# Rotation equivariance of `sepW` (source 3586-3626, 2683)

The target `SepWRotEquiv` is reduced to the existing `sepWEquivariance` (`K2`), which needs the
integrability of the `sepW` integrand at the reference point `y₀ = (ϱ, 0, y₂)`.  That
integrability is the hypothesis `SepBoxIntegrable` (Sub file `PartIII-b_C_near_masked_18_3_4_2`).  The
rotation `Q = cylFrame y = rotM (y₀/ϱ) (y₁/ϱ)` maps `y₀` to `y`, and `cartLift` is equivariant for
every rotation about the vertical axis (`cartLift (Qz) = Q cartLift(z) Qᵀ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift chartOf cylFrame hRad nsSym IsBoxTensor)

lemma hRad_rot {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (z : Space) :
    hRad (actM (rotM co si) z) = hRad z := by
  have e0 : actM (rotM co si) z 0 = co * z 0 - si * z 1 := by
    simp [actM_apply, rotM, Fin.sum_univ_three, sub_eq_add_neg]
  have e1 : actM (rotM co si) z 1 = si * z 0 + co * z 1 := by
    simp [actM_apply, rotM, Fin.sum_univ_three]
  unfold hRad
  rw [e0, e1]
  congr 1
  linear_combination (z 0 ^ 2 + z 1 ^ 2) * h

lemma cylFrame_rot {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (z : Space) :
    cylFrame (actM (rotM co si) z) = rotM co si * cylFrame z := by
  have hr := hRad_rot h z
  have e0 : actM (rotM co si) z 0 = co * z 0 - si * z 1 := by
    simp [actM_apply, rotM, Fin.sum_univ_three, sub_eq_add_neg]
  have e1 : actM (rotM co si) z 1 = si * z 0 + co * z 1 := by
    simp [actM_apply, rotM, Fin.sum_univ_three]
  unfold cylFrame
  rw [hr, e0, e1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotM, sub_eq_add_neg] <;> ring

lemma cartLift_rot {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (R c : ℝ) (m : Chart → Ten3) (τ : ℝ)
    (z : Space) :
    cartLift R c m τ (actM (rotM co si) z) =
      rotM co si * cartLift R c m τ z * (rotM co si).transpose := by
  have hr := hRad_rot h z
  have e2 : actM (rotM co si) z 2 = z 2 := by
    simp [actM_apply, rotM, Fin.sum_univ_three]
  have hch : chartOf R c (actM (rotM co si) z) τ = chartOf R c z τ := by
    unfold chartOf
    rw [hr, e2]
  unfold cartLift
  rw [hch, cylFrame_rot h z, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The reduction of `SepWRotEquiv` to the integrability hypothesis. -/
theorem sepW_rot_equiv_of_integrable (hI : SepBoxIntegrable) (ν R c μ : ℝ) (hν : 0 < ν)
    (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4 : ℝ) < μ) (m : Chart → Ten3) (hm : IsBoxTensor m)
    (τ : ℝ) (y : Space) (hy : 0 < hRad y) :
    IIIa.sepW ν (μ : ℂ) (cartLift R c m) y τ =
      fun i => ∑ j : Fin 3, ((cylFrame y i j : ℝ) : ℂ) *
        IIIa.sepW ν (μ : ℂ) (cartLift R c m) (WithLp.toLp 2 ![hRad y, 0, y 2]) τ j := by
  have hne : hRad y ≠ 0 := hy.ne'
  have hsq : hRad y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hcs : (y 0 / hRad y) ^ 2 + (y 1 / hRad y) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hsq, div_self (pow_ne_zero 2 hne)]
  have hQy : actM (rotM (y 0 / hRad y) (y 1 / hRad y)) (WithLp.toLp 2 ![hRad y, 0, y 2]) = y := by
    ext i
    fin_cases i <;> simp [actM_apply, rotM, Fin.sum_univ_three] <;> field_simp
  have hy0 : 0 < hRad (WithLp.toLp 2 ![hRad y, 0, y 2] : Space) := by
    have h0 : (WithLp.toLp 2 ![hRad y, 0, y 2] : Space) 0 = hRad y := by simp
    have h1 : (WithLp.toLp 2 ![hRad y, 0, y 2] : Space) 1 = 0 := by simp
    show 0 < Real.sqrt ((WithLp.toLp 2 ![hRad y, 0, y 2] : Space) 0 ^ 2 +
      (WithLp.toLp 2 ![hRad y, 0, y 2] : Space) 1 ^ 2)
    rw [h0, h1]
    apply Real.sqrt_pos.2
    positivity
  have hsep := sepWEquivariance (rotM (y 0 / hRad y) (y 1 / hRad y)) (rotM_orth hcs) ν (μ : ℂ)
    (cartLift R c m) (fun τ' z => cartLift_rot hcs R c m τ' z) (WithLp.toLp 2 ![hRad y, 0, y 2])
    τ (hI ν R c μ hν hR hc hμ m hm τ _ hy0)
  rw [hQy] at hsep
  exact hsep

/-- `SepWRotEquiv` from the integrability leaf. -/
theorem sepW_rot_equiv_of_box (hI : SepBoxIntegrable) : SepWRotEquiv :=
  fun ν R c μ hν hR hc hμ m hm τ y hy =>
    sepW_rot_equiv_of_integrable hI ν R c μ hν hR hc hμ m hm τ y hy

/-- `SepWRotEquiv` (task `PartIII-b:C/near/masked/18/3/4/2`), from the proved box integrability. -/
theorem sepW_rot_equiv : SepWRotEquiv :=
  sepW_rot_equiv_of_box sepBoxIntegrable

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
