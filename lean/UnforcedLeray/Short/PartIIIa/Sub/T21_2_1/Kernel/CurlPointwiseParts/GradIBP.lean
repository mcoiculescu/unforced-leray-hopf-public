import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6
import UnforcedLeray.Units.B0579

/-!
# `KerGradIBP`: gradient integration by parts on the cell (SP 2081-2084, 3121)

For `G` smooth and `d`-periodic in `q`, and a cylinder test `φ`, each coordinate gives
`∫_cell ∂_jG ∂_jφ = -∫_cell ∂_j∂_jG φ`.  Proof: `P := ∂_jG` is smooth and periodic, so
`P φ` is a cylinder test; its `∂_j` integrates to zero, and the product rule splits it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Product of a smooth `d`-periodic function with a cylinder test is a cylinder test. -/
theorem mul_test_of_periodic {d : ℝ} {H φ : B0579.Plane → ℝ} (hH : ContDiff ℝ ∞ H)
    (hHp : ∀ x : B0579.Plane, H (x.1 + d, x.2) = H x) (hφ : B0579.IsCylTest d φ) :
    B0579.IsCylTest d (fun x => H x * φ x) where
  smooth := hH.mul hφ.smooth
  periodic x := by
    show H (x.1 + d, x.2) * φ (x.1 + d, x.2) = H x * φ x
    rw [hHp x, hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by
      show H x * φ x = 0
      rw [hR x hx, mul_zero]⟩

/-- A smooth `d`-periodic function has `d`-periodic partial derivatives. -/
theorem pd_periodic_of_periodic {d : ℝ} {H : B0579.Plane → ℝ}
    (hHp : ∀ x : B0579.Plane, H (x.1 + d, x.2) = H x) (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j H (x.1 + d, x.2) = B0579.pd j H x := by
  have hfun : (fun y : B0579.Plane => H (y + ((d, 0) : B0579.Plane))) = H := by
    funext y
    have hy : y + ((d, 0) : B0579.Plane) = (y.1 + d, y.2) := by ext <;> simp
    rw [hy]
    exact hHp y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := H) (x := x) ((d, 0) : B0579.Plane)
  rw [hfun] at h
  have hx : x + ((d, 0) : B0579.Plane) = (x.1 + d, x.2) := by ext <;> simp
  rw [hx] at h
  simp only [B0579.pd]
  rw [← h]

/-- One coordinate of the gradient integration by parts. -/
theorem gradIBP_one {d : ℝ} {G : B0579.Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGp : ∀ z : B0579.Plane, G (z.1 + d, z.2) = G z) (j : Fin 2)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest d φ) :
    ∫ x in B0579.cell d, B0579.pd j G x * B0579.pd j φ x =
      -∫ x in B0579.cell d, B0579.pd j (B0579.pd j G) x * φ x := by
  have hP : ContDiff ℝ ∞ (B0579.pd j G) := B0579.contDiff_pd hG j
  have hPp : ∀ x : B0579.Plane, B0579.pd j G (x.1 + d, x.2) = B0579.pd j G x :=
    pd_periodic_of_periodic hGp j
  have hQ : B0579.IsCylTest d (fun x => B0579.pd j G x * φ x) :=
    mul_test_of_periodic hP hPp hφ
  have hPP : ContDiff ℝ ∞ (B0579.pd j (B0579.pd j G)) := B0579.contDiff_pd hP j
  have hPPp : ∀ x : B0579.Plane, B0579.pd j (B0579.pd j G) (x.1 + d, x.2) =
      B0579.pd j (B0579.pd j G) x :=
    pd_periodic_of_periodic hPp j
  have hS : B0579.IsCylTest d (fun x => B0579.pd j (B0579.pd j G) x * φ x) :=
    mul_test_of_periodic hPP hPPp hφ
  have hT : B0579.IsCylTest d (fun x => B0579.pd j G x * B0579.pd j φ x) :=
    mul_test_of_periodic hP hPp (hφ.pd j)
  have i1 : IntegrableOn (fun x => B0579.pd j (B0579.pd j G) x * φ x) (B0579.cell d) :=
    hS.integrableOn
  have i2 : IntegrableOn (fun x => B0579.pd j G x * B0579.pd j φ x) (B0579.cell d) :=
    hT.integrableOn
  have hprod : ∀ x : B0579.Plane,
      B0579.pd j (fun y => B0579.pd j G y * φ y) x =
        B0579.pd j (B0579.pd j G) x * φ x + B0579.pd j G x * B0579.pd j φ x :=
    fun x => B0579.pd_mul (hP.differentiable (by simp)) hφ.differentiable j x
  have h0 := B0579.integral_pd_eq_zero hQ j
  simp only [hprod] at h0
  rw [integral_add i1 i2] at h0
  linarith

/-- **Gradient integration by parts** (`KerGradIBP`, SP 2081-2084, 3121). -/
theorem kerGradIBP : UnforcedLeray.Short.IIIa.KerGradIBP := by
  intro d _hd G hG hGp φ hφ
  have a0 := gradIBP_one hG hGp 0 hφ
  have a1 := gradIBP_one hG hGp 1 hφ
  have b0 : IntegrableOn (fun x => B0579.pd 0 G x * B0579.pd 0 φ x) (B0579.cell d) :=
    (mul_test_of_periodic (B0579.contDiff_pd hG 0) (pd_periodic_of_periodic hGp 0)
      (hφ.pd 0)).integrableOn
  have b1 : IntegrableOn (fun x => B0579.pd 1 G x * B0579.pd 1 φ x) (B0579.cell d) :=
    (mul_test_of_periodic (B0579.contDiff_pd hG 1) (pd_periodic_of_periodic hGp 1)
      (hφ.pd 1)).integrableOn
  have c0 : IntegrableOn (fun x => B0579.pd 0 (B0579.pd 0 G) x * φ x) (B0579.cell d) :=
    (mul_test_of_periodic (B0579.contDiff_pd (B0579.contDiff_pd hG 0) 0)
      (pd_periodic_of_periodic (pd_periodic_of_periodic hGp 0) 0) hφ).integrableOn
  have c1 : IntegrableOn (fun x => B0579.pd 1 (B0579.pd 1 G) x * φ x) (B0579.cell d) :=
    (mul_test_of_periodic (B0579.contDiff_pd (B0579.contDiff_pd hG 1) 1)
      (pd_periodic_of_periodic (pd_periodic_of_periodic hGp 1) 1) hφ).integrableOn
  have hL := integral_add b0 b1
  have hR : ∫ x in B0579.cell d, (B0579.pd 0 (B0579.pd 0 G) x + B0579.pd 1 (B0579.pd 1 G) x) * φ x
      = (∫ x in B0579.cell d, B0579.pd 0 (B0579.pd 0 G) x * φ x) +
        (∫ x in B0579.cell d, B0579.pd 1 (B0579.pd 1 G) x * φ x) := by
    simp only [add_mul]
    exact integral_add c0 c1
  linarith

end UnforcedLeray.Short.IIIa
