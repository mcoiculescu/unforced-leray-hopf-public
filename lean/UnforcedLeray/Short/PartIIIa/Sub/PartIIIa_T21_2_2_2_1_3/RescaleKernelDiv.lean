import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.Dil
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# `PartIII-a:T21/2/2/2/1/3` leaf `RescaleKernelDiv` (SP 2875-2896, 3052-3057)

The divergence clause of the kernel Biot-Savart velocity. For a test `φ` of the cell `c`, the
dilation `φ̃(z) = φ(√a z)` is a test of the cell `c/√a` (`Dil.isCylTest_dilate`) with
`∂_k φ̃(z) = √a (∂_k φ)(√a z)` (`Dil.pd_dilate`). The integrand of the target is `G`, and
`G(√a y) = u(y)·∇φ̃(y)`, so the change of variables `ChangeVar.integral_cell_scale` transfers
the vanishing.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
open UnforcedLeray
open UnforcedLeray.Short.IIIa

theorem rescaleKernelDiv : UnforcedLeray.Short.IIIa.E0.RescaleKernelDiv := by
  intro c a hc ha u hu φ hφ
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hφ' := UnforcedLeray.Short.IIIa.E0.RsDil.isCylTest_dilate hs hφ
  have hk := hu _ hφ'
  set G : ℝ × ℝ → ℝ := fun x =>
    Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0 * B0579.pd 0 φ x +
      Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1 * B0579.pd 1 φ x with hG
  have hpt : ∀ y : ℝ × ℝ, G (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      u y 0 * B0579.pd 0 (fun z : ℝ × ℝ => φ (Real.sqrt a * z.1, Real.sqrt a * z.2)) y +
        u y 1 * B0579.pd 1 (fun z : ℝ × ℝ => φ (Real.sqrt a * z.1, Real.sqrt a * z.2)) y := by
    intro y
    rw [UnforcedLeray.Short.IIIa.E0.RsDil.pd_dilate _ 0 φ hφ.differentiable y,
      UnforcedLeray.Short.IIIa.E0.RsDil.pd_dilate _ 1 φ hφ.differentiable y]
    simp only [hG]
    rw [mul_div_cancel_left₀ _ hs.ne', mul_div_cancel_left₀ _ hs.ne']
    ring
  have hfunEq : (fun y : ℝ × ℝ => G (Real.sqrt a * y.1, Real.sqrt a * y.2)) =
      fun y : ℝ × ℝ => u y 0 * B0579.pd 0 (fun z : ℝ × ℝ => φ (Real.sqrt a * z.1, Real.sqrt a * z.2)) y +
        u y 1 * B0579.pd 1 (fun z : ℝ × ℝ => φ (Real.sqrt a * z.1, Real.sqrt a * z.2)) y :=
    funext hpt
  have hk2 : ∫ y in B0579.cell (cellLen c a), G (Real.sqrt a * y.1, Real.sqrt a * y.2) = 0 := by
    rw [hfunEq]
    exact hk
  have hcv := UnforcedLeray.Short.IIIa.integral_cell_scale c a ha G
  rw [hk2] at hcv
  have hinv : a⁻¹ ≠ 0 := inv_ne_zero ha.ne'
  have hI := (mul_eq_zero.mp hcv.symm).resolve_left hinv
  exact hI
