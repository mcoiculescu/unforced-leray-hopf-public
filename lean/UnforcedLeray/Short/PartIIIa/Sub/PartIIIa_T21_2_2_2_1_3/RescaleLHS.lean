import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1/3/6`: the left side `RescaleLHS` of the adjoint identity

Source `the November 2 reference manuscript` (SP), lines 3052-3058.
The complex-valued version of `integral_cell_scale` (same proof, via
`Measure.setIntegral_comp_smul_of_pos`) gives `∫_{C_{c/√a}} G(√a y) dy = a⁻¹ ∫_{C_c} G`,
and `a⁻¹ · a = 1` cancels the factor `a` in the integrand.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- Change of variables `x = √a y` on the moving cell, for a complex-valued integrand. -/
theorem rescaleLHS_cellScaleC (c a : ℝ) (ha : 0 < a) (G : ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell (cellLen c a), G (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell c, G x := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (ℝ × ℝ))) G
    (B0579.cell (cellLen c a)) hs
  rw [sqrt_smul_cell c a ha] at h
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, Real.sq_sqrt ha.le, Complex.real_smul] at h
  exact h

/-- **`RescaleLHS`** (SP 3052-3058): `∫_{C_{c/√a}} a χ(√a y) ψ(y) dy = ∫_{C_c} χ(x) ψ(x/√a) dx`. -/
theorem rescaleLHS : UnforcedLeray.Short.IIIa.E0.RescaleLHS := by
  intro c a hc ha χ ψ
  have hsne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hA := rescaleLHS_cellScaleC c a ha
    (fun x => (a : ℂ) * χ x * (ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) : ℂ))
  simp only [mul_div_cancel_left₀ _ hsne, Prod.mk.eta] at hA
  rw [hA]
  have hinv : ((a⁻¹ : ℝ) : ℂ) * (a : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hac
  simp only [mul_assoc]
  rw [integral_const_mul, ← mul_assoc, hinv, one_mul]

end UnforcedLeray.Short.IIIa.E0
