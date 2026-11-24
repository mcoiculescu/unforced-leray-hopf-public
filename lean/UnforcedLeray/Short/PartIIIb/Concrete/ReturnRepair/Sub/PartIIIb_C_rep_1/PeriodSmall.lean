import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed

/-!
# Leaf `PeriodSmall` (`PartIII-b:C/rep/1/6`, source 2031-2037, 4109-4124)

`2 ε_n c_n ≤ 1` for large `n`, where `ε_n = retEps`, `c_n = ν_n⁻²`.
We cube the quantity: `(2 ε c)³ = (8/(2|𝒞|)) · x^{6-r} e^{-γ x}` with `x = ν⁻¹`, which tends to `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The cube of `2 ε c` with `ε = (e^{-γ/ν} ν^r / (2C))^{1/3}` and `c = (ν²)⁻¹`. -/
theorem periodSmall_cube_eq (γ r C ν : ℝ) (hν : 0 < ν) (hC : 0 < C) :
    (2 * ((Real.exp (-(γ / ν)) * ν ^ r / (2 * C)) ^ (1 / 3 : ℝ)) * (ν ^ 2)⁻¹) ^ 3
      = (8 / (2 * C)) * ((ν⁻¹) ^ (6 - r) * Real.exp (-γ * ν⁻¹)) := by
  have hB : 0 ≤ Real.exp (-(γ / ν)) * ν ^ r / (2 * C) := by
    have h1 : 0 < ν ^ r := Real.rpow_pos_of_pos hν r
    have h2 : 0 < Real.exp (-(γ / ν)) := Real.exp_pos _
    have h3 : 0 < 2 * C := by linarith
    exact div_nonneg (mul_nonneg h2.le h1.le) h3.le
  have h3 : ((Real.exp (-(γ / ν)) * ν ^ r / (2 * C)) ^ (1 / 3 : ℝ)) ^ 3
      = Real.exp (-(γ / ν)) * ν ^ r / (2 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    norm_num
  have key : (2 * ((Real.exp (-(γ / ν)) * ν ^ r / (2 * C)) ^ (1 / 3 : ℝ)) * (ν ^ 2)⁻¹) ^ 3
      = 8 * (((Real.exp (-(γ / ν)) * ν ^ r / (2 * C)) ^ (1 / 3 : ℝ)) ^ 3) * ((ν ^ 2)⁻¹) ^ 3 := by
    ring
  rw [key, h3]
  have hν6 : ν ^ (6 - r) = ν ^ (6 : ℝ) / ν ^ r := Real.rpow_sub hν 6 r
  have h6 : ν ^ (6 : ℝ) = ν ^ 6 := by exact_mod_cast Real.rpow_natCast ν 6
  have he : -(γ / ν) = -γ * ν⁻¹ := by ring
  rw [Real.inv_rpow hν.le, hν6, h6, he]
  have hνr : 0 < ν ^ r := Real.rpow_pos_of_pos hν r
  have hν6' : 0 < ν ^ 6 := pow_pos hν 6
  field_simp

/-- **Leaf `PeriodSmall`** (source 2031-2037, 4109-4124): `P_n = 2 ε_n c_n ≤ 1` for large `n`. -/
theorem periodSmall : UnforcedLeray.Short.PartIIIb.Concrete.PeriodSmall := by
  intro D dm dp hst
  have hω : D.Pl.eigenvalue.im ≠ 0 := hst.omega_ne
  have hγ : 0 < D.Pl.eigenvalue.re := hst.gamma_pos
  have hC : 0 < ‖D.Pl.signedCoeff D.σ₀‖ := norm_pos_iff.2 D.coeff_ne
  have hνT : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto D.σ₀ hω, Eventually.of_forall fun n => retNu_pos D.Pl D.σ₀ n⟩
  have hxT : Tendsto (fun n : ℕ => (retNu D.Pl D.σ₀ n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hνT
  have hG : Tendsto (fun x : ℝ => x ^ (6 - (D.Pl.kappa.re - 5 - 2 * D.σ₀)) *
      Real.exp (-D.Pl.eigenvalue.re * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hγ
  have h3 : Tendsto (fun n : ℕ => (8 / (2 * ‖D.Pl.signedCoeff D.σ₀‖)) *
      ((retNu D.Pl D.σ₀ n)⁻¹ ^ (6 - (D.Pl.kappa.re - 5 - 2 * D.σ₀)) *
        Real.exp (-D.Pl.eigenvalue.re * (retNu D.Pl D.σ₀ n)⁻¹))) atTop (𝓝 0) := by
    have h := (hG.comp hxT).const_mul (8 / (2 * ‖D.Pl.signedCoeff D.σ₀‖))
    rw [mul_zero] at h
    exact h
  have hT3 : Tendsto (fun n : ℕ => (2 * (D.level n).ε * cOf (D.level n).ν) ^ 3) atTop (𝓝 0) := by
    refine h3.congr (fun n => ?_)
    exact (periodSmall_cube_eq D.Pl.eigenvalue.re (D.Pl.kappa.re - 5 - 2 * D.σ₀)
      ‖D.Pl.signedCoeff D.σ₀‖ (retNu D.Pl D.σ₀ n) (retNu_pos D.Pl D.σ₀ n) hC).symm
  filter_upwards [hT3.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn
  have hνn : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεn : 0 < (D.level n).ε := (D.level n).ε_pos
  have hcn : 0 < cOf (D.level n).ν := cOf_pos hνn
  have hnn : 0 ≤ 2 * (D.level n).ε * cOf (D.level n).ν :=
    mul_nonneg (mul_nonneg (by norm_num) hεn.le) hcn.le
  exact (pow_le_one_iff_of_nonneg hnn (by norm_num)).1 hn

end UnforcedLeray.Short.PartIIIb.Concrete

end
