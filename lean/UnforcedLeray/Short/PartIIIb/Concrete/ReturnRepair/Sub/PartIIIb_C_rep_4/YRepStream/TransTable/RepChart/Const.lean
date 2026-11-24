import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Hold

/-!
# `RepChart/Const`: the `ρ_b` algebra `ρ_b^{-1/2} R⁻¹ ρ_b = P_ν ε^{25/22} e^{m₀/(2ν)}` (source 2698-2713)
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RC

theorem repConst {C0 m0 ν ε : ℝ} (k0 : ℕ) (hC0 : 0 < C0) (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) :
    Real.sqrt ((C0 * (ν ^ k0)⁻¹ * Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ))⁻¹ * Real.pi⁻¹) *
        (ε⁻¹)⁻¹ * (C0 * (ν ^ k0)⁻¹ * Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ)) ≤
      Real.sqrt C0 * Real.sqrt Real.pi⁻¹ * ν⁻¹ ^ k0 * ε ^ (25 / 22 : ℝ) * Real.exp (m0 / 2 / ν) := by
  set ρ : ℝ := C0 * (ν ^ k0)⁻¹ * Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ0
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
  have h1 : Real.sqrt (ρ⁻¹ * Real.pi⁻¹) * ρ = Real.sqrt Real.pi⁻¹ * Real.sqrt ρ := by
    rw [Real.sqrt_mul (inv_nonneg.2 hρ0.le), Real.sqrt_inv]
    have h7 : (Real.sqrt ρ)⁻¹ * ρ = Real.sqrt ρ := by
      field_simp
      nlinarith [hsq]
    calc (Real.sqrt ρ)⁻¹ * Real.sqrt Real.pi⁻¹ * ρ
        = Real.sqrt Real.pi⁻¹ * ((Real.sqrt ρ)⁻¹ * ρ) := by ring
      _ = _ := by rw [h7]
  have h2 : Real.sqrt ρ = Real.sqrt C0 * Real.sqrt ((ν ^ k0)⁻¹) * Real.exp (m0 / 2 / ν) *
      ε ^ (3 / 22 : ℝ) := by
    rw [hρ, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    congr 2
    · rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
    · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]; norm_num
  have h3 : Real.sqrt ((ν ^ k0)⁻¹) ≤ ν⁻¹ ^ k0 := by
    have h4 : 1 ≤ ν⁻¹ ^ k0 := one_le_pow₀ ((one_le_inv₀ hν).2 hν1)
    have h5 : (ν ^ k0)⁻¹ = ν⁻¹ ^ k0 := by rw [inv_pow]
    rw [h5]
    exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h6 : ε ^ (25 / 22 : ℝ) = ε * ε ^ (3 / 22 : ℝ) := by
    rw [← Real.rpow_one_add' hε.le (by norm_num)]; norm_num
  rw [inv_inv]
  calc Real.sqrt (ρ⁻¹ * Real.pi⁻¹) * ε * ρ
      = (Real.sqrt (ρ⁻¹ * Real.pi⁻¹) * ρ) * ε := by ring
    _ = Real.sqrt Real.pi⁻¹ * Real.sqrt ρ * ε := by rw [h1]
    _ = Real.sqrt C0 * Real.sqrt Real.pi⁻¹ * Real.sqrt ((ν ^ k0)⁻¹) * ε ^ (25 / 22 : ℝ) *
          Real.exp (m0 / 2 / ν) := by rw [h2, h6]; ring
    _ ≤ _ := by gcongr

end RC

end UnforcedLeray.Short.PartIIIb.Concrete

end
