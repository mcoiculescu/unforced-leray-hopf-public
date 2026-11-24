import UnforcedLeray.Loc.L01Coefficient.Maps
import UnforcedLeray.Lib.Gaussian.Kernel

/-!
# Step L1, helpers: the heat profile is `𝒯`-periodic in phase

Support for `Loc/L01Coefficient.lean` (step L1, `paper/main.tex` lines 275–281: "uniformly
in phase", `U_* ∈ C_per C₀`; blueprint units B0707, B0710).

`heatProfile_add_period`: if `u(e^{𝒯/2}x) = e^{-𝒯/2}u(x)` for `x ≠ 0` (`loc:eq:dss`), then
`H_h[u](y, τ + 𝒯) = H_h[u](y, τ)` at every point. The proof is the change of variables
`z = e^{𝒯/2} w` in the heat integral, with the Gaussian scaling
`G_{λ²s}(λw) = λ^{-3}G_s(w)` (`Gaussian.gaussKernel_scale`). It holds for every `u`
(non-integrable heat integrals are `0` on both sides, by `Measure.integral_comp_smul`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

/-- The change of variables `z = λw` in a heat integral of a field homogeneous of degree
`-1` under the dilation by `λ`. -/
theorem heat_integral_scale {u : SpatialField} {lam : ℝ} (hlam : 0 < lam)
    (hdss : ∀ x : Space, x ≠ 0 → u (lam • x) = lam⁻¹ • u x) {s : ℝ} (hs : 0 < s)
    (x : Space) :
    (∫ z : Space, Heat.kernel (lam ^ 2 * s) z • u (lam • x - z)) =
      lam⁻¹ • ∫ w : Space, Heat.kernel s w • u (x - w) := by
  have h1 := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space)
    (fun z : Space => Heat.kernel (lam ^ 2 * s) z • u (lam • x - z)) lam
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  rw [hfin] at h1
  have hr : lam ^ (-((3 : ℕ) : ℝ)) = (lam ^ 3)⁻¹ := by
    rw [Real.rpow_neg hlam.le, Real.rpow_natCast]
  have h2 : (fun w : Space => Heat.kernel (lam ^ 2 * s) (lam • w) • u (lam • x - lam • w))
      =ᵐ[volume] fun w => (lam ^ 3)⁻¹ • lam⁻¹ • (Heat.kernel s w • u (x - w)) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton x)] with w hw
    have hxw : x - w ≠ 0 := sub_ne_zero.mpr (fun h => hw (by rw [h]; rfl))
    rw [← smul_sub, hdss _ hxw, ← Gaussian.gaussKernel_three_eq,
      Gaussian.gaussKernel_scale hlam hs, hr]
    simp only [smul_smul]
    congr 1
    ring
  rw [integral_congr_ae h2, integral_smul, integral_smul,
    abs_of_pos (inv_pos.mpr (pow_pos hlam 3))] at h1
  exact (smul_right_injective Space (inv_ne_zero (pow_pos hlam 3).ne')) h1.symm

/-- **Periodicity of the heat profile** (lines 159–163 with `loc:eq:dss`):
`H_h[u](·, τ + 𝒯) = H_h[u](·, τ)` pointwise. -/
theorem heatProfile_add_period {h T : ℝ} {u : SpatialField} (hh : 0 < h)
    (hdss : ∀ x : Space, x ≠ 0 → u (Real.exp (T / 2) • x) = Real.exp (-(T / 2)) • u x)
    (τ : ℝ) (y : Space) : heatProfile h u (τ + T) y = heatProfile h u τ y := by
  have hlam : 0 < Real.exp (T / 2) := Real.exp_pos _
  have hs : 0 < h * Real.exp τ := mul_pos hh (Real.exp_pos _)
  have hdss' : ∀ x : Space, x ≠ 0 →
      u (Real.exp (T / 2) • x) = (Real.exp (T / 2))⁻¹ • u x := by
    intro x hx
    rw [hdss x hx, Real.exp_neg]
  have htime : h * Real.exp (τ + T) = Real.exp (T / 2) ^ 2 * (h * Real.exp τ) := by
    rw [← Real.exp_nat_mul, Real.exp_add]
    have : ((2 : ℕ) : ℝ) * (T / 2) = T := by push_cast; ring
    rw [this]
    ring
  have hpoint : Real.exp ((τ + T) / 2) • y = Real.exp (T / 2) • (Real.exp (τ / 2) • y) := by
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [heatProfile_apply, heatProfile_apply, htime, hpoint,
    heat_integral_scale hlam hdss' hs, smul_smul]
  congr 1
  rw [show (τ + T) / 2 = τ / 2 + T / 2 by ring, Real.exp_add]
  field_simp

end UnforcedLeray.Blueprint.L01
