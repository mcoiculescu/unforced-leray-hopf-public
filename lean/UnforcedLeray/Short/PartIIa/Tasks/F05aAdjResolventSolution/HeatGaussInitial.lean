import UnforcedLeray.Short.PartIIa.Sub.F05_1

/-!
# Part II-a, task `PartII-a:F05a`: initial value and periodicity of `heatGauss`

Target: `HeatGaussInitial` (defined in `Short/PartII-a/Sub/F05_1.lean`, line 136).

Source of record: `the November 2 reference manuscript`, lines 1445-1451
(the adjoint heat semigroup `S(t)^*h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)` at line 1447).

Proof. `heatGauss Φ₀ w p = ∫ ξ, γ(ξ) • Φ₀(p.1, p.2 - w • ξ)` with `γ = Heat.kernel 1`.
(a) At `w = 0` the shift `w • ξ` vanishes, so the integrand is `γ(ξ) • Φ₀ p`, and
`Heat.integral_kernel` (`∫ γ = 1`) gives `Φ₀ p`.
(b) The integrand at `(τ + P, y)` equals the integrand at `(τ, y)` pointwise in `ξ`, by
the `P`-periodicity `Φ₀(τ + P, z) = Φ₀(τ, z)` of the phase test (`hPhi.periodic`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

theorem heatGaussInitial_proof : UnforcedLeray.Short.PartIIa.HeatGaussInitial := by
  intro P hP Φ₀ hPhi
  refine ⟨?_, ?_⟩
  · intro p
    simp only [heatGauss, zero_smul, sub_zero, Prod.mk.eta]
    rw [integral_smul_const,
      UnforcedLeray.Heat.integral_kernel (by norm_num : (0 : ℝ) < 1), one_smul]
  · intro w τ y
    have h : ∀ ξ : Space, Φ₀ (τ + P, y - w • ξ) = Φ₀ (τ, y - w • ξ) :=
      fun ξ => hPhi.periodic τ (y - w • ξ)
    simp only [heatGauss, h]

end UnforcedLeray.Short.PartIIa
