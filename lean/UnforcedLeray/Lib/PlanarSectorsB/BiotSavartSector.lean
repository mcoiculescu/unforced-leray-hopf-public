import UnforcedLeray.Lib.PlanarSectorsB.SectorSum

/-!
# The sector form of `(Kf)·∇E₀` (INF12 target P8, partial)


§5, Level P, target **P8** (Biot–Savart identification). Manuscript (`paper/main.tex`):
`𝓛f = -Ω∂_ϑf - (Kf)·∇E₀`, `K = ∇^⊥Δ⁻¹` (lines 662–670, `eq:st18-t00004`, unit `B0009`),
`E₀' = r k` (lines 639–647).

This module proves the *pointwise Cartesian* half of P8: if the streamfunction of a sector-`n`
vorticity is the sector function `Ψ(y) = ψ(|y|)(y/|y|)ⁿ` (`Ang.ofProfile n ψ`) and `Ψ` is
differentiable at `y`, then its velocity `u = ∇^⊥Ψ = (-∂₂Ψ, ∂₁Ψ)` satisfies

  `u·∇E₀(y) = -i n k(|y|) Ψ(y)`,   with `∇E₀(y) = E₀'(r) y/r = k(r) y`,

so `-(Kf)·∇E₀ = i n k (Δ_{|n|}⁻¹ f_n) e^{inϑ}`, which is the kernel of `couplingSec` (target P6).
The key step is `fderiv_sector_rot`: the angular derivative `∂_ϑΨ = DΨ(y)[iy]` of a function
with `Ψ ∘ O_θ = e^{inθ}Ψ` is `inΨ` (this is also `Ω∂_ϑf = inΩf` on sector `n`).

**Not built** (the analytic half of P8): the identification of the convolution
`Kf(y) = (2π)⁻¹∫(y-z)^⊥|y-z|⁻² f(z) dz` with `∇^⊥ Σ_{n≠0} (greenN |n| f_n)(r) e^{inϑ}` for
`f ∈ L¹ ∩ L²_M` (non-compactly supported data; NonUniqueEuler `green_eq_logPotential` covers only
annulus-supported profiles).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real Complex

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialK)
open UnforcedLeray.Planar.NUE

theorem hasDerivAt_rot_apply (y : ℂ) : HasDerivAt (fun θ : ℝ => rot θ y) (I * y) 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * I) (1 * I) 0 :=
    (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
  have h2 := (h1.cexp).mul_const y
  have e : (fun θ : ℝ => rot θ y) = fun θ : ℝ => Complex.exp ((θ : ℂ) * I) * y := by
    funext θ
    rfl
  rw [e]
  refine h2.congr_deriv ?_
  simp

/-- **Angular derivative of a sector function**: if `Ψ ∘ O_θ = e^{inθ} Ψ` at `y` for all `θ`
and `Ψ` has derivative `L` at `y`, then `∂_ϑΨ(y) = L(iy) = i n Ψ(y)`. -/
theorem fderiv_sector_rot {n : ℤ} {Ψ : ℂ → ℂ} {y : ℂ} {L : ℂ →L[ℝ] ℂ} (hΨ : HasFDerivAt Ψ L y)
    (hrot : ∀ θ : ℝ, Ψ (rot θ y) = Complex.exp ((n : ℂ) * θ * I) * Ψ y) :
    L (I * y) = I * n * Ψ y := by
  have h0 : rot 0 y = y := Polar.rot_zero y
  have hc : HasDerivAt (fun θ : ℝ => Ψ (rot θ y)) (L (I * y)) 0 := by
    have hΨ' : HasFDerivAt Ψ L (rot 0 y) := by rw [h0]; exact hΨ
    exact hΨ'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rot_apply y)
  have h1 : HasDerivAt (fun θ : ℝ => (n : ℂ) * θ * I) ((n : ℂ) * 1 * I) 0 :=
    ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (n : ℂ)).mul_const I
  have h2 := (h1.cexp).mul_const (Ψ y)
  have e : (fun θ : ℝ => Ψ (rot θ y)) = fun θ : ℝ => Complex.exp ((n : ℂ) * θ * I) * Ψ y :=
    funext hrot
  rw [e] at hc
  have := hc.unique h2
  rw [this]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one]
  ring

/-- Sector functions `ψ(|y|)(y/|y|)ⁿ` satisfy the rotation law pointwise. -/
theorem ofProfile_rot (n : ℤ) (ψ : ℝ → ℂ) (θ : ℝ) (y : ℂ) :
    Ang.ofProfile n ψ (rot θ y) = Complex.exp ((n : ℂ) * θ * I) * Ang.ofProfile n ψ y := by
  rw [Ang.ofProfile, Ang.ofProfile, Polar.norm_rot, angPhase_rot]
  ring

/-- **P8, Cartesian coupling identity.** Let `Ψ = ψ(|y|)(y/|y|)ⁿ` be differentiable at `y` with
derivative `L`, and let `u = ∇^⊥Ψ = (-∂₂Ψ, ∂₁Ψ)` with `∂₁Ψ = L 1`, `∂₂Ψ = L i`. With
`∇E₀(y) = k(|y|) y` (since `E₀' = r k`, tex line 647),
`u·∇E₀(y) = -∂₂Ψ k y₁ + ∂₁Ψ k y₂ = -i n k(|y|) Ψ(y)`. Hence `-(Kf)·∇E₀` on sector `n` is
multiplication of the Green streamfunction by `i n k`, the kernel of `couplingSec` (tex lines
662–670 and 1366–1379). -/
theorem velocity_dot_gradE0_sector {n : ℤ} {ψ : ℝ → ℂ} {y : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hΨ : HasFDerivAt (Ang.ofProfile n ψ) L y) :
    -L I * ((radialK ‖y‖ * y.re : ℝ) : ℂ) + L 1 * ((radialK ‖y‖ * y.im : ℝ) : ℂ) =
      -(I * n * (radialK ‖y‖ : ℂ) * Ang.ofProfile n ψ y) := by
  have hrot := fderiv_sector_rot hΨ (ofProfile_rot n ψ · y)
  have hIy : I * y = (-y.im) • (1 : ℂ) + y.re • I := by
    apply Complex.ext <;> simp
  have hL : L (I * y) = -y.im * L 1 + y.re * L I := by
    rw [hIy, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hL] at hrot
  push_cast
  linear_combination (-(radialK ‖y‖ : ℂ)) * hrot

end UnforcedLeray.Planar
