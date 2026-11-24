import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Chain
import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Param
import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Ibp

/-!
# Helper for `polarReduction`: the angular mode identity

For a smooth `φ : ℝ × ℝ → ℂ` and `Φ(r) = ∫_{-π}^{π} e^{2iθ} φ(r cos θ, r sin θ) dθ`, for `r ≠ 0`
`Φ'' + Φ'/r - 4Φ/r² = ∫_{-π}^{π} e^{2iθ} Δφ(r cos θ, r sin θ) dθ`  (`angular_identity`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff
open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

namespace UnforcedLeray.Short.PartI.PolarRed

theorem contDiff_pol : ContDiff ℝ ∞ (fun p : ℝ × ℝ => pol p.1 p.2) := by
  unfold pol
  exact (contDiff_fst.mul (Real.contDiff_cos.comp contDiff_snd)).prodMk
    (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd))

theorem contDiff_expMode :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.exp (2 * Complex.I * (p.2 : ℂ))) :=
  Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))

/-- The angular mode `(r, θ) ↦ e^{2iθ} φ(r cos θ, r sin θ)`. -/
def angF (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (2 * Complex.I * (p.2 : ℂ)) * φ (pol p.1 p.2)

/-- The radial derivative of `angF φ` in its first variable, `e^{2iθ} ∂_r φ(pol r θ)`. -/
def G1 (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (2 * Complex.I * (p.2 : ℂ)) *
    fderiv ℝ φ (pol p.1 p.2) (Real.cos p.2, Real.sin p.2)

theorem contDiff_angF {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (angF φ) :=
  contDiff_expMode.mul (hφ.comp contDiff_pol)

theorem contDiff_G1 {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (G1 φ) := by
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ => fderiv ℝ φ (pol p.1 p.2)) :=
    (ContDiff.fderiv_right (m := ∞) hφ (by simp)).comp contDiff_pol
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.cos p.2, Real.sin p.2)) :=
    (Real.contDiff_cos.comp contDiff_snd).prodMk (Real.contDiff_sin.comp contDiff_snd)
  exact contDiff_expMode.mul (hD.clm_apply hc)

theorem hasDerivAt_angF_slice {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => angF φ (s, θ)) (G1 φ (r, θ)) r :=
  (hasDerivAt_phi_r hφ r θ).const_mul (Complex.exp (2 * Complex.I * (θ : ℂ)))

theorem deriv_Phi {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    deriv (fun r : ℝ => ∫ θ in (-π)..π, angF φ (r, θ)) =
      fun r : ℝ => ∫ θ in (-π)..π, G1 φ (r, θ) := by
  funext r
  have h1 := hasDerivAt_param (contDiff_angF hφ) r
  have h2 : (fun θ : ℝ => dsl (angF φ) (r, θ)) = fun θ : ℝ => G1 φ (r, θ) := by
    funext θ
    exact (hasDerivAt_slice (contDiff_angF hφ) r θ).unique (hasDerivAt_angF_slice hφ r θ)
  rw [h1.deriv, h2]

theorem deriv_deriv_phi_eq {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    deriv (fun s => deriv (fun t => φ (pol t θ)) s) r =
      fderiv ℝ (fderiv ℝ φ) (pol r θ) (Real.cos θ, Real.sin θ) (Real.cos θ, Real.sin θ) := by
  have hfun : (fun s => deriv (fun t => φ (pol t θ)) s) =
      fun s => fderiv ℝ φ (pol s θ) (Real.cos θ, Real.sin θ) := by
    funext s
    exact (hasDerivAt_phi_r hφ s θ).deriv
  rw [hfun]
  exact (hasDerivAt_fderiv_apply hφ r θ _).deriv

theorem dsl_G1_eq {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    dsl (G1 φ) (r, θ) = Complex.exp (2 * Complex.I * (θ : ℂ)) *
      deriv (fun s => deriv (fun t => φ (pol t θ)) s) r := by
  have hs := hasDerivAt_slice (contDiff_G1 hφ) r θ
  have key : HasDerivAt (fun s : ℝ => G1 φ (s, θ))
      (Complex.exp (2 * Complex.I * (θ : ℂ)) *
        fderiv ℝ (fderiv ℝ φ) (pol r θ) (Real.cos θ, Real.sin θ) (Real.cos θ, Real.sin θ)) r :=
    (hasDerivAt_fderiv_apply hφ r θ (Real.cos θ, Real.sin θ)).const_mul
      (Complex.exp (2 * Complex.I * (θ : ℂ)))
  rw [deriv_deriv_phi_eq hφ r θ]
  exact hs.unique key

/-- The second radial derivative of the angular integral is the integral of the second radial
derivative of the angular mode. -/
theorem deriv_deriv_Phi {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    deriv (deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ))) r =
      ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun s => deriv (fun t => φ (pol t θ)) s) r := by
  rw [deriv_Phi hφ, (hasDerivAt_param (contDiff_G1 hφ) r).deriv]
  congr 1
  funext θ
  exact dsl_G1_eq hφ r θ

theorem deriv_Phi_radial {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ)) r =
      ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) * deriv (fun t => φ (pol t θ)) r := by
  rw [deriv_Phi hφ]
  dsimp only
  congr 1
  funext θ
  have hd : deriv (fun t => φ (pol t θ)) r = fderiv ℝ φ (pol r θ) (Real.cos θ, Real.sin θ) :=
    (hasDerivAt_phi_r hφ r θ).deriv
  simp only [G1, hd]

/-- **Angular mode identity.** For `r ≠ 0`:
`Φ'' + Φ'/r - 4Φ/r² = ∫ e^{2iθ} Δφ(pol r θ) dθ`, where `Δφ = ∂₁²φ + ∂₂²φ`. -/
theorem angular_identity {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ))) r +
        deriv (fun r' : ℝ => ∫ θ in (-π)..π, angF φ (r', θ)) r / (r : ℂ) -
          4 * (∫ θ in (-π)..π, angF φ (r, θ)) / (r : ℂ) ^ 2 =
      ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ)) := by
  -- smoothness and periodicity of the radial profile `h = φ(pol r ·)`
  have hh : ContDiff ℝ ∞ (fun σ : ℝ => φ (pol r σ)) := by
    have hc : ContDiff ℝ ∞ (fun σ : ℝ => pol r σ) :=
      (contDiff_const.mul Real.contDiff_cos).prodMk (contDiff_const.mul Real.contDiff_sin)
    exact hφ.comp hc
  have hper : φ (pol r (-π)) = φ (pol r π) := by simp [pol]
  have hper' : deriv (fun σ : ℝ => φ (pol r σ)) (-π) = deriv (fun σ : ℝ => φ (pol r σ)) π := by
    rw [(hasDerivAt_phi_θ hφ r (-π)).deriv, (hasDerivAt_phi_θ hφ r π).deriv]
    simp [pol]
  have hIBP : ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (deriv (fun σ : ℝ => φ (pol r σ))) θ =
      -4 * ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) * φ (pol r θ) :=
    ibp_ang_second hh hper hper'
  -- continuity of the three integrands in θ
  have hdh : ContDiff ℝ ∞ (deriv (fun σ : ℝ => φ (pol r σ))) :=
    (contDiff_infty_iff_deriv.1 hh).2
  have hddh : Continuous (deriv (deriv (fun σ : ℝ => φ (pol r σ)))) :=
    (contDiff_infty_iff_deriv.1 hdh).2.continuous
  have hcont_pair : Continuous (fun θ : ℝ => (r, θ)) := Continuous.prodMk continuous_const continuous_id
  have c2 : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
      deriv (fun s => deriv (fun t => φ (pol t θ)) s) r) := by
    have e : (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun s => deriv (fun t => φ (pol t θ)) s) r) = fun θ => dsl (G1 φ) (r, θ) := by
      funext θ
      exact (dsl_G1_eq hφ r θ).symm
    rw [e]
    exact ((contDiff_dsl (contDiff_G1 hφ)).continuous).comp hcont_pair
  have c1 : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
      deriv (fun t => φ (pol t θ)) r) := by
    have e : (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun t => φ (pol t θ)) r) = fun θ => G1 φ (r, θ) := by
      funext θ
      have hd : deriv (fun t => φ (pol t θ)) r = fderiv ℝ φ (pol r θ) (Real.cos θ, Real.sin θ) :=
        (hasDerivAt_phi_r hφ r θ).deriv
      simp only [G1, hd]
    rw [e]
    exact (contDiff_G1 hφ).continuous.comp hcont_pair
  have c0 : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
      deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ) :=
    (contDiff_expMode.continuous.comp hcont_pair).mul hddh
  have hIBP : ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ =
      -4 * ∫ θ in (-π)..π, angF φ (r, θ) :=
    ibp_ang_second hh hper hper'
  have hsplit : ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ)) =
      (∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun s => deriv (fun t => φ (pol t θ)) s) r) +
      (∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun t => φ (pol t θ)) r) / (r : ℂ) +
      (∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ) / (r : ℂ) ^ 2 := by
    have hfun : (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        (iterDirDeriv [ev 0, ev 0] φ (pol r θ) + iterDirDeriv [ev 1, ev 1] φ (pol r θ))) =
        fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
          deriv (fun s => deriv (fun t => φ (pol t θ)) s) r +
        Complex.exp (2 * Complex.I * (θ : ℂ)) * deriv (fun t => φ (pol t θ)) r / (r : ℂ) +
        Complex.exp (2 * Complex.I * (θ : ℂ)) *
          deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ / (r : ℂ) ^ 2 := by
      funext θ
      rw [← polar_laplacian hφ hr θ]
      ring
    have hA : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun s => deriv (fun t => φ (pol t θ)) s) r +
        Complex.exp (2 * Complex.I * (θ : ℂ)) * deriv (fun t => φ (pol t θ)) r / (r : ℂ)) :=
      c2.add (c1.div_const _)
    have hB : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun τ => deriv (fun σ => φ (pol r σ)) τ) θ / (r : ℂ) ^ 2) :=
      c0.div_const _
    have hC : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun s => deriv (fun t => φ (pol t θ)) s) r) := c2
    have hD : Continuous (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)) *
        deriv (fun t => φ (pol t θ)) r / (r : ℂ)) := c1.div_const _
    rw [hfun, intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
      intervalIntegral.integral_add (hC.intervalIntegrable _ _) (hD.intervalIntegrable _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_div]

  rw [deriv_deriv_Phi hφ r, deriv_Phi_radial hφ r, hsplit, hIBP]
  ring

end UnforcedLeray.Short.PartI.PolarRed
