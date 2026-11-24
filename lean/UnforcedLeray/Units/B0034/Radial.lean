import UnforcedLeray.Analysis.GaussianVortex.RadialProfile
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# B0034 helper: the radial Rayleigh equation from the logarithmic one

B0034 (`paper/main.tex`, lines 1012–1021) states the mode in the radial variable,
`(Ω-c_N)Δ₂φ_N - kφ_N = 0` on `[R₁,R₂] = [e^{-N}, e^N]`, with
`Δ₂ = ∂_r² + r⁻¹∂_r - 4r⁻²` (tex line 815, `n = 2`) and `k = E₀'/r` (tex line 647),
and normalizes `F_N(t) = φ_N(e^t)`. The compiled Evans framework works with the
logarithmic form `(Ω-c)(F''-4F) - AF = 0` (tex line 836, eq. `st18-t00021`), with
`A(t) = r E₀'(r) = r²k(r)`. Under `φ(r) = F(log r)`,
`r²Δ₂φ(r) = (F''-4F)(log r)`, so the two equations are equivalent for `r > 0`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology
namespace UnforcedLeray.B0034
open UnforcedLeray.Rayleigh UnforcedLeray.GaussianVortex

/-- The radial operator at angular index two, `Δ₂φ = φ'' + r⁻¹φ' - 4r⁻²φ`
(tex line 815 with `n = 2`); derivatives are genuine real derivatives. -/
def radialDelta2 (φ : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv φ) r + deriv φ r / (r : ℂ) - 4 * φ r / (r : ℂ) ^ 2

/-- `A(t) = r²k(r)` at `r = e^t` (tex lines 819–822). -/
theorem gaussianRayleighCoefficient_eq_radialK (t : ℝ) :
    gaussianRayleighCoefficient t = Real.exp t ^ 2 * radialK (Real.exp t) := by
  rw [gaussianRayleighCoefficient_eq, radialK, radialOmega_exp, exp_sq_eq_exp_twice]
  unfold Sturm.neutralRadius
  ring

/-- `k(r) = A(log r)/r²` for `r > 0`. -/
theorem radialK_eq_div {r : ℝ} (hr : 0 < r) :
    radialK r = gaussianRayleighCoefficient (Real.log r) / r ^ 2 := by
  rw [gaussianRayleighCoefficient_eq_radialK, Real.exp_log hr]
  field_simp

/-- Chain rule: if `F'' ` is the second derivative of `F`, then for `r > 0` the
logarithmic Rayleigh equation at `log r` gives the radial one at `r` for
`φ = F ∘ log`. -/
theorem radial_equation_of_log {F F' F'' : ℝ → ℂ} {c : ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : ∀ t, HasDerivAt F' (F'' t) t)
    {r : ℝ} (hr : 0 < r)
    (heq : ((Sturm.neutralOmega (Real.log r) : ℂ) - c) *
        (F'' (Real.log r) - 4 * F (Real.log r)) -
      (gaussianRayleighCoefficient (Real.log r) : ℂ) * F (Real.log r) = 0) :
    ((radialOmega r : ℂ) - c) * radialDelta2 (fun s => F (Real.log s)) r -
      (radialK r : ℂ) * F (Real.log r) = 0 := by
  -- first derivative on `(0,∞)`
  have h1 : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s => F (Real.log s)) (s⁻¹ • F' (Real.log s)) s := fun s hs =>
    (hF (Real.log s)).scomp s (Real.hasDerivAt_log hs.ne')
  have hd1 : deriv (fun s => F (Real.log s)) =ᶠ[𝓝 r] fun s => s⁻¹ • F' (Real.log s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (h1 s hs).deriv
  -- second derivative at `r`
  have h2 : HasDerivAt (fun s => s⁻¹ • F' (Real.log s))
      (r⁻¹ • (r⁻¹ • F'' (Real.log r)) + (-(r ^ 2)⁻¹) • F' (Real.log r)) r :=
    (hasDerivAt_inv hr.ne').smul ((hF' (Real.log r)).scomp r (Real.hasDerivAt_log hr.ne'))
  have hdd : deriv (deriv (fun s => F (Real.log s))) r =
      r⁻¹ • (r⁻¹ • F'' (Real.log r)) + (-(r ^ 2)⁻¹) • F' (Real.log r) := by
    rw [hd1.deriv_eq]
    exact h2.deriv
  have hd : deriv (fun s => F (Real.log s)) r = r⁻¹ • F' (Real.log r) := (h1 r hr).deriv
  have hΩ : radialOmega r = Sturm.neutralOmega (Real.log r) := by
    rw [← radialOmega_exp, Real.exp_log hr]
  unfold radialDelta2
  rw [hdd, hd, hΩ, radialK_eq_div hr]
  simp only [Complex.real_smul]
  push_cast
  linear_combination ((r : ℂ) ^ 2)⁻¹ * heq

/-- `F ∘ log` is `C²` on `(0,∞)` when `F` is. -/
theorem contDiffOn_comp_log {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) :
    ContDiffOn ℝ 2 (fun s => F (Real.log s)) (Ioi 0) :=
  hF.comp_contDiffOn (Real.contDiffOn_log.mono fun _ hs => ne_of_gt hs)

end UnforcedLeray.B0034
