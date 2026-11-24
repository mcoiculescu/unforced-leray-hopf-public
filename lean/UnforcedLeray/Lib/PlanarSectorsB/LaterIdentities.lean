import UnforcedLeray.Lib.PlanarSectorsB.Coupling
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Later-chapter planar identities (INF12 target P10, partial)


§5, Level P, target **P10**: explicit angular integrals and radial moments, one lemma per unit.
Built here (the exact identities of the units, with honest hypotheses):

* `B0364`(d) (`eq:st18-t00368`, `paper/main.tex` lines 6788–6801):
  `integral_sin_sq_mul_exp_two` (`∫₀^{2π} sin²ϑ e^{2iϑ} dϑ = -π/2`) and `quadrupole_ofProfile_two`
  (`Q_∞(h e^{2iϑ}) = -(2/π)∫ η² h e^{2iϑ} = ∫₀^∞ r³ h`, for integrable `η² w`).
* `B0372` (line 6868): `quadrupolePoly_annihilated` — the harmonic quadratic polynomial
  `Re(y²) = y₁² - y₂²` is annihilated by `Δ - y·∇/2 + 1` (Mathlib's Laplacian on `ℂ = ℝ²`).
  The consequence `Q_∞ D = 0` (Gaussian graph regularity and cutoffs) is not built.
* `B0400` (`eq:st18-t00408`, lines 7109–7118): `integral_outer_variables` — in the outer
  variables `r = |x'| = s^{-1/2}`, `Y = η/√s`, `dx' dY = π s^{-5/2} ds dη` (iterated form).
* `B0638` (lines 12572–12582): `rE0'_eq`, `unitSource_eq`: `H₀ = rE₀'e^{2iϑ} = r²k e^{2iϑ}`.
* `B0856` (lines 12737–12743): `harmonic_separation`:
  `d cos2ϑ + e sin2ϑ = ½(d - ie)e^{2iϑ} + ½(d + ie)e^{-2iϑ}`.
* `B0857` (`eq:affine-4-109`, lines 12746–12756): `integral_radial_source_eq_zero` (general
  `∫₀^∞(rE' + 2E) r dr = 0` when `r²E → 0`), `integral_rE0'_add_two_E0` (for `E = E₀`) and
  `integral_plane_rE0'_add_two_E0` (zero circulation in the plane).

Not built: `B0232` (heat-scaled terminal kernel asymptotics), `B0388` (plane stress moments
`E_q = iC`), `B0824` (curl of the isolated affine source) and `B0832` (integrated Cartesian
tensor), whose statements use objects of later chapters that are not yet in Lean.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real Complex
open scoped InnerProductSpace

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialVorticity radialOmega_pos)
open UnforcedLeray.Planar.NUE

/-! ### B0638: the unit angular-two Gaussian source -/

/-- `r E₀'(r) = r² k(r)` (`paper/main.tex` line 12578: `k = E₀'/r`, tex line 647). -/
theorem rE0'_eq (r : ℝ) : r * deriv radialVorticity r = r ^ 2 * radialK r := by
  rw [GaussianVortex.deriv_radialVorticity]
  ring

/-- **B0638.** `H₀ = r E₀'(r) e^{2iϑ}` equals the G4 input `H = r² k(r) e^{2iϑ}`. -/
theorem unitSource_eq :
    Ang.ofProfile 2 (fun r => ((r * deriv radialVorticity r : ℝ) : ℂ)) =
      Ang.ofProfile 2 (fun r => ((r ^ 2 * radialK r : ℝ) : ℂ)) := by
  funext y
  simp only [Ang.ofProfile, rE0'_eq]

/-! ### B0856: harmonic separation -/

/-- **B0856.** `d cos 2ϑ + e sin 2ϑ = ½(d - ie) e^{2iϑ} + ½(d + ie) e^{-2iϑ}` (`paper/main.tex`
lines 12737–12743: the positive harmonic of the curl of the affine source has coefficient
`-(d - ie)/2` against `-rE' e^{2iϑ}`). -/
theorem harmonic_separation (d e θ : ℝ) :
    ((d * Real.cos (2 * θ) + e * Real.sin (2 * θ) : ℝ) : ℂ) =
      (d - I * e) / 2 * Complex.exp (2 * θ * I) + (d + I * e) / 2 * Complex.exp (-(2 * θ * I)) := by
  push_cast
  rw [Complex.cos, Complex.sin]
  have h1 : -((2 : ℂ) * θ) * I = -(2 * θ * I) := by ring
  rw [h1]
  ring_nf

/-! ### B0857: the angular-zero radial input has zero circulation -/

/-- `∫₀^∞ (rE'(r) + 2E(r)) r dr = 0` whenever `r²E(r) → 0` at infinity and the integrand is
integrable: the integrand is `(r²E)'` (`paper/main.tex` line 12750). -/
theorem integral_radial_source_eq_zero {E E' : ℝ → ℝ} (hd : ∀ r, HasDerivAt E (E' r) r)
    (hint : IntegrableOn (fun r => (r * E' r + 2 * E r) * r) (Ioi 0))
    (hlim : Tendsto (fun r => r ^ 2 * E r) atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), (r * E' r + 2 * E r) * r = 0 := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun r => r ^ 2 * E r) ((x * E' x + 2 * E x) * x) x := by
    intro x _
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact (h2.mul (hd x)).congr_deriv (by ring)
  have hcont : ContinuousWithinAt (fun r => r ^ 2 * E r) (Ici 0) 0 :=
    ((continuous_pow 2).continuousAt.mul (hd 0).continuousAt).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp

theorem tendsto_sq_mul_radialVorticity :
    Tendsto (fun r : ℝ => r ^ 2 * radialVorticity r) atTop (𝓝 0) := by
  have hx : Tendsto (fun r : ℝ => r ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  have h1 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  have h2 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx
  have h := (h1.const_mul 8).sub (h2.const_mul 8)
  rw [mul_zero, sub_zero] at h
  refine h.congr fun r => ?_
  simp only [Function.comp_def, radialVorticity, radialOmega]
  ring

theorem integrableOn_radial_source_E0 :
    IntegrableOn (fun r : ℝ => (r * (r * radialK r) + 2 * radialVorticity r) * r) (Ioi 0) := by
  have h := (integrableOn_mul_one_add_sq_rpow_mul_exp (a := 2) (c := 1 / 4)
    (by norm_num)).const_mul 4
  refine h.mono' ?_ ?_
  · exact ((((continuous_id.mul (continuous_id.mul B0012.continuous_radialK)).add
      (continuous_const.mul GaussianVortex.radialVorticity_smooth.continuous)).mul
        continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : (0 : ℝ) < r := hr
    have hb : 0 < 1 + r ^ 2 := by positivity
    have hp : (1 + r ^ 2) ^ (2 : ℝ) = (1 + r ^ 2) ^ 2 := Real.rpow_two _
    have he : Real.exp (-(1 / 4 * r ^ 2)) = radialOmega r := by
      unfold radialOmega
      congr 1
      ring
    rw [hp, he, Real.norm_eq_abs]
    have hΩ := (radialOmega_pos r).le
    have heq : (r * (r * radialK r) + 2 * radialVorticity r) * r =
        r * ((r ^ 4 / 4 - 3 * r ^ 2 + 4) * radialOmega r) := by
      unfold radialK radialVorticity
      ring
    rw [heq, abs_mul, abs_of_pos hr', abs_mul, abs_of_nonneg hΩ]
    have hq : |r ^ 4 / 4 - 3 * r ^ 2 + 4| ≤ 4 * (1 + r ^ 2) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
    calc r * (|r ^ 4 / 4 - 3 * r ^ 2 + 4| * radialOmega r)
        ≤ r * (4 * (1 + r ^ 2) ^ 2 * radialOmega r) := by gcongr
      _ = 4 * (r * ((1 + r ^ 2) ^ 2 * radialOmega r)) := by ring

/-- **B0857** (`eq:affine-4-109`, line 12750): `∫₀^∞ (rE₀' + 2E₀) r dr = 0` for the Gaussian
vorticity `E₀ = (2 - r²/2)e^{-r²/4}` (`eq:st18-t00001`). -/
theorem integral_rE0'_add_two_E0 :
    ∫ r in Ioi (0 : ℝ), (r * deriv radialVorticity r + 2 * radialVorticity r) * r = 0 := by
  simp_rw [GaussianVortex.deriv_radialVorticity]
  exact integral_radial_source_eq_zero (E := radialVorticity)
    (fun r => GaussianVortex.hasDerivAt_radialVorticity r) integrableOn_radial_source_E0
    tendsto_sq_mul_radialVorticity

/-- **B0857, zero circulation in the plane**: `∫_{ℝ²} (rE₀' + 2E₀)(|y|) dy = 0`. -/
theorem integral_plane_rE0'_add_two_E0 :
    ∫ y : ℂ, (‖y‖ * deriv radialVorticity ‖y‖ + 2 * radialVorticity ‖y‖) = 0 := by
  rw [Polar.integral_comp_norm (fun r => r * deriv radialVorticity r + 2 * radialVorticity r)]
  have h : ∫ r in Ioi (0 : ℝ), r • (r * deriv radialVorticity r + 2 * radialVorticity r) =
      ∫ r in Ioi (0 : ℝ), (r * deriv radialVorticity r + 2 * radialVorticity r) * r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [h, integral_rE0'_add_two_E0, smul_zero]

/-! ### B0364(d): the quadrupole of an angular-two vorticity -/

theorem integral_exp_int_mul_I {k : ℤ} (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp ((k : ℂ) * θ * I) = 0 := by
  have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
  have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * π) hc
  have e : ∀ θ : ℝ, (k : ℂ) * θ * I = (k : ℂ) * I * θ := fun θ => by ring
  simp_rw [e]
  rw [h]
  have h2 : Complex.exp ((k : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
    have : (k : ℂ) * I * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [h2]
  simp

/-- `∫₀^{2π} sin²ϑ e^{2iϑ} dϑ = -π/2` (`paper/main.tex` line 6800). -/
theorem integral_sin_sq_mul_exp_two :
    ∫ θ in (0 : ℝ)..2 * π, ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * I) =
      -((π : ℂ) / 2) := by
  have hpt : ∀ θ : ℝ, ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * I) =
      -(1 / 4) * Complex.exp (((4 : ℤ) : ℂ) * θ * I) +
        (1 / 2) * Complex.exp (((2 : ℤ) : ℂ) * θ * I) - 1 / 4 := by
    intro θ
    set X := Complex.exp (θ * I) with hX
    have hX0 : X ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (2 * θ * I) = X ^ 2 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h2' : Complex.exp (((2 : ℤ) : ℂ) * θ * I) = X ^ 2 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h4 : Complex.exp (((4 : ℤ) : ℂ) * θ * I) = X ^ 4 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hs : ((Real.sin θ : ℝ) : ℂ) = (X⁻¹ - X) * I / 2 := by
      rw [Complex.ofReal_sin, Complex.sin, hX, ← Complex.exp_neg]
      congr 2
      ring_nf
    rw [h2, h2', h4, hs]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hpt]
  have hc1 : IntervalIntegrable (fun θ : ℝ => -(1 / 4 : ℂ) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => -(1 / 4 : ℂ) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * I)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ : ℝ => (1 / 2 : ℂ) *
      Complex.exp (((2 : ℤ) : ℂ) * θ * I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => (1 / 2 : ℂ) *
      Complex.exp (((2 : ℤ) : ℂ) * θ * I)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hc1.add hc2) intervalIntegrable_const,
    intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_exp_int_mul_I (by norm_num : (4 : ℤ) ≠ 0),
    integral_exp_int_mul_I (by norm_num : (2 : ℤ) ≠ 0), intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_zero, add_zero, zero_sub, real_smul]
  push_cast
  ring

theorem angPhase_circleMap {r : ℝ} (hr : 0 < r) (n : ℤ) (θ : ℝ) :
    Ang.angPhase n (circleMap 0 r θ) = Complex.exp (n * θ * I) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Ang.angPhase, norm_circleMap_zero, abs_of_pos hr, circleMap_zero,
    mul_div_cancel_left₀ _ hr', ← Complex.exp_int_mul]
  congr 1
  ring

/-- **B0364**(d) (`eq:st18-t00368`, `paper/main.tex` lines 6788–6801): for an angular-two
vorticity `w = h(r)e^{2iϑ}` with `η² w` integrable, `Q_∞(w) = -(2/π)∫_{ℝ²} η² w = ∫₀^∞ r³ h`
(`η = Im y`). -/
theorem quadrupole_ofProfile_two {h : ℝ → ℂ}
    (hint : Integrable (fun y : ℂ => ((y.im : ℝ) : ℂ) ^ 2 * Ang.ofProfile 2 h y)) :
    -(2 / (π : ℂ)) * ∫ y : ℂ, ((y.im : ℝ) : ℂ) ^ 2 * Ang.ofProfile 2 h y =
      ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * h r := by
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hint]
  have hin : ∀ r ∈ Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * π,
      ((((circleMap 0 r θ).im : ℝ) : ℂ) ^ 2 * Ang.ofProfile 2 h (circleMap 0 r θ)) =
        -((π : ℂ) / 2) * ((r : ℂ) ^ 3 * h r) := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have hpt : ∀ θ : ℝ, (((circleMap 0 r θ).im : ℝ) : ℂ) ^ 2 * Ang.ofProfile 2 h (circleMap 0 r θ) =
        ((r : ℂ) ^ 2 * h r) * (((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * I)) := by
      intro θ
      have him : (circleMap 0 r θ).im = r * Real.sin θ := by
        rw [circleMap_zero]
        simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
      rw [Ang.ofProfile, angPhase_circleMap hr' 2 θ, norm_circleMap_zero, abs_of_pos hr', him]
      push_cast
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_exp_two, Complex.real_smul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul, ← mul_assoc]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc : -(2 / (π : ℂ)) * -((π : ℂ) / 2) = 1 := by
    field_simp
  rw [hc, one_mul]

/-! ### B0372: the harmonic quadratic polynomial -/

/-- **B0372** (`paper/main.tex` line 6868): the harmonic quadratic polynomial
`P(y) = Re(y²) = y₁² - y₂²` (which selects `Q_∞` on angular-two functions) is annihilated by
`D*_unweighted = Δ - y·∇/2 + 1`: `ΔP = 0` (real part of a holomorphic function) and
`y·∇P = 2P` (homogeneity). Here `Δ` is Mathlib's Laplacian on `ℂ = ℝ²` and `y·∇P(y)` is
`fderiv ℝ P y y`. -/
theorem quadrupolePoly_annihilated (y : ℂ) :
    Laplacian.laplacian (fun z : ℂ => (z ^ 2).re) y -
        1 / 2 * fderiv ℝ (fun z : ℂ => (z ^ 2).re) y y + (y ^ 2).re = 0 := by
  have hΔ : Laplacian.laplacian (fun z : ℂ => (z ^ 2).re) y = 0 := by
    have h : AnalyticAt ℂ (fun z : ℂ => z ^ 2) y := analyticAt_id.pow 2
    exact h.harmonicAt_re.2.self_of_nhds
  have h1 := (hasDerivAt_pow 2 y).hasFDerivAt.restrictScalars ℝ
  have h2 := (Complex.reCLM.hasFDerivAt (x := y ^ 2)).comp y h1
  have e : (fun z : ℂ => (z ^ 2).re) = ⇑Complex.reCLM ∘ fun z : ℂ => z ^ 2 := by
    funext z
    simp
  have hD : fderiv ℝ (fun z : ℂ => (z ^ 2).re) y y = 2 * (y ^ 2).re := by
    rw [e, h2.fderiv]
    simp [Complex.mul_re, sq]
    ring
  rw [hΔ, hD]
  ring

/-! ### B0400: the outer-variable Jacobian -/

/-- **B0400** (`eq:st18-t00408`, `paper/main.tex` lines 7109–7118): in the outer variables
`r = |x'| = s^{-1/2}`, `Y = η/√s` one has `dx' dY = π s^{-5/2} ds dη`, in iterated form
(no integrability hypothesis: each one-dimensional substitution holds for Bochner integrals). -/
theorem integral_outer_variables {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → ℝ → E) :
    ∫ x : ℂ, ∫ Y : ℝ, F ‖x‖ Y =
      π • ∫ s in Ioi (0 : ℝ), s ^ (-(5 / 2 : ℝ)) •
        ∫ η : ℝ, F (s ^ (-(1 / 2 : ℝ))) (η / Real.sqrt s) := by
  rw [Polar.integral_comp_norm (fun r => ∫ Y, F r Y)]
  have key := integral_comp_rpow_Ioi (fun r : ℝ => r • ∫ Y, F r Y) (p := -(1 / 2 : ℝ))
    (by norm_num)
  rw [← key, ← integral_smul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  rw [Measure.integral_comp_div (fun η => F (s ^ (-(1 / 2 : ℝ))) η) (Real.sqrt s)]
  simp only [smul_smul]
  congr 1
  have e1 : s ^ (-(1 / 2 : ℝ) - 1) * s ^ (-(1 / 2 : ℝ)) = s ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hs']
    norm_num
  have e2 : s ^ (-(5 / 2 : ℝ)) * Real.sqrt s = s ^ (-(2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs']
    norm_num
  rw [abs_of_neg (by norm_num : -(1 / 2 : ℝ) < 0), abs_of_pos (Real.sqrt_pos.2 hs')]
  linear_combination π * e1 - π * e2

end UnforcedLeray.Planar
