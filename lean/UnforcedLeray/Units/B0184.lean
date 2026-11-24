import UnforcedLeray.Analysis.RingLift.Chart
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# B0184 `eq:st18-t00187`: physical ring chart and differentiation rules

Blueprint unit B0184, label `eq:st18-t00187`, `paper/main.tex` lines 2837–2850
(subsection "Coordinates and equations" of the exact solenoidal lift; the operator
`K = η∂_η + 2s∂_s` is defined at line 2805).

Statement in words. Let `R ≥ 2` and `ε = R⁻¹`. For physical cylindrical coordinates
`r > 0`, `z` and `t > 0` put `a_r = R/r`, `q = R log(r/R)`, `η = a_r z`, `s = a_r² t` and
`D_ε = ∂_q − εK` with `K = η∂_η + 2s∂_s`. A cylinder function is a function of `(r, z, t)`
of the form `F(r,z,t) = f(q, η, s)` for a profile `f`. On cylinder functions the physical
derivatives are `∂_r = a_r D_ε`, `∂_z = a_r ∂_η` and `∂_t = a_r² ∂_s`, that is
`∂_r F = a_r (D_ε f)(q,η,s)`, `∂_z F = a_r (∂_η f)(q,η,s)`, `∂_t F = a_r² (∂_s f)(q,η,s)`.

The coordinate functions `a_r, q, η, s` and their one-variable derivatives are the compiled
declarations of `UnforcedLeray.Analysis.RingLift.Chart`; this file adds the profile partial
derivatives, the operators `K` and `D_ε`, the cylinder lift, and the multivariable chain rule
that turns the one-variable derivatives into the three differentiation rules. It also records
that `(q, η, s)` is a genuine chart of `{r > 0} × ℝ × ℝ` (explicit inverse) and that
`a_r = exp(−εq)` is itself a cylinder function.

Hypotheses. The manuscript's cylinder functions are smooth; the only implicit hypothesis
added is differentiability of the profile `f` at the image point (without it the Lean
`fderiv` is the junk value `0` and the identities could fail).
-/

set_option autoImplicit false
noncomputable section
namespace UnforcedLeray.B0184

open UnforcedLeray.RingLift

/-- Profile variables `(q, (η, s))`, the same layout as the draft
-/
abbrev ProfilePoint := ℝ × (ℝ × ℝ)

/-- Unit vector in the log-radius direction `q`. -/
def eqDir : ProfilePoint := (1, (0, 0))
/-- Unit vector in the transverse direction `η`. -/
def eηDir : ProfilePoint := (0, (1, 0))
/-- Unit vector in the age direction `s`. -/
def esDir : ProfilePoint := (0, (0, 1))

/-- The curvature parameter `ε = R⁻¹` (tex line 2839). -/
def ringEps (R : ℝ) : ℝ := R⁻¹

/-- The physical ring chart `(r, z, t) ↦ (q, η, s) = (R log(r/R), a_r z, a_r² t)`
(tex lines 2842–2843, equation `eq:st18-t00187`). -/
def profileChart (R r z t : ℝ) : ProfilePoint :=
  (logRadius R r, (transverseCoordinate R r z, ageCoordinate R r t))

/-- The cylinder function `F(r,z,t) = f(q, η, s)` attached to a profile `f`. -/
def cylinderLift (R : ℝ) (f : ProfilePoint → ℝ) (r z t : ℝ) : ℝ :=
  f (profileChart R r z t)

/-- Profile partial derivative `∂_q`. -/
def partialQ (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := fderiv ℝ f x eqDir
/-- Profile partial derivative `∂_η`. -/
def partialEta (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := fderiv ℝ f x eηDir
/-- Profile partial derivative `∂_s`. -/
def partialAge (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := fderiv ℝ f x esDir

/-- The scaling operator `K = η∂_η + 2s∂_s` (tex line 2805). -/
def ageOperator (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  x.2.1 * partialEta f x + 2 * x.2.2 * partialAge f x

/-- The curved log-radius derivative `D_ε = ∂_q − εK` (tex line 2844). -/
def ringD (R : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  partialQ f x - ringEps R * ageOperator f x

/-! ## The chart: definitions unfolded and its inverse -/

/-- The chart coordinates are exactly the manuscript's: `a_r = R/r`, `q = R log(r/R)`,
`η = a_r z`, `s = a_r² t` (tex lines 2842–2843). -/
theorem profileChart_eq (R r z t : ℝ) :
    radialScale R r = R / r ∧
    profileChart R r z t =
      (R * Real.log (r / R), ((R / r) * z, (R / r) ^ 2 * t)) := by
  exact ⟨rfl, rfl⟩

/-- Inverse of the ring chart: `r = R e^{q/R}`, `z = η e^{q/R}`, `t = s e^{2q/R}`. -/
def profileChartInv (R : ℝ) (x : ProfilePoint) : ℝ × (ℝ × ℝ) :=
  (R * Real.exp (x.1 / R), (x.2.1 * Real.exp (x.1 / R), x.2.2 * Real.exp (x.1 / R) ^ 2))

/-- The chart is onto `ℝ³`: every profile point is the image of the point
`profileChartInv R x`, which has positive radius. -/
theorem profileChart_profileChartInv (R : ℝ) (hR : 0 < R) (x : ProfilePoint) :
    0 < (profileChartInv R x).1 ∧
    profileChart R (profileChartInv R x).1 (profileChartInv R x).2.1
        (profileChartInv R x).2.2 = x := by
  obtain ⟨q, η, s⟩ := x
  have hE : 0 < Real.exp (q / R) := Real.exp_pos _
  refine ⟨mul_pos hR hE, ?_⟩
  simp only [profileChart, profileChartInv, logRadius, transverseCoordinate, ageCoordinate,
    radialScale]
  have h1 : R * Real.exp (q / R) / R = Real.exp (q / R) := by field_simp
  have h2 : R / (R * Real.exp (q / R)) = (Real.exp (q / R))⁻¹ := by field_simp
  rw [h1, Real.log_exp, h2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
  · simp only
    field_simp
  · simp only
    field_simp

/-- The chart is injective on `r > 0`: the inverse recovers `(r, z, t)`. -/
theorem profileChartInv_profileChart (R r z t : ℝ) (hR : 0 < R) (hr : 0 < r) :
    profileChartInv R (profileChart R r z t) = (r, (z, t)) := by
  have hq : logRadius R r / R = Real.log (r / R) := by
    simp only [logRadius]
    field_simp
  have hE : Real.exp (logRadius R r / R) = r / R := by
    rw [hq, Real.exp_log (div_pos hr hR)]
  simp only [profileChartInv, profileChart, hE, transverseCoordinate, ageCoordinate,
    radialScale]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
  · simp only
    field_simp
  · simp only
    field_simp

/-- The radial scale is itself a cylinder function: `a_r = e^{−εq}` for `r, R > 0`. -/
theorem radialScale_eq_exp (R r : ℝ) (hR : 0 < R) (hr : 0 < r) :
    radialScale R r = Real.exp (-(ringEps R) * logRadius R r) := by
  have h : -(ringEps R) * logRadius R r = Real.log (R / r) := by
    simp only [ringEps, logRadius]
    rw [Real.log_div hr.ne' hR.ne', Real.log_div hR.ne' hr.ne']
    field_simp
    ring
  rw [h, Real.exp_log (div_pos hR hr)]
  rfl

/-! ## Linear algebra of the profile derivative -/

/-- A linear functional on profile space in coordinates. -/
theorem clm_apply_coords (L : ProfilePoint →L[ℝ] ℝ) (a b c : ℝ) :
    L (a, (b, c)) = a * L eqDir + b * L eηDir + c * L esDir := by
  have hv : ((a, (b, c)) : ProfilePoint) = a • eqDir + b • eηDir + c • esDir := by
    simp [eqDir, eηDir, esDir]
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]

/-! ## Derivatives of the chart along the physical coordinate lines -/

/-- Radial derivative of the chart: `∂_r(q, η, s) = (a_r, −η/r, −2s/r)`. -/
theorem hasDerivAt_profileChart_radial (R r z t : ℝ) (hR : R ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun x => profileChart R x z t)
      ((radialScale R r,
        (-transverseCoordinate R r z / r, -2 * ageCoordinate R r t / r)) : ProfilePoint) r :=
  (hasDerivAt_logRadius R r hR hr).prodMk
    ((hasDerivAt_transverseCoordinate_radial R r z hr).prodMk
      (hasDerivAt_ageCoordinate_radial R r t hr))

/-- Axial derivative of the chart: `∂_z(q, η, s) = (0, a_r, 0)`. -/
theorem hasDerivAt_profileChart_axial (R r z t : ℝ) :
    HasDerivAt (fun y => profileChart R r y t)
      (((0 : ℝ), (radialScale R r, (0 : ℝ))) : ProfilePoint) z :=
  (hasDerivAt_const z (logRadius R r)).prodMk
    ((hasDerivAt_transverseCoordinate_axial R r z).prodMk
      (hasDerivAt_const z (ageCoordinate R r t)))

/-- Time derivative of the chart: `∂_t(q, η, s) = (0, 0, a_r²)`. -/
theorem hasDerivAt_profileChart_time (R r z t : ℝ) :
    HasDerivAt (fun τ => profileChart R r z τ)
      (((0 : ℝ), ((0 : ℝ), radialScale R r ^ 2)) : ProfilePoint) t :=
  (hasDerivAt_const t (logRadius R r)).prodMk
    ((hasDerivAt_const t (transverseCoordinate R r z)).prodMk
      (hasDerivAt_ageCoordinate_time R r t))

/-! ## The differentiation rules on cylinder functions (multivariable chain rule) -/

/-- `∂_r = a_r D_ε` on cylinder functions, `HasFDerivAt` form (tex line 2848):
if `f` has derivative `f'` at `(q, η, s)` then
`∂_r F = a_r (f' e_q − ε(η f' e_η + 2s f' e_s))`. -/
theorem hasDerivAt_cylinderLift_radial (R r z t : ℝ) (hR : R ≠ 0) (hr : r ≠ 0)
    (f : ProfilePoint → ℝ) (f' : ProfilePoint →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' (profileChart R r z t)) :
    HasDerivAt (fun x => cylinderLift R f x z t)
      (radialScale R r * (f' eqDir - ringEps R *
        (transverseCoordinate R r z * f' eηDir + 2 * ageCoordinate R r t * f' esDir))) r := by
  have h := hf.comp_hasDerivAt r (hasDerivAt_profileChart_radial R r z t hR hr)
  have he : f' ((radialScale R r,
        (-transverseCoordinate R r z / r, -2 * ageCoordinate R r t / r)) : ProfilePoint) =
      radialScale R r * (f' eqDir - ringEps R *
        (transverseCoordinate R r z * f' eηDir + 2 * ageCoordinate R r t * f' esDir)) := by
    rw [clm_apply_coords]
    simp only [radialScale, ringEps]
    field_simp
    ring
  rw [he] at h
  exact h

/-- `∂_z = a_r ∂_η` on cylinder functions, `HasFDerivAt` form (tex line 2849). -/
theorem hasDerivAt_cylinderLift_axial (R r z t : ℝ)
    (f : ProfilePoint → ℝ) (f' : ProfilePoint →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' (profileChart R r z t)) :
    HasDerivAt (fun y => cylinderLift R f r y t) (radialScale R r * f' eηDir) z := by
  have h := hf.comp_hasDerivAt z (hasDerivAt_profileChart_axial R r z t)
  have he : f' (((0 : ℝ), (radialScale R r, (0 : ℝ))) : ProfilePoint) =
      radialScale R r * f' eηDir := by
    rw [clm_apply_coords]
    ring
  rw [he] at h
  exact h

/-- `∂_t = a_r² ∂_s` on cylinder functions, `HasFDerivAt` form (tex line 2850). -/
theorem hasDerivAt_cylinderLift_time (R r z t : ℝ)
    (f : ProfilePoint → ℝ) (f' : ProfilePoint →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' (profileChart R r z t)) :
    HasDerivAt (fun τ => cylinderLift R f r z τ) (radialScale R r ^ 2 * f' esDir) t := by
  have h := hf.comp_hasDerivAt t (hasDerivAt_profileChart_time R r z t)
  have he : f' (((0 : ℝ), ((0 : ℝ), radialScale R r ^ 2)) : ProfilePoint) =
      radialScale R r ^ 2 * f' esDir := by
    rw [clm_apply_coords]
    ring
  rw [he] at h
  exact h

/-- `∂_r = a_r D_ε` as an identity of cylinder functions (tex line 2848):
`∂_r [f(q,η,s)] = a_r (D_ε f)(q,η,s)`. -/
theorem hasDerivAt_cylinderLift_radial_ringD (R r z t : ℝ) (hR : R ≠ 0) (hr : r ≠ 0)
    (f : ProfilePoint → ℝ) (hf : DifferentiableAt ℝ f (profileChart R r z t)) :
    HasDerivAt (fun x => cylinderLift R f x z t)
      (radialScale R r * cylinderLift R (ringD R f) r z t) r := by
  have h := hasDerivAt_cylinderLift_radial R r z t hR hr f _ hf.hasFDerivAt
  simpa [cylinderLift, ringD, ageOperator, partialQ, partialEta, partialAge,
    profileChart] using h

/-- `∂_z = a_r ∂_η` as an identity of cylinder functions (tex line 2849). -/
theorem hasDerivAt_cylinderLift_axial_partialEta (R r z t : ℝ)
    (f : ProfilePoint → ℝ) (hf : DifferentiableAt ℝ f (profileChart R r z t)) :
    HasDerivAt (fun y => cylinderLift R f r y t)
      (radialScale R r * cylinderLift R (partialEta f) r z t) z :=
  hasDerivAt_cylinderLift_axial R r z t f _ hf.hasFDerivAt

/-- `∂_t = a_r² ∂_s` as an identity of cylinder functions (tex line 2850). -/
theorem hasDerivAt_cylinderLift_time_partialAge (R r z t : ℝ)
    (f : ProfilePoint → ℝ) (hf : DifferentiableAt ℝ f (profileChart R r z t)) :
    HasDerivAt (fun τ => cylinderLift R f r z τ)
      (radialScale R r ^ 2 * cylinderLift R (partialAge f) r z t) t :=
  hasDerivAt_cylinderLift_time R r z t f _ hf.hasFDerivAt

/-- **Unit B0184** (`eq:st18-t00187`, tex lines 2837–2850). Let `R ≥ 2`, `ε = R⁻¹`,
`r > 0` and `t > 0`. For every profile `f(q, η, s)` differentiable at the chart image of
`(r, z, t)`, the cylinder function `F = f(q, η, s)` satisfies
`∂_r F = a_r D_ε f`, `∂_z F = a_r ∂_η f` and `∂_t F = a_r² ∂_s f`
(tex lines 2847–2850), where `D_ε = ∂_q − εK`, `K = η∂_η + 2s∂_s`. -/
theorem ringChart_differentiation_rules (R r z t : ℝ) (hR : 2 ≤ R) (hr : 0 < r)
    (_ht : 0 < t) (f : ProfilePoint → ℝ)
    (hf : DifferentiableAt ℝ f (profileChart R r z t)) :
    deriv (fun x => cylinderLift R f x z t) r =
        radialScale R r * cylinderLift R (ringD R f) r z t ∧
    deriv (fun y => cylinderLift R f r y t) z =
        radialScale R r * cylinderLift R (partialEta f) r z t ∧
    deriv (fun τ => cylinderLift R f r z τ) t =
        radialScale R r ^ 2 * cylinderLift R (partialAge f) r z t := by
  have hR0 : R ≠ 0 := by linarith
  exact ⟨(hasDerivAt_cylinderLift_radial_ringD R r z t hR0 hr.ne' f hf).deriv,
    (hasDerivAt_cylinderLift_axial_partialEta R r z t f hf).deriv,
    (hasDerivAt_cylinderLift_time_partialAge R r z t f hf).deriv⟩

/-- **Unit B0184, operator form** (tex lines 2847–2850). For a profile `f` that is
differentiable everywhere (the manuscript's cylinder functions are smooth), the three
differentiation rules hold as identities of functions on the physical domain
`r > 0`, `t > 0`: `∂_r ∘ lift = a_r · lift ∘ D_ε`, `∂_z ∘ lift = a_r · lift ∘ ∂_η`,
`∂_t ∘ lift = a_r² · lift ∘ ∂_s`. -/
theorem ringChart_differentiation_rules_on_domain (R : ℝ) (hR : 2 ≤ R)
    (f : ProfilePoint → ℝ) (hf : Differentiable ℝ f) :
    ∀ r z t : ℝ, 0 < r → 0 < t →
      deriv (fun x => cylinderLift R f x z t) r =
          radialScale R r * cylinderLift R (ringD R f) r z t ∧
      deriv (fun y => cylinderLift R f r y t) z =
          radialScale R r * cylinderLift R (partialEta f) r z t ∧
      deriv (fun τ => cylinderLift R f r z τ) t =
          radialScale R r ^ 2 * cylinderLift R (partialAge f) r z t :=
  fun r z t hr ht => ringChart_differentiation_rules R r z t hR hr ht f (hf _)

end UnforcedLeray.B0184
