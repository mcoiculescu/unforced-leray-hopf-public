import UnforcedLeray.Lib.PlanarSectorsB.LaterIdentitiesB
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane

/-!
# The plane angular-two stress identities `E_q = iC`, `E_η = -E_q` (INF12 P10: B0388)


§5, Level P, target **P10** (B0388: "polar integrals of `e^{2iϑ}` against `cos²ϑ`, `sinϑcosϑ`,
`sin²ϑ`; velocity of a sector-two stream function").

Manuscript (`paper/main.tex`): the stress moments `E_η = (2/c)∫v₁u₁`, `E_q = (2/c)∫v₂u₂`,
`C = (1/c)∫(v₁u₂ + v₂u₁)` (`eq:st18-t00383`, lines 6955–6962) and "the plane radial
angular-two identity is `E_q = iC` and `E_η = -E_q`" (lines 7004–7005, unit `B0388`), for the
plane radial vortex `V₀ = Ω(r)y^⊥` (`eq:st18-t00001`, line 638) and the perturbation velocity
`u = ∇^⊥Ψ` of an angular-two stream `Ψ = ψ(r)e^{2iϑ}`.

Main declarations (namespace `UnforcedLeray.Planar`):
* `fderiv_ofProfile_two_one`, `fderiv_ofProfile_two_I`: the Cartesian partial derivatives of
  `Ψ = ψ(r)e^{2iϑ}` at `y = re^{iθ} ≠ 0`:
  `∂₁Ψ = e^{2iθ}(ψ' cosθ - (2iψ/r) sinθ)`, `∂₂Ψ = e^{2iθ}(ψ' sinθ + (2iψ/r) cosθ)`;
* `vortexV1`, `vortexV2` (`V₀ = Ω(r)y^⊥`), `streamU1`, `streamU2` (`u = (-∂₂Ψ, ∂₁Ψ)`);
* `integral_v2u2`, `integral_v1u2_add_v2u1`, `integral_v1u1`:
  `∫v₂u₂ = (π/2)I`, `∫(v₁u₂ + v₂u₁) = -iπI`, `∫v₁u₁ = -(π/2)I`, `I = ∫₀^∞Ω r(ψ' + 2ψ/r)r dr`;
* **`stressEq_eq_I_mul_stressC`** (`E_q = iC`) and **`stressEη_eq_neg_stressEq`**
  (`E_η = -E_q`), hence `D_c = R_c = 0` in the plane (`stressDefects_eq_zero`).

Hypotheses: `ψ` has derivative `ψ'(r)` at every `r > 0`, and `r·Ω(r) r(|ψ'| + 2|ψ|/r)` is
integrable on `(0, ∞)` (`stressDom`; this makes the three plane moments absolutely convergent).
The moments are plane integrals over all of `ℝ²` ("cell-free"). The convergence of the actual
scaled defects on fixed `θ` intervals (second half of B0388) is not built.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real Metric
open scoped ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialOmega_pos)
open UnforcedLeray.Planar.NUE

/-! ### Angular integrals against `e^{2iϑ}` -/

theorem exp_two_mul_eq (θ : ℝ) :
    Complex.exp (2 * θ * Complex.I) = Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I) := by
  push_cast
  ring_nf

/-- `∫₀^{2π} cos²ϑ e^{2iϑ} dϑ = π/2`. -/
theorem integral_cos_sq_mul_exp_two :
    ∫ θ in (0 : ℝ)..2 * π, ((Real.cos θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I) =
      (π : ℂ) / 2 := by
  have hpt : ∀ θ : ℝ, ((Real.cos θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I) =
      (1 / 4) * Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I) +
        (1 / 2) * Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I) + 1 / 4 := by
    intro θ
    set X := Complex.exp (θ * Complex.I) with hX
    have hX0 : X ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (2 * θ * Complex.I) = X ^ 2 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h2' : Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I) = X ^ 2 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h4 : Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I) = X ^ 4 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hc : ((Real.cos θ : ℝ) : ℂ) = (X + X⁻¹) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos, hX, ← Complex.exp_neg]
      congr 2
      ring_nf
    rw [h2, h2', h4, hc]
    field_simp
    ring
  simp_rw [hpt]
  have hc1 : IntervalIntegrable (fun θ : ℝ => (1 / 4 : ℂ) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => (1 / 4 : ℂ) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ : ℝ => (1 / 2 : ℂ) *
      Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => (1 / 2 : ℂ) *
      Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc1.add hc2) intervalIntegrable_const,
    intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_exp_int_mul_I (by norm_num : (4 : ℤ) ≠ 0),
    integral_exp_int_mul_I (by norm_num : (2 : ℤ) ≠ 0), intervalIntegral.integral_const]
  simp only [sub_zero, mul_zero, zero_add, Complex.real_smul]
  push_cast
  ring

/-- `∫₀^{2π} sinϑ cosϑ e^{2iϑ} dϑ = iπ/2`. -/
theorem integral_sin_mul_cos_mul_exp_two :
    ∫ θ in (0 : ℝ)..2 * π, ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) *
        Complex.exp (2 * θ * Complex.I) = Complex.I * (π : ℂ) / 2 := by
  have hpt : ∀ θ : ℝ, ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) *
      Complex.exp (2 * θ * Complex.I) =
      -(Complex.I / 4) * Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I) + Complex.I / 4 := by
    intro θ
    set X := Complex.exp (θ * Complex.I) with hX
    have hX0 : X ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (2 * θ * Complex.I) = X ^ 2 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h4 : Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I) = X ^ 4 := by
      rw [hX, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hc : ((Real.cos θ : ℝ) : ℂ) = (X + X⁻¹) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos, hX, ← Complex.exp_neg]
      congr 2
      ring_nf
    have hs : ((Real.sin θ : ℝ) : ℂ) = (X⁻¹ - X) * Complex.I / 2 := by
      rw [Complex.ofReal_sin, Complex.sin, hX, ← Complex.exp_neg]
      congr 2
      ring_nf
    rw [h2, h4, hc, hs]
    field_simp
    ring_nf
  simp_rw [hpt]
  have hc1 : IntervalIntegrable (fun θ : ℝ => -(Complex.I / 4) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => -(Complex.I / 4) *
      Complex.exp (((4 : ℤ) : ℂ) * θ * Complex.I)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_exp_int_mul_I (by norm_num : (4 : ℤ) ≠ 0),
    intervalIntegral.integral_const]
  simp only [sub_zero, mul_zero, zero_add, Complex.real_smul]
  push_cast
  ring

/-! ### Partial derivatives of the angular-two stream -/

theorem angPhase_two_eq (y : ℂ) : Ang.angPhase 2 y = (y / (‖y‖ : ℂ)) ^ 2 := by
  rw [Ang.angPhase]
  norm_cast

theorem differentiableAt_ofProfile_two {ψ : ℝ → ℂ} {y : ℂ} (hy : y ≠ 0)
    (hψ : DifferentiableAt ℝ ψ ‖y‖) : DifferentiableAt ℝ (Ang.ofProfile 2 ψ) y := by
  have e : Ang.ofProfile 2 ψ = fun z : ℂ => ψ ‖z‖ * (z / (‖z‖ : ℂ)) ^ 2 := by
    funext z
    rw [Ang.ofProfile, angPhase_two_eq]
  rw [e]
  have hid : DifferentiableAt ℝ (fun z : ℂ => z) y := differentiableAt_id
  have hn : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) y := hid.norm ℝ hy
  have hn' : DifferentiableAt ℝ (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y hn
  have hy' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
  have hinv : DifferentiableAt ℝ (fun z : ℂ => (((‖z‖ : ℝ) : ℂ))⁻¹) y :=
    ((differentiableAt_inv (𝕜 := ℂ) hy').restrictScalars ℝ).comp y hn'
  have hq : DifferentiableAt ℝ (fun z : ℂ => z / ((‖z‖ : ℝ) : ℂ)) y := by
    simp_rw [div_eq_mul_inv]
    exact hid.mul hinv
  have hq2 : DifferentiableAt ℝ (fun z : ℂ => (z / ((‖z‖ : ℝ) : ℂ)) ^ 2) y := hq.pow 2
  have hg : DifferentiableAt ℝ (fun z : ℂ => ψ ‖z‖) y := hψ.comp y hn
  exact hg.mul hq2

/-- The radial derivative: `DΨ(y)[y] = |y| ψ'(|y|) e^{2iϑ}`. -/
theorem fderiv_ofProfile_two_radial {ψ : ℝ → ℂ} {ψ' : ℂ} {y : ℂ} (hy : y ≠ 0)
    (hψ : HasDerivAt ψ ψ' ‖y‖) :
    fderiv ℝ (Ang.ofProfile 2 ψ) y y = ‖y‖ * ψ' * Ang.angPhase 2 y := by
  have hd := (differentiableAt_ofProfile_two hy hψ.differentiableAt).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => y + t • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add y
  have h1' : HasFDerivAt (Ang.ofProfile 2 ψ) (fderiv ℝ (Ang.ofProfile 2 ψ) y)
      (y + (0 : ℝ) • y) := by
    rw [zero_smul, add_zero]
    exact hd
  have hc := h1'.comp_hasDerivAt (0 : ℝ) h1
  -- the radial line
  have hr : HasDerivAt (fun t : ℝ => ψ ((1 + t) * ‖y‖) * Ang.angPhase 2 y)
      (ψ' * ‖y‖ * Ang.angPhase 2 y) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => (1 + t) * ‖y‖) ‖y‖ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖y‖
    have hψ' : HasDerivAt ψ ψ' ((1 + 0) * ‖y‖) := by
      rw [add_zero, one_mul]
      exact hψ
    exact ((hψ'.scomp (0 : ℝ) h2).mul_const (Ang.angPhase 2 y)).congr_deriv
      (by rw [Complex.real_smul]; ring)
  have hev : (fun t : ℝ => Ang.ofProfile 2 ψ (y + t • y)) =ᶠ[𝓝 0]
      fun t : ℝ => ψ ((1 + t) * ‖y‖) * Ang.angPhase 2 y := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
    have ht' : 0 < 1 + t := by
      have : -1 < t := ht
      linarith
    have e : y + t • y = (1 + t) • y := by rw [add_smul, one_smul]
    rw [e, Ang.ofProfile, norm_smul, Real.norm_of_nonneg ht'.le, angPhase_smul ht']
  have := hc.unique (hr.congr_of_eventuallyEq hev)
  rw [this]
  ring

/-- **The Cartesian partials of `Ψ = ψ(r)e^{2iϑ}`** at `y ≠ 0`:
`∂₁Ψ = e^{2iϑ}(ψ' y₁/r - 2iψ y₂/r²)`. -/
theorem fderiv_ofProfile_two_one {ψ : ℝ → ℂ} {ψ' : ℂ} {y : ℂ} (hy : y ≠ 0)
    (hψ : HasDerivAt ψ ψ' ‖y‖) :
    fderiv ℝ (Ang.ofProfile 2 ψ) y 1 = Ang.angPhase 2 y *
      (ψ' * ((y.re / ‖y‖ : ℝ) : ℂ) -
        2 * Complex.I * ψ ‖y‖ / (‖y‖ : ℂ) * ((y.im / ‖y‖ : ℝ) : ℂ)) := by
  set L := fderiv ℝ (Ang.ofProfile 2 ψ) y
  have hd := (differentiableAt_ofProfile_two hy hψ.differentiableAt).hasFDerivAt
  have hrot := fderiv_sector_rot (n := 2) hd (ofProfile_rot 2 ψ · y)
  have hrad := fderiv_ofProfile_two_radial hy hψ
  have e1 : L y = y.re * L 1 + y.im * L Complex.I := by
    have : y = y.re • (1 : ℂ) + y.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have e2 : L (Complex.I * y) = -y.im * L 1 + y.re * L Complex.I := by
    have : Complex.I * y = (-y.im) • (1 : ℂ) + y.re • Complex.I := by
      apply Complex.ext <;> simp
    rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
  have hsq : (y.re : ℂ) ^ 2 + (y.im : ℂ) ^ 2 = (‖y‖ : ℂ) ^ 2 := by
    have := Complex.sq_norm y
    rw [Complex.normSq_apply] at this
    exact_mod_cast (by rw [this]; ring : y.re ^ 2 + y.im ^ 2 = ‖y‖ ^ 2)
  rw [Ang.ofProfile] at hrot
  have eq1 := e1.symm.trans hrad
  have eq2 := e2.symm.trans hrot
  have hA : (‖y‖ : ℂ) ^ 2 * L 1 = Ang.angPhase 2 y *
      (ψ' * y.re * ‖y‖ - 2 * Complex.I * ψ ‖y‖ * y.im) := by
    push_cast at eq2
    linear_combination (y.re : ℂ) * eq1 - (y.im : ℂ) * eq2 - L 1 * hsq
  have hr2 : (‖y‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  calc L 1 = ((‖y‖ : ℂ) ^ 2 * L 1) / (‖y‖ : ℂ) ^ 2 := by field_simp
    _ = _ := by
      rw [hA]
      push_cast
      field_simp

/-- `∂₂Ψ = e^{2iϑ}(ψ' y₂/r + 2iψ y₁/r²)`. -/
theorem fderiv_ofProfile_two_I {ψ : ℝ → ℂ} {ψ' : ℂ} {y : ℂ} (hy : y ≠ 0)
    (hψ : HasDerivAt ψ ψ' ‖y‖) :
    fderiv ℝ (Ang.ofProfile 2 ψ) y Complex.I = Ang.angPhase 2 y *
      (ψ' * ((y.im / ‖y‖ : ℝ) : ℂ) +
        2 * Complex.I * ψ ‖y‖ / (‖y‖ : ℂ) * ((y.re / ‖y‖ : ℝ) : ℂ)) := by
  set L := fderiv ℝ (Ang.ofProfile 2 ψ) y
  have hd := (differentiableAt_ofProfile_two hy hψ.differentiableAt).hasFDerivAt
  have hrot := fderiv_sector_rot (n := 2) hd (ofProfile_rot 2 ψ · y)
  have hrad := fderiv_ofProfile_two_radial hy hψ
  have e1 : L y = y.re * L 1 + y.im * L Complex.I := by
    have : y = y.re • (1 : ℂ) + y.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have e2 : L (Complex.I * y) = -y.im * L 1 + y.re * L Complex.I := by
    have : Complex.I * y = (-y.im) • (1 : ℂ) + y.re • Complex.I := by
      apply Complex.ext <;> simp
    rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
  have hsq : (y.re : ℂ) ^ 2 + (y.im : ℂ) ^ 2 = (‖y‖ : ℂ) ^ 2 := by
    have := Complex.sq_norm y
    rw [Complex.normSq_apply] at this
    exact_mod_cast (by rw [this]; ring : y.re ^ 2 + y.im ^ 2 = ‖y‖ ^ 2)
  rw [Ang.ofProfile] at hrot
  have eq1 := e1.symm.trans hrad
  have eq2 := e2.symm.trans hrot
  have hB : (‖y‖ : ℂ) ^ 2 * L Complex.I = Ang.angPhase 2 y *
      (ψ' * y.im * ‖y‖ + 2 * Complex.I * ψ ‖y‖ * y.re) := by
    push_cast at eq2
    linear_combination (y.im : ℂ) * eq1 + (y.re : ℂ) * eq2 - L Complex.I * hsq
  have hr2 : (‖y‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  calc L Complex.I = ((‖y‖ : ℂ) ^ 2 * L Complex.I) / (‖y‖ : ℂ) ^ 2 := by field_simp
    _ = _ := by
      rw [hB]
      push_cast
      field_simp

/-! ### The velocities and the stress moments -/

/-- The plane radial vortex velocity `V₀ = Ω(r)y^⊥`, `y^⊥ = (-y₂, y₁)` (`eq:st18-t00001`,
`paper/main.tex` line 638), first component. -/
def vortexV1 (y : ℂ) : ℂ := -((radialOmega ‖y‖ * y.im : ℝ) : ℂ)

/-- Second component of `V₀ = Ω(r)y^⊥`. -/
def vortexV2 (y : ℂ) : ℂ := ((radialOmega ‖y‖ * y.re : ℝ) : ℂ)

/-- The velocity `u = ∇^⊥Ψ = (-∂₂Ψ, ∂₁Ψ)` of the angular-two stream `Ψ = ψ(r)e^{2iϑ}`, first
component (`∂₂Ψ = DΨ(y)[i]`). -/
def streamU1 (ψ : ℝ → ℂ) (y : ℂ) : ℂ := -fderiv ℝ (Ang.ofProfile 2 ψ) y Complex.I

/-- Second component of `u = ∇^⊥Ψ` (`∂₁Ψ = DΨ(y)[1]`). -/
def streamU2 (ψ : ℝ → ℂ) (y : ℂ) : ℂ := fderiv ℝ (Ang.ofProfile 2 ψ) y 1

/-- `I = ∫₀^∞ Ω r (ψ' + 2ψ/r) r dr`. -/
def stressI (ψ ψ' : ℝ → ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), ((radialOmega r * r : ℝ) : ℂ) * (ψ' r + 2 * ψ r / r) * r

/-- `E_η = (2/c)∫v₁u₁` (`eq:st18-t00383`, `paper/main.tex` line 6957, in the plane). -/
def stressEη (c : ℂ) (ψ : ℝ → ℂ) : ℂ := 2 / c * ∫ y : ℂ, vortexV1 y * streamU1 ψ y

/-- `E_q = (2/c)∫v₂u₂` (line 6958). -/
def stressEq (c : ℂ) (ψ : ℝ → ℂ) : ℂ := 2 / c * ∫ y : ℂ, vortexV2 y * streamU2 ψ y

/-- `C = (1/c)∫(v₁u₂ + v₂u₁)` (line 6959). -/
def stressC (c : ℂ) (ψ : ℝ → ℂ) : ℂ :=
  1 / c * ∫ y : ℂ, (vortexV1 y * streamU2 ψ y + vortexV2 y * streamU1 ψ y)

/-! ### Angular combination -/

theorem angular_combo (a b c : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, (a * ((Real.cos θ : ℝ) : ℂ) ^ 2 +
        b * (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) +
        c * ((Real.sin θ : ℝ) : ℂ) ^ 2) * Complex.exp (2 * θ * Complex.I) =
      a * ((π : ℂ) / 2) + b * (Complex.I * (π : ℂ) / 2) - c * ((π : ℂ) / 2) := by
  have e : ∀ θ : ℝ, (a * ((Real.cos θ : ℝ) : ℂ) ^ 2 +
      b * (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) +
      c * ((Real.sin θ : ℝ) : ℂ) ^ 2) * Complex.exp (2 * θ * Complex.I) =
      a * (((Real.cos θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I)) +
      b * (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) * Complex.exp (2 * θ * Complex.I)) +
      c * (((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I)) := fun θ => by ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun θ : ℝ =>
      a * (((Real.cos θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I))) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      a * (((Real.cos θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => b * (((Real.sin θ : ℝ) : ℂ) *
      ((Real.cos θ : ℝ) : ℂ) * Complex.exp (2 * θ * Complex.I))) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => b * (((Real.sin θ : ℝ) : ℂ) *
      ((Real.cos θ : ℝ) : ℂ) * Complex.exp (2 * θ * Complex.I))).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ : ℝ =>
      c * (((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I))) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      c * (((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.exp (2 * θ * Complex.I))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq_mul_exp_two,
    integral_sin_mul_cos_mul_exp_two, integral_sin_sq_mul_exp_two]
  ring

/-! ### Polar evaluation and integrability -/

theorem integral_plane_of_circle {F : ℂ → ℂ} (hF : Integrable F) {G : ℝ → ℂ}
    (hG : ∀ r : ℝ, 0 < r → ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) = G r) :
    ∫ y, F y = ∫ r in Ioi (0 : ℝ), (r : ℂ) * G r := by
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hF]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [hG r hr, Complex.real_smul]

theorem integrable_of_radial_bound {F : ℂ → ℂ} (hFm : AEStronglyMeasurable F volume)
    {H : ℝ → ℝ} (hH : IntegrableOn (fun r => r * H r) (Ioi 0))
    (hb : ∀ y : ℂ, y ≠ 0 → ‖F y‖ ≤ H ‖y‖) : Integrable F := by
  have h1 : Integrable (fun y : ℂ => H ‖y‖) :=
    Polar.integrable_comp_norm_iff.2 (by simpa only [smul_eq_mul] using hH)
  refine h1.mono' hFm ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with y hy
  exact hb y hy

/-- The dominating radial function `Ω(r) r (|ψ'| + 2|ψ|/r)`. -/
def stressDom (ψ ψ' : ℝ → ℂ) (r : ℝ) : ℝ := radialOmega r * r * (‖ψ' r‖ + 2 * ‖ψ r‖ / r)

theorem norm_vortexV1_le (y : ℂ) : ‖vortexV1 y‖ ≤ radialOmega ‖y‖ * ‖y‖ := by
  rw [vortexV1, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (radialOmega_pos _)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm y) (radialOmega_pos _).le

theorem norm_vortexV2_le (y : ℂ) : ‖vortexV2 y‖ ≤ radialOmega ‖y‖ * ‖y‖ := by
  rw [vortexV2, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (radialOmega_pos _)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm y) (radialOmega_pos _).le

theorem norm_partial_le (ψ' ψr : ℂ) {y : ℂ} (hy : y ≠ 0) (a b : ℝ) (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (sgn : ℂ) (hs : ‖sgn‖ = 1) :
    ‖Ang.angPhase 2 y * (ψ' * (a : ℂ) + sgn * (2 * Complex.I * ψr / (‖y‖ : ℂ) * (b : ℂ)))‖ ≤
      ‖ψ'‖ + 2 * ‖ψr‖ / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [norm_mul, Ang.norm_angPhase hy, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hs, one_mul, norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hn, Complex.norm_ofNat]
  have h1 : ‖ψ'‖ * |a| ≤ ‖ψ'‖ := by
    calc ‖ψ'‖ * |a| ≤ ‖ψ'‖ * 1 := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ = ‖ψ'‖ := mul_one _
  have h2 : 2 * 1 * ‖ψr‖ / ‖y‖ * |b| ≤ 2 * ‖ψr‖ / ‖y‖ := by
    have : 0 ≤ 2 * 1 * ‖ψr‖ / ‖y‖ := by positivity
    calc 2 * 1 * ‖ψr‖ / ‖y‖ * |b| ≤ 2 * 1 * ‖ψr‖ / ‖y‖ * 1 := mul_le_mul_of_nonneg_left hb this
      _ = 2 * ‖ψr‖ / ‖y‖ := by ring
  rw [Real.norm_eq_abs]
  linarith

theorem streamU2_eq {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {y : ℂ}
    (hy : y ≠ 0) :
    streamU2 ψ y = Ang.angPhase 2 y * (ψ' ‖y‖ * ((y.re / ‖y‖ : ℝ) : ℂ) +
      (-1) * (2 * Complex.I * ψ ‖y‖ / (‖y‖ : ℂ) * ((y.im / ‖y‖ : ℝ) : ℂ))) := by
  rw [streamU2, fderiv_ofProfile_two_one hy (hψ _ (norm_pos_iff.2 hy))]
  ring

theorem streamU1_eq {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {y : ℂ}
    (hy : y ≠ 0) :
    streamU1 ψ y = -(Ang.angPhase 2 y * (ψ' ‖y‖ * ((y.im / ‖y‖ : ℝ) : ℂ) +
      1 * (2 * Complex.I * ψ ‖y‖ / (‖y‖ : ℂ) * ((y.re / ‖y‖ : ℝ) : ℂ)))) := by
  rw [streamU1, fderiv_ofProfile_two_I hy (hψ _ (norm_pos_iff.2 hy))]
  ring

theorem norm_streamU2_le {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {y : ℂ}
    (hy : y ≠ 0) : ‖streamU2 ψ y‖ ≤ ‖ψ' ‖y‖‖ + 2 * ‖ψ ‖y‖‖ / ‖y‖ := by
  rw [streamU2_eq hψ hy]
  exact norm_partial_le _ _ hy _ _ (abs_re_div_norm_le_one y) (abs_im_div_norm_le_one y) _
    (by simp)

theorem norm_streamU1_le {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {y : ℂ}
    (hy : y ≠ 0) : ‖streamU1 ψ y‖ ≤ ‖ψ' ‖y‖‖ + 2 * ‖ψ ‖y‖‖ / ‖y‖ := by
  rw [streamU1_eq hψ hy, norm_neg]
  exact norm_partial_le _ _ hy _ _ (abs_im_div_norm_le_one y) (abs_re_div_norm_le_one y) _
    (by simp)

theorem measurable_streamU1 (ψ : ℝ → ℂ) : Measurable (streamU1 ψ) :=
  (measurable_fderiv_apply_const ℝ (Ang.ofProfile 2 ψ) Complex.I).neg

theorem measurable_streamU2 (ψ : ℝ → ℂ) : Measurable (streamU2 ψ) :=
  measurable_fderiv_apply_const ℝ (Ang.ofProfile 2 ψ) 1

theorem continuous_vortexV1 : Continuous vortexV1 :=
  (Complex.continuous_ofReal.comp ((B0012.continuous_radialOmega.comp continuous_norm).mul
    Complex.continuous_im)).neg

theorem continuous_vortexV2 : Continuous vortexV2 :=
  Complex.continuous_ofReal.comp ((B0012.continuous_radialOmega.comp continuous_norm).mul
    Complex.continuous_re)

theorem norm_mul_le_dom {ψ ψ' : ℝ → ℂ} {v u : ℂ} {y : ℂ}
    (hv : ‖v‖ ≤ radialOmega ‖y‖ * ‖y‖) (hu : ‖u‖ ≤ ‖ψ' ‖y‖‖ + 2 * ‖ψ ‖y‖‖ / ‖y‖) :
    ‖v * u‖ ≤ stressDom ψ ψ' ‖y‖ := by
  rw [norm_mul, stressDom]
  exact mul_le_mul hv hu (norm_nonneg _) (by have := radialOmega_pos ‖y‖; positivity)

/-! ### The three plane moments -/

theorem circleMap_ne_zero' {r : ℝ} (hr : 0 < r) (θ : ℝ) : circleMap 0 r θ ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_circleMap_zero, abs_of_pos hr]
  exact hr.ne'

/-- Shorthand `Ω(r) r` as a complex number. -/
abbrev omr (r : ℝ) : ℂ := ((radialOmega r * r : ℝ) : ℂ)

theorem v2u2_circle {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    vortexV2 (circleMap 0 r θ) * streamU2 ψ (circleMap 0 r θ) =
      (omr r * ψ' r * ((Real.cos θ : ℝ) : ℂ) ^ 2 +
        (-(omr r * (2 * Complex.I * ψ r / r))) *
          (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) +
        0 * ((Real.sin θ : ℝ) : ℂ) ^ 2) * Complex.exp (2 * θ * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [streamU2_eq hψ (circleMap_ne_zero' hr θ), vortexV2, norm_circleMap_zero, abs_of_pos hr,
    circleMap_zero_re, circleMap_zero_im, angPhase_circleMap hr]
  push_cast
  field_simp
  ring

theorem v1u1_circle {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    vortexV1 (circleMap 0 r θ) * streamU1 ψ (circleMap 0 r θ) =
      (0 * ((Real.cos θ : ℝ) : ℂ) ^ 2 +
        omr r * (2 * Complex.I * ψ r / r) * (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) +
        omr r * ψ' r * ((Real.sin θ : ℝ) : ℂ) ^ 2) * Complex.exp (2 * θ * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [streamU1_eq hψ (circleMap_ne_zero' hr θ), vortexV1, norm_circleMap_zero, abs_of_pos hr,
    circleMap_zero_re, circleMap_zero_im, angPhase_circleMap hr]
  push_cast
  field_simp
  ring

theorem cross_circle {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    vortexV1 (circleMap 0 r θ) * streamU2 ψ (circleMap 0 r θ) +
        vortexV2 (circleMap 0 r θ) * streamU1 ψ (circleMap 0 r θ) =
      ((-(omr r * (2 * Complex.I * ψ r / r))) * ((Real.cos θ : ℝ) : ℂ) ^ 2 +
        (-(2 * omr r * ψ' r)) * (((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) +
        omr r * (2 * Complex.I * ψ r / r) * ((Real.sin θ : ℝ) : ℂ) ^ 2) *
          Complex.exp (2 * θ * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [streamU1_eq hψ (circleMap_ne_zero' hr θ), streamU2_eq hψ (circleMap_ne_zero' hr θ),
    vortexV1, vortexV2, norm_circleMap_zero, abs_of_pos hr, circleMap_zero_re, circleMap_zero_im,
    angPhase_circleMap hr]
  push_cast
  field_simp
  ring

theorem aesm_vu {f g : ℂ → ℂ} (hf : Continuous f) (hg : Measurable g) :
    AEStronglyMeasurable (fun y => f y * g y) volume :=
  (hf.measurable.mul hg).aestronglyMeasurable

/-- **`∫v₂u₂ = (π/2) I`** (B0388, `paper/main.tex` lines 7004–7005). -/
theorem integral_v2u2 {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) :
    ∫ y : ℂ, vortexV2 y * streamU2 ψ y = (π : ℂ) / 2 * stressI ψ ψ' := by
  have hF : Integrable fun y : ℂ => vortexV2 y * streamU2 ψ y :=
    integrable_of_radial_bound (aesm_vu continuous_vortexV2 (measurable_streamU2 ψ)) hI
      fun y hy => norm_mul_le_dom (norm_vortexV2_le y) (norm_streamU2_le hψ hy)
  rw [integral_plane_of_circle hF (G := fun r => omr r * ψ' r * ((π : ℂ) / 2) +
      (-(omr r * (2 * Complex.I * ψ r / r))) * (Complex.I * (π : ℂ) / 2) - 0 * ((π : ℂ) / 2))
    (fun r hr => by simp_rw [v2u2_circle hψ hr]; exact angular_combo _ _ _),
    stressI, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < r from hr).ne'
  simp only [omr]
  field_simp
  linear_combination (-(2 : ℂ) * ((radialOmega r * r : ℝ) : ℂ) * ψ r) * Complex.I_sq

/-- **`∫v₁u₁ = -(π/2) I`** (B0388). -/
theorem integral_v1u1 {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) :
    ∫ y : ℂ, vortexV1 y * streamU1 ψ y = -((π : ℂ) / 2 * stressI ψ ψ') := by
  have hF : Integrable fun y : ℂ => vortexV1 y * streamU1 ψ y :=
    integrable_of_radial_bound (aesm_vu continuous_vortexV1 (measurable_streamU1 ψ)) hI
      fun y hy => norm_mul_le_dom (norm_vortexV1_le y) (norm_streamU1_le hψ hy)
  rw [integral_plane_of_circle hF (G := fun r => 0 * ((π : ℂ) / 2) +
      omr r * (2 * Complex.I * ψ r / r) * (Complex.I * (π : ℂ) / 2) -
        omr r * ψ' r * ((π : ℂ) / 2))
    (fun r hr => by simp_rw [v1u1_circle hψ hr]; exact angular_combo _ _ _),
    stressI, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < r from hr).ne'
  simp only [omr]
  field_simp
  linear_combination ((2 : ℂ) * ((radialOmega r * r : ℝ) : ℂ) * ψ r) * Complex.I_sq

/-- **`∫(v₁u₂ + v₂u₁) = -iπ I`** (B0388). -/
theorem integral_v1u2_add_v2u1 {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) :
    ∫ y : ℂ, (vortexV1 y * streamU2 ψ y + vortexV2 y * streamU1 ψ y) =
      -(Complex.I * π * stressI ψ ψ') := by
  have hI2 : IntegrableOn (fun r => r * (2 * stressDom ψ ψ' r)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hI.const_mul 2) (fun r _ => ?_) measurableSet_Ioi
    ring
  have hF : Integrable fun y : ℂ => vortexV1 y * streamU2 ψ y + vortexV2 y * streamU1 ψ y := by
    refine integrable_of_radial_bound
      ((aesm_vu continuous_vortexV1 (measurable_streamU2 ψ)).add
        (aesm_vu continuous_vortexV2 (measurable_streamU1 ψ))) hI2 fun y hy => ?_
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_mul_le_dom (ψ := ψ) (ψ' := ψ') (norm_vortexV1_le y) (norm_streamU2_le hψ hy)
    have h2 := norm_mul_le_dom (ψ := ψ) (ψ' := ψ') (norm_vortexV2_le y) (norm_streamU1_le hψ hy)
    linarith
  rw [integral_plane_of_circle hF (G := fun r =>
      (-(omr r * (2 * Complex.I * ψ r / r))) * ((π : ℂ) / 2) +
        (-(2 * omr r * ψ' r)) * (Complex.I * (π : ℂ) / 2) -
        omr r * (2 * Complex.I * ψ r / r) * ((π : ℂ) / 2))
    (fun r hr => by simp_rw [cross_circle hψ hr]; exact angular_combo _ _ _),
    stressI, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < r from hr).ne'
  simp only [omr]
  field_simp
  ring

/-- **B0388, `E_q = iC`** (`paper/main.tex` lines 7004–7005, plane part): for the plane radial
vortex and an angular-two stream, `(2/c)∫v₂u₂ = i(1/c)∫(v₁u₂ + v₂u₁)`. -/
theorem stressEq_eq_I_mul_stressC {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) (c : ℂ) :
    stressEq c ψ = Complex.I * stressC c ψ := by
  rw [stressEq, stressC, integral_v2u2 hψ hI, integral_v1u2_add_v2u1 hψ hI]
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  · field_simp
    linear_combination (stressI ψ ψ') * Complex.I_sq

/-- **B0388, `E_η = -E_q`** (plane part). -/
theorem stressEη_eq_neg_stressEq {ψ ψ' : ℝ → ℂ}
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) (c : ℂ) :
    stressEη c ψ = -stressEq c ψ := by
  rw [stressEη, stressEq, integral_v1u1 hψ hI, integral_v2u2 hψ hI]
  ring

/-- **B0388**: the plane defects `D_c = E_η + E_q` and `R_c = E_q - iC` vanish exactly. -/
theorem stressDefects_eq_zero {ψ ψ' : ℝ → ℂ} (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r)
    (hI : IntegrableOn (fun r => r * stressDom ψ ψ' r) (Ioi 0)) (c : ℂ) :
    stressEη c ψ + stressEq c ψ = 0 ∧ stressEq c ψ - Complex.I * stressC c ψ = 0 := by
  refine ⟨?_, ?_⟩
  · rw [stressEη_eq_neg_stressEq hψ hI, neg_add_cancel]
  · rw [stressEq_eq_I_mul_stressC hψ hI, sub_self]

end UnforcedLeray.Planar
