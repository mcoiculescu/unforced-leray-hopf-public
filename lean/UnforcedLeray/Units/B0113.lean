import UnforcedLeray.Analysis.GaussianVortex.ProfileBridge
import UnforcedLeray.Analysis.NonlinearBackground.TrainScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# B0113 — Exact radial Gaussian heat vortex (`eq:st18-t00086`)

Blueprint unit **B0113**, label `eq:st18-t00086`, `paper/main.tex` lines 1718–1727
(proof environment "The exact heat scaling", §`sec:st18-1883`).

**Statement.** Fix a viscosity `ν > 0` and put `a(s) = 1 + ν s`,
`V(s,x) = a^{-3/2} V₀(x/√a)` and `E(s,x) = a^{-2} E₀(x/√a)`, where `V₀(y) = e^{-|y|²/4} y^⊥`
and `E₀ = (2 - r²/2)e^{-r²/4}` are the unit Gaussian vortex and its vorticity
(`eq:st18-t00001`, unit B0006). Then for every `s ≥ 0` the velocity `V` is divergence free
with curl `E`, the pair `(V, P)` with the radial pressure `P(s,x) = -a^{-3}e^{-|x|²/(2a)}`
solves the unforced two-dimensional Navier–Stokes equations with viscosity `ν`, the radial
vorticity is not advected by its tangential velocity (`V·∇E = 0`), and `E` (as well as each
Cartesian component of `V`, and the streamfunction `-2a^{-1}e^{-|x|²/(4a)}`) solves the heat
equation `∂ₛf = νΔf`.

**Conventions.** `V₀ = GaussianVortex.velocity`, `E₀ = GaussianVortex.vorticity`,
`P₀ = GaussianVortex.pressure`, `ψ₀ = GaussianVortex.streamfunction` (compiled, unit B0006).
Spatial derivatives are the classical Cartesian partials `partialX`, `partialY` of
`GaussianVortex.PlanarDefs`; `timeD`, `lap`, `ClassicalMeridionalSystem` are the compiled
planar Navier–Stokes notions of `NonlinearBackground.TrainScaling`. The manuscript names no
pressure; `heatPressure` is the explicit one, `a^{-3}P₀(x/√a)`. Time derivatives in the main
statements are `HasDerivAt` (so no `deriv` junk value is involved); the fields are smooth in
`x` for each `s` and jointly smooth in `(s,x)` on `{a(s) > 0}`. The hypotheses are exactly
`ν > 0`, `s ≥ 0`; the intermediate lemmas only use `a(s) > 0`.

This file adapts the (non-compiling) draft

(`heatV_solves_heat`, `heatV_solves_NS`); the calculus is rewritten in terms of `a⁻¹`.

Main declarations: `exact_heat_scaling`, `heatVortex_navierStokes`,
`heatVortex_vorticity_not_advected`, `heatVortex_heat_equation`,
`heatVortex_classicalSystem`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology
open Filter

namespace UnforcedLeray.B0113

open UnforcedLeray.GaussianVortex
open UnforcedLeray.NonlinearBackground

/-! ### The manuscript's fields -/

/-- The heat width `a(s) = 1 + ν s` of `eq:st18-t00086` (tex line 1722). -/
def heatWidth (ν s : ℝ) : ℝ := 1 + ν * s

/-- `V(s,x) = a^{-3/2} V₀(x/√a)` (tex line 1723), with `V₀ = velocity`. -/
def heatVelocity (ν s : ℝ) (x : Plane) : Plane :=
  heatWidth ν s ^ (-(3 / 2 : ℝ)) • velocity ((Real.sqrt (heatWidth ν s))⁻¹ • x)

/-- `E(s,x) = a^{-2} E₀(x/√a)` (tex line 1724), with `E₀ = vorticity`. -/
def heatVorticity (ν s : ℝ) (x : Plane) : ℝ :=
  (heatWidth ν s)⁻¹ ^ 2 * vorticity ((Real.sqrt (heatWidth ν s))⁻¹ • x)

/-- The radial pressure `a^{-3} P₀(x/√a)`, `P₀ = pressure = -e^{-|y|²/2}`. -/
def heatPressure (ν s : ℝ) (x : Plane) : ℝ :=
  (heatWidth ν s)⁻¹ ^ 3 * pressure ((Real.sqrt (heatWidth ν s))⁻¹ • x)

/-- The streamfunction `a^{-1} ψ₀(x/√a) = -2a^{-1}e^{-|x|²/(4a)}`. -/
def heatStreamfunction (ν s : ℝ) (x : Plane) : ℝ :=
  (heatWidth ν s)⁻¹ * streamfunction ((Real.sqrt (heatWidth ν s))⁻¹ • x)

/-- First Cartesian component of `V`, as a time-dependent scalar field. -/
def heatVelocityX (ν : ℝ) : ScalarField := fun s x => (heatVelocity ν s x).1

/-- Second Cartesian component of `V`, as a time-dependent scalar field. -/
def heatVelocityY (ν : ℝ) : ScalarField := fun s x => (heatVelocity ν s x).2

/-! ### Explicit Gaussian calculus at width `a` -/

/-- A Gaussian of width `a`. -/
def gw (a : ℝ) (z : Plane) : ℝ := Real.exp (-(a⁻¹ * radiusSq z / 4))

theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem hasDerivAt_gw_x (a : ℝ) (z : Plane) :
    HasDerivAt (fun t => gw a (t, z.2)) (-(a⁻¹ * z.1 / 2) * gw a z) z.1 := by
  have h := ((((hasDerivAt_sq' z.1).add_const (z.2 ^ 2)).const_mul a⁻¹).div_const 4).fun_neg.exp
  refine h.congr_deriv ?_
  simp only [gw, radiusSq]
  ring

theorem hasDerivAt_gw_y (a : ℝ) (z : Plane) :
    HasDerivAt (fun t => gw a (z.1, t)) (-(a⁻¹ * z.2 / 2) * gw a z) z.2 := by
  have h := ((((hasDerivAt_sq' z.2).const_add (z.1 ^ 2)).const_mul a⁻¹).div_const 4).fun_neg.exp
  refine h.congr_deriv ?_
  simp only [gw, radiusSq]
  ring

theorem hasDerivAt_mul_gw_x (a : ℝ) (z : Plane) {P : ℝ → ℝ} {P' : ℝ}
    (hP : HasDerivAt P P' z.1) :
    HasDerivAt (fun t => P t * gw a (t, z.2))
      ((P' - P z.1 * (a⁻¹ * z.1 / 2)) * gw a z) z.1 := by
  refine (hP.fun_mul (hasDerivAt_gw_x a z)).congr_deriv ?_
  simp only [Prod.mk.eta]
  ring

theorem hasDerivAt_mul_gw_y (a : ℝ) (z : Plane) {P : ℝ → ℝ} {P' : ℝ}
    (hP : HasDerivAt P P' z.2) :
    HasDerivAt (fun t => P t * gw a (z.1, t))
      ((P' - P z.2 * (a⁻¹ * z.2 / 2)) * gw a z) z.2 := by
  refine (hP.fun_mul (hasDerivAt_gw_y a z)).congr_deriv ?_
  simp only [Prod.mk.eta]
  ring

theorem hasDerivAt_gw_a {a : ℝ} (ha : a ≠ 0) (z : Plane) :
    HasDerivAt (fun b => gw b z) (a⁻¹ ^ 2 * radiusSq z / 4 * gw a z) a := by
  have h := (((hasDerivAt_inv ha).mul_const (radiusSq z)).div_const 4).fun_neg.exp
  refine h.congr_deriv ?_
  simp only [gw]
  ring

theorem hasDerivAt_mul_gw_a {a : ℝ} (ha : a ≠ 0) (z : Plane) {P : ℝ → ℝ} {P' : ℝ}
    (hP : HasDerivAt P P' a) :
    HasDerivAt (fun b => P b * gw b z)
      ((P' + P a * (a⁻¹ ^ 2 * radiusSq z / 4)) * gw a z) a := by
  refine (hP.fun_mul (hasDerivAt_gw_a ha z)).congr_deriv ?_
  ring

theorem hasDerivAt_inv_sq {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun b : ℝ => b⁻¹ ^ 2) (-2 * a⁻¹ ^ 3) a := by
  have h := (hasDerivAt_sq' a⁻¹).comp a (hasDerivAt_inv ha)
  refine h.congr_deriv ?_
  ring

/-! ### Explicit fields at width `a` -/

/-- Explicit velocity `a⁻² z^⊥ e^{-|z|²/(4a)}`. -/
def vExp (a : ℝ) (z : Plane) : Plane :=
  (-(a⁻¹ ^ 2) * z.2 * gw a z, a⁻¹ ^ 2 * z.1 * gw a z)

/-- Explicit vorticity `a⁻² (2 - |z|²/(2a)) e^{-|z|²/(4a)}`. -/
def eExp (a : ℝ) (z : Plane) : ℝ := a⁻¹ ^ 2 * (2 - a⁻¹ * radiusSq z / 2) * gw a z

/-- Explicit pressure `-a⁻³ e^{-|z|²/(2a)}`. -/
def pExp (a : ℝ) (z : Plane) : ℝ := -(a⁻¹ ^ 3) * (gw a z * gw a z)

/-- Explicit streamfunction `-2 a⁻¹ e^{-|z|²/(4a)}`. -/
def ψExp (a : ℝ) (z : Plane) : ℝ := -2 * a⁻¹ * gw a z

/-! #### First spatial derivatives -/

theorem vExp1_x (a : ℝ) (z : Plane) :
    partialX (fun w => (vExp a w).1) z = a⁻¹ ^ 3 * z.1 * z.2 / 2 * gw a z :=
  (hasDerivAt_mul_gw_x a z (hasDerivAt_const z.1 (-(a⁻¹ ^ 2) * z.2))).deriv.trans (by ring)

theorem vExp1_y (a : ℝ) (z : Plane) :
    partialY (fun w => (vExp a w).1) z = a⁻¹ ^ 2 * (a⁻¹ * z.2 ^ 2 / 2 - 1) * gw a z :=
  (hasDerivAt_mul_gw_y a z ((hasDerivAt_id' z.2).const_mul (-(a⁻¹ ^ 2)))).deriv.trans
    (by ring)

theorem vExp2_x (a : ℝ) (z : Plane) :
    partialX (fun w => (vExp a w).2) z = a⁻¹ ^ 2 * (1 - a⁻¹ * z.1 ^ 2 / 2) * gw a z :=
  (hasDerivAt_mul_gw_x a z ((hasDerivAt_id' z.1).const_mul (a⁻¹ ^ 2))).deriv.trans
    (by ring)

theorem vExp2_y (a : ℝ) (z : Plane) :
    partialY (fun w => (vExp a w).2) z = -(a⁻¹ ^ 3 * z.1 * z.2 / 2) * gw a z :=
  (hasDerivAt_mul_gw_y a z (hasDerivAt_const z.2 (a⁻¹ ^ 2 * z.1))).deriv.trans (by ring)

theorem eExp_x (a : ℝ) (z : Plane) :
    partialX (eExp a) z = a⁻¹ ^ 3 * z.1 * (a⁻¹ * radiusSq z / 4 - 2) * gw a z :=
  (hasDerivAt_mul_gw_x a z (((((hasDerivAt_sq' z.1).add_const (z.2 ^ 2)).const_mul
    a⁻¹).div_const 2).const_sub 2 |>.const_mul (a⁻¹ ^ 2))).deriv.trans
    (by simp only [radiusSq]; ring)

theorem eExp_y (a : ℝ) (z : Plane) :
    partialY (eExp a) z = a⁻¹ ^ 3 * z.2 * (a⁻¹ * radiusSq z / 4 - 2) * gw a z :=
  (hasDerivAt_mul_gw_y a z (((((hasDerivAt_sq' z.2).const_add (z.1 ^ 2)).const_mul
    a⁻¹).div_const 2).const_sub 2 |>.const_mul (a⁻¹ ^ 2))).deriv.trans
    (by simp only [radiusSq]; ring)

theorem pExp_x (a : ℝ) (z : Plane) :
    partialX (pExp a) z = a⁻¹ ^ 4 * z.1 * (gw a z * gw a z) :=
  (((hasDerivAt_gw_x a z).fun_mul (hasDerivAt_gw_x a z)).const_mul (-(a⁻¹ ^ 3))).deriv.trans
    (by simp only [Prod.mk.eta]; ring)

theorem pExp_y (a : ℝ) (z : Plane) :
    partialY (pExp a) z = a⁻¹ ^ 4 * z.2 * (gw a z * gw a z) :=
  (((hasDerivAt_gw_y a z).fun_mul (hasDerivAt_gw_y a z)).const_mul (-(a⁻¹ ^ 3))).deriv.trans
    (by simp only [Prod.mk.eta]; ring)

theorem ψExp_x (a : ℝ) (z : Plane) :
    partialX (ψExp a) z = a⁻¹ ^ 2 * z.1 * gw a z :=
  (hasDerivAt_mul_gw_x a z (hasDerivAt_const z.1 (-2 * a⁻¹))).deriv.trans (by ring)

theorem ψExp_y (a : ℝ) (z : Plane) :
    partialY (ψExp a) z = a⁻¹ ^ 2 * z.2 * gw a z :=
  (hasDerivAt_mul_gw_y a z (hasDerivAt_const z.2 (-2 * a⁻¹))).deriv.trans (by ring)

/-! #### Second spatial derivatives -/

theorem vExp1_xx (a : ℝ) (z : Plane) :
    partialX (partialX (fun w => (vExp a w).1)) z =
      a⁻¹ ^ 3 * z.2 / 2 * (1 - a⁻¹ * z.1 ^ 2 / 2) * gw a z := by
  rw [show partialX (fun w => (vExp a w).1) = fun w => a⁻¹ ^ 3 * w.1 * w.2 / 2 * gw a w from
    funext (vExp1_x a)]
  exact (hasDerivAt_mul_gw_x a z ((((hasDerivAt_id' z.1).const_mul (a⁻¹ ^ 3)).mul_const
    z.2).div_const 2)).deriv.trans (by ring)

theorem vExp1_yy (a : ℝ) (z : Plane) :
    partialY (partialY (fun w => (vExp a w).1)) z =
      a⁻¹ ^ 3 * z.2 * (3 / 2 - a⁻¹ * z.2 ^ 2 / 4) * gw a z := by
  rw [show partialY (fun w => (vExp a w).1) =
      fun w => a⁻¹ ^ 2 * (a⁻¹ * w.2 ^ 2 / 2 - 1) * gw a w from funext (vExp1_y a)]
  exact (hasDerivAt_mul_gw_y a z (((((hasDerivAt_sq' z.2).const_mul a⁻¹).div_const 2).sub_const
    1).const_mul (a⁻¹ ^ 2))).deriv.trans (by ring)

theorem vExp2_xx (a : ℝ) (z : Plane) :
    partialX (partialX (fun w => (vExp a w).2)) z =
      -(a⁻¹ ^ 3 * z.1 * (3 / 2 - a⁻¹ * z.1 ^ 2 / 4)) * gw a z := by
  rw [show partialX (fun w => (vExp a w).2) =
      fun w => a⁻¹ ^ 2 * (1 - a⁻¹ * w.1 ^ 2 / 2) * gw a w from funext (vExp2_x a)]
  exact (hasDerivAt_mul_gw_x a z (((((hasDerivAt_sq' z.1).const_mul a⁻¹).div_const 2).const_sub
    1).const_mul (a⁻¹ ^ 2))).deriv.trans (by ring)

theorem vExp2_yy (a : ℝ) (z : Plane) :
    partialY (partialY (fun w => (vExp a w).2)) z =
      -(a⁻¹ ^ 3 * z.1 / 2 * (1 - a⁻¹ * z.2 ^ 2 / 2)) * gw a z := by
  rw [show partialY (fun w => (vExp a w).2) =
      fun w => -(a⁻¹ ^ 3 * w.1 * w.2 / 2) * gw a w from funext (vExp2_y a)]
  exact (hasDerivAt_mul_gw_y a z ((((hasDerivAt_id' z.2).const_mul (a⁻¹ ^ 3 * z.1)).div_const
    2).fun_neg)).deriv.trans (by ring)

theorem eExp_xx (a : ℝ) (z : Plane) :
    partialX (partialX (eExp a)) z =
      (a⁻¹ ^ 3 * (a⁻¹ * radiusSq z / 4 - 2) + a⁻¹ ^ 4 * z.1 ^ 2 / 2 -
        a⁻¹ ^ 3 * z.1 * (a⁻¹ * radiusSq z / 4 - 2) * (a⁻¹ * z.1 / 2)) * gw a z := by
  rw [show partialX (eExp a) =
      fun w => a⁻¹ ^ 3 * w.1 * (a⁻¹ * radiusSq w / 4 - 2) * gw a w from funext (eExp_x a)]
  exact (hasDerivAt_mul_gw_x a z (((hasDerivAt_id' z.1).const_mul (a⁻¹ ^ 3)).fun_mul
    (((((hasDerivAt_sq' z.1).add_const (z.2 ^ 2)).const_mul a⁻¹).div_const 4).sub_const
      2))).deriv.trans (by simp only [radiusSq]; ring)

theorem eExp_yy (a : ℝ) (z : Plane) :
    partialY (partialY (eExp a)) z =
      (a⁻¹ ^ 3 * (a⁻¹ * radiusSq z / 4 - 2) + a⁻¹ ^ 4 * z.2 ^ 2 / 2 -
        a⁻¹ ^ 3 * z.2 * (a⁻¹ * radiusSq z / 4 - 2) * (a⁻¹ * z.2 / 2)) * gw a z := by
  rw [show partialY (eExp a) =
      fun w => a⁻¹ ^ 3 * w.2 * (a⁻¹ * radiusSq w / 4 - 2) * gw a w from funext (eExp_y a)]
  exact (hasDerivAt_mul_gw_y a z (((hasDerivAt_id' z.2).const_mul (a⁻¹ ^ 3)).fun_mul
    (((((hasDerivAt_sq' z.2).const_add (z.1 ^ 2)).const_mul a⁻¹).div_const 4).sub_const
      2))).deriv.trans (by simp only [radiusSq]; ring)

theorem ψExp_xx (a : ℝ) (z : Plane) :
    partialX (partialX (ψExp a)) z = a⁻¹ ^ 2 * (1 - a⁻¹ * z.1 ^ 2 / 2) * gw a z := by
  rw [show partialX (ψExp a) = fun w => a⁻¹ ^ 2 * w.1 * gw a w from funext (ψExp_x a)]
  exact (hasDerivAt_mul_gw_x a z ((hasDerivAt_id' z.1).const_mul (a⁻¹ ^ 2))).deriv.trans
    (by ring)

theorem ψExp_yy (a : ℝ) (z : Plane) :
    partialY (partialY (ψExp a)) z = a⁻¹ ^ 2 * (1 - a⁻¹ * z.2 ^ 2 / 2) * gw a z := by
  rw [show partialY (ψExp a) = fun w => a⁻¹ ^ 2 * w.2 * gw a w from funext (ψExp_y a)]
  exact (hasDerivAt_mul_gw_y a z ((hasDerivAt_id' z.2).const_mul (a⁻¹ ^ 2))).deriv.trans
    (by ring)

/-! #### Laplacians, curl, divergence, advection -/

theorem vExp1_lap (a : ℝ) (z : Plane) :
    partialX (partialX (fun w => (vExp a w).1)) z +
        partialY (partialY (fun w => (vExp a w).1)) z =
      a⁻¹ ^ 2 * z.2 * (2 * a⁻¹ - a⁻¹ ^ 2 * radiusSq z / 4) * gw a z := by
  rw [vExp1_xx, vExp1_yy]
  simp only [radiusSq]
  ring

theorem vExp2_lap (a : ℝ) (z : Plane) :
    partialX (partialX (fun w => (vExp a w).2)) z +
        partialY (partialY (fun w => (vExp a w).2)) z =
      a⁻¹ ^ 2 * z.1 * (a⁻¹ ^ 2 * radiusSq z / 4 - 2 * a⁻¹) * gw a z := by
  rw [vExp2_xx, vExp2_yy]
  simp only [radiusSq]
  ring

theorem eExp_lap (a : ℝ) (z : Plane) :
    partialX (partialX (eExp a)) z + partialY (partialY (eExp a)) z =
      (2 * a⁻¹ ^ 4 * radiusSq z - 4 * a⁻¹ ^ 3 - a⁻¹ ^ 5 * radiusSq z ^ 2 / 8) * gw a z := by
  rw [eExp_xx, eExp_yy]
  simp only [radiusSq]
  ring

theorem ψExp_lap (a : ℝ) (z : Plane) :
    partialX (partialX (ψExp a)) z + partialY (partialY (ψExp a)) z = eExp a z := by
  rw [ψExp_xx, ψExp_yy]
  simp only [eExp, radiusSq]
  ring

theorem vExp_divergence (a : ℝ) (z : Plane) : divergence (vExp a) z = 0 := by
  rw [divergence, vExp1_x, vExp2_y]
  ring

theorem vExp_curl (a : ℝ) (z : Plane) : curl (vExp a) z = eExp a z := by
  rw [curl, vExp2_x, vExp1_y]
  simp only [eExp, radiusSq]
  ring

theorem ψExp_perp (a : ℝ) (z : Plane) : perpendicularGradient (ψExp a) z = vExp a z := by
  simp only [perpendicularGradient, ψExp_x, ψExp_y, vExp]
  refine Prod.ext ?_ ?_ <;> ring

theorem vExp_advection (a : ℝ) (z : Plane) :
    advection (vExp a) z =
      (-(a⁻¹ ^ 4 * z.1 * (gw a z * gw a z)), -(a⁻¹ ^ 4 * z.2 * (gw a z * gw a z))) := by
  simp only [advection, scalarAdvection]
  rw [vExp1_x, vExp1_y, vExp2_x, vExp2_y]
  simp only [vExp]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem vExp_euler (a : ℝ) (z : Plane) :
    advection (vExp a) z + gradient (pExp a) z = 0 := by
  rw [vExp_advection]
  simp only [gradient, pExp_x, pExp_y]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero,
    Prod.snd_zero] <;> ring

theorem eExp_advection (a : ℝ) (z : Plane) :
    scalarAdvection (vExp a) (eExp a) z = 0 := by
  simp only [scalarAdvection, eExp_x, eExp_y, vExp]
  ring

/-! #### Derivatives in the width -/

theorem vExp1_a {a : ℝ} (ha : a ≠ 0) (z : Plane) :
    HasDerivAt (fun b => (vExp b z).1)
      (a⁻¹ ^ 2 * z.2 * (2 * a⁻¹ - a⁻¹ ^ 2 * radiusSq z / 4) * gw a z) a :=
  (hasDerivAt_mul_gw_a ha z ((hasDerivAt_inv_sq ha).fun_neg.mul_const z.2)).congr_deriv
    (by ring)

theorem vExp2_a {a : ℝ} (ha : a ≠ 0) (z : Plane) :
    HasDerivAt (fun b => (vExp b z).2)
      (a⁻¹ ^ 2 * z.1 * (a⁻¹ ^ 2 * radiusSq z / 4 - 2 * a⁻¹) * gw a z) a :=
  (hasDerivAt_mul_gw_a ha z ((hasDerivAt_inv_sq ha).mul_const z.1)).congr_deriv (by ring)

theorem eExp_a {a : ℝ} (ha : a ≠ 0) (z : Plane) :
    HasDerivAt (fun b => eExp b z)
      ((2 * a⁻¹ ^ 4 * radiusSq z - 4 * a⁻¹ ^ 3 - a⁻¹ ^ 5 * radiusSq z ^ 2 / 8) * gw a z) a :=
  (hasDerivAt_mul_gw_a ha z ((hasDerivAt_inv_sq ha).fun_mul
    ((((hasDerivAt_inv ha).mul_const (radiusSq z)).div_const 2).const_sub 2))).congr_deriv
    (by ring)

theorem ψExp_a {a : ℝ} (ha : a ≠ 0) (z : Plane) :
    HasDerivAt (fun b => ψExp b z) (eExp a z) a :=
  (hasDerivAt_mul_gw_a ha z ((hasDerivAt_inv ha).const_mul (-2))).congr_deriv
    (by simp only [eExp]; ring)

/-! ### Width, eventual positivity, scaling identities -/

theorem heatWidth_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) : 0 < heatWidth ν s := by
  have := mul_nonneg hν.le hs
  unfold heatWidth
  linarith

theorem hasDerivAt_heatWidth (ν s : ℝ) : HasDerivAt (heatWidth ν) ν s :=
  (((hasDerivAt_id' s).const_mul ν).const_add 1).congr_deriv (mul_one ν)

theorem eventually_heatWidth_pos {ν s : ℝ} (ha : 0 < heatWidth ν s) :
    ∀ᶠ t in 𝓝 s, 0 < heatWidth ν t :=
  (hasDerivAt_heatWidth ν s).continuousAt.tendsto.eventually (lt_mem_nhds ha)

theorem radiusSq_smul (c : ℝ) (x : Plane) : radiusSq (c • x) = c ^ 2 * radiusSq x := by
  simp only [radiusSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem inv_sqrt_sq {a : ℝ} (ha : 0 < a) : (Real.sqrt a)⁻¹ ^ 2 = a⁻¹ := by
  rw [inv_pow, Real.sq_sqrt ha.le]

theorem radiusSq_inv_sqrt_smul {a : ℝ} (ha : 0 < a) (x : Plane) :
    radiusSq ((Real.sqrt a)⁻¹ • x) = a⁻¹ * radiusSq x := by
  rw [radiusSq_smul, inv_sqrt_sq ha]

theorem planarGaussian_inv_sqrt_smul {a : ℝ} (ha : 0 < a) (x : Plane) :
    planarGaussian ((Real.sqrt a)⁻¹ • x) = gw a x := by
  rw [planarGaussian, radiusSq_inv_sqrt_smul ha, gw]

theorem rpow_neg_three_halves_mul {a : ℝ} (ha : 0 < a) :
    a ^ (-(3 / 2 : ℝ)) * (Real.sqrt a)⁻¹ = a⁻¹ ^ 2 := by
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [Real.rpow_neg ha.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc (a * Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ = (a * Real.sqrt a ^ 2)⁻¹ := by ring
    _ = a⁻¹ ^ 2 := by rw [hs]; ring

/-- Explicit form: `V(s,x) = a⁻² x^⊥ e^{-|x|²/(4a)}`. -/
theorem heatVelocity_eq {ν s : ℝ} (ha : 0 < heatWidth ν s) :
    heatVelocity ν s = vExp (heatWidth ν s) := by
  funext x
  have key := rpow_neg_three_halves_mul ha
  simp only [heatVelocity, velocity, planarGaussian_inv_sqrt_smul ha, vExp, Prod.smul_mk,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← key]
  refine Prod.ext ?_ ?_ <;> ring

/-- Explicit form: `E(s,x) = a⁻² (2 - |x|²/(2a)) e^{-|x|²/(4a)}`. -/
theorem heatVorticity_eq {ν s : ℝ} (ha : 0 < heatWidth ν s) :
    heatVorticity ν s = eExp (heatWidth ν s) := by
  funext x
  simp only [heatVorticity, vorticity, planarGaussian_inv_sqrt_smul ha,
    radiusSq_inv_sqrt_smul ha, eExp]
  ring

theorem gw_mul_self (a : ℝ) (z : Plane) :
    gw a z * gw a z = Real.exp (-(a⁻¹ * radiusSq z / 2)) := by
  rw [gw, ← Real.exp_add]
  ring_nf

/-- Explicit form: `P(s,x) = -a⁻³ e^{-|x|²/(2a)}`, a radial pressure. -/
theorem heatPressure_eq {ν s : ℝ} (ha : 0 < heatWidth ν s) :
    heatPressure ν s = pExp (heatWidth ν s) := by
  funext x
  simp only [heatPressure, pressure, radiusSq_inv_sqrt_smul ha, pExp, gw_mul_self]
  ring_nf

/-- Explicit form: `ψ(s,x) = -2a⁻¹ e^{-|x|²/(4a)}`. -/
theorem heatStreamfunction_eq {ν s : ℝ} (ha : 0 < heatWidth ν s) :
    heatStreamfunction ν s = ψExp (heatWidth ν s) := by
  funext x
  simp only [heatStreamfunction, streamfunction, planarGaussian_inv_sqrt_smul ha, ψExp]
  ring

/-! ### Initial data, smoothness, radial form -/

/-- At `s = 0` the branch starts from the Gaussian vortex `V₀`. -/
theorem heatVelocity_zero (ν : ℝ) : heatVelocity ν 0 = velocity := by
  funext x
  simp [heatVelocity, heatWidth]

/-- At `s = 0` the vorticity is `E₀`. -/
theorem heatVorticity_zero (ν : ℝ) : heatVorticity ν 0 = vorticity := by
  funext x
  simp [heatVorticity, heatWidth]

theorem heatPressure_zero (ν : ℝ) : heatPressure ν 0 = pressure := by
  funext x
  simp [heatPressure, heatWidth]

theorem heatStreamfunction_zero (ν : ℝ) : heatStreamfunction ν 0 = streamfunction := by
  funext x
  simp [heatStreamfunction, heatWidth]

theorem contDiff_heatVelocity (ν s : ℝ) : ContDiff ℝ ∞ (heatVelocity ν s) :=
  (contDiff_velocity.comp (contDiff_id.const_smul _)).const_smul _

theorem contDiff_heatVorticity (ν s : ℝ) : ContDiff ℝ ∞ (heatVorticity ν s) :=
  contDiff_const.mul (contDiff_vorticity.comp (contDiff_id.const_smul _))

theorem contDiff_heatPressure (ν s : ℝ) : ContDiff ℝ ∞ (heatPressure ν s) :=
  contDiff_const.mul (contDiff_pressure.comp (contDiff_id.const_smul _))

theorem contDiff_heatStreamfunction (ν s : ℝ) : ContDiff ℝ ∞ (heatStreamfunction ν s) :=
  contDiff_const.mul (contDiff_streamfunction.comp (contDiff_id.const_smul _))

theorem isOpen_heatWidth_pos (ν : ℝ) : IsOpen {q : ℝ × Plane | 0 < heatWidth ν q.1} :=
  isOpen_lt continuous_const (by unfold heatWidth; fun_prop)

/-- Joint smoothness of `V` in `(s,x)` wherever `a(s) > 0`. -/
theorem contDiffOn_heatVelocity (ν : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Plane => heatVelocity ν q.1 q.2)
      {q | 0 < heatWidth ν q.1} := by
  intro p hp
  have hne : heatWidth ν p.1 ≠ 0 := ne_of_gt hp
  have hev : (fun q : ℝ × Plane => heatVelocity ν q.1 q.2) =ᶠ[𝓝 p]
      (fun q => vExp (heatWidth ν q.1) q.2) := by
    filter_upwards [(isOpen_heatWidth_pos ν).mem_nhds hp] with q hq
    rw [heatVelocity_eq hq]
  have hsm : ContDiffAt ℝ ∞ (fun q : ℝ × Plane => vExp (heatWidth ν q.1) q.2) p := by
    unfold vExp gw radiusSq
    unfold heatWidth at hne ⊢
    fun_prop (disch := exact hne)
  exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt

/-- Joint smoothness of `E` in `(s,x)` wherever `a(s) > 0`. -/
theorem contDiffOn_heatVorticity (ν : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Plane => heatVorticity ν q.1 q.2)
      {q | 0 < heatWidth ν q.1} := by
  intro p hp
  have hne : heatWidth ν p.1 ≠ 0 := ne_of_gt hp
  have hev : (fun q : ℝ × Plane => heatVorticity ν q.1 q.2) =ᶠ[𝓝 p]
      (fun q => eExp (heatWidth ν q.1) q.2) := by
    filter_upwards [(isOpen_heatWidth_pos ν).mem_nhds hp] with q hq
    rw [heatVorticity_eq hq]
  have hsm : ContDiffAt ℝ ∞ (fun q : ℝ × Plane => eExp (heatWidth ν q.1) q.2) p := by
    unfold eExp gw radiusSq
    unfold heatWidth at hne ⊢
    fun_prop (disch := exact hne)
  exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt

/-- Joint smoothness of the pressure in `(s,x)` wherever `a(s) > 0`. -/
theorem contDiffOn_heatPressure (ν : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Plane => heatPressure ν q.1 q.2)
      {q | 0 < heatWidth ν q.1} := by
  intro p hp
  have hne : heatWidth ν p.1 ≠ 0 := ne_of_gt hp
  have hev : (fun q : ℝ × Plane => heatPressure ν q.1 q.2) =ᶠ[𝓝 p]
      (fun q => pExp (heatWidth ν q.1) q.2) := by
    filter_upwards [(isOpen_heatWidth_pos ν).mem_nhds hp] with q hq
    rw [heatPressure_eq hq]
  have hsm : ContDiffAt ℝ ∞ (fun q : ℝ × Plane => pExp (heatWidth ν q.1) q.2) p := by
    unfold pExp gw radiusSq
    unfold heatWidth at hne ⊢
    fun_prop (disch := exact hne)
  exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt

/-- The vorticity is radial: `E(s,x) = a⁻² E₀(|x|/√a)` with the radial profile `E₀(r)`. -/
theorem heatVorticity_eq_radial {ν s : ℝ} (ha : 0 < heatWidth ν s) (x : Plane) :
    heatVorticity ν s x =
      (heatWidth ν s)⁻¹ ^ 2 *
        radialVorticity (radialCoordinate x / Real.sqrt (heatWidth ν s)) := by
  rw [heatVorticity, vorticity_eq_radialVorticity, radiusSq_inv_sqrt_smul ha,
    Real.sqrt_mul (inv_nonneg.mpr ha.le), Real.sqrt_inv, radialCoordinate, div_eq_inv_mul]

/-! ### Spatial identities at each time -/

theorem heatVelocity_divergence {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    divergence (heatVelocity ν s) z = 0 := by
  rw [heatVelocity_eq ha]
  exact vExp_divergence _ z

theorem curl_heatVelocity {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    curl (heatVelocity ν s) z = heatVorticity ν s z := by
  rw [heatVelocity_eq ha, heatVorticity_eq ha]
  exact vExp_curl _ z

theorem perpendicularGradient_heatStreamfunction {ν s : ℝ} (ha : 0 < heatWidth ν s)
    (z : Plane) : perpendicularGradient (heatStreamfunction ν s) z = heatVelocity ν s z := by
  rw [heatVelocity_eq ha, heatStreamfunction_eq ha]
  exact ψExp_perp _ z

theorem lap_heatStreamfunction {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (heatStreamfunction ν) s z = heatVorticity ν s z := by
  change partialX (partialX (heatStreamfunction ν s)) z +
    partialY (partialY (heatStreamfunction ν s)) z = _
  rw [heatStreamfunction_eq ha, heatVorticity_eq ha]
  exact ψExp_lap _ z

theorem heatVelocity_euler {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    advection (heatVelocity ν s) z + gradient (heatPressure ν s) z = 0 := by
  rw [heatVelocity_eq ha, heatPressure_eq ha]
  exact vExp_euler _ z

theorem heatVorticity_advection {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    scalarAdvection (heatVelocity ν s) (heatVorticity ν s) z = 0 := by
  rw [heatVelocity_eq ha, heatVorticity_eq ha]
  exact eExp_advection _ z

theorem lap_heatVelocityX {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (heatVelocityX ν) s z =
      (heatWidth ν s)⁻¹ ^ 2 * z.2 *
        (2 * (heatWidth ν s)⁻¹ - (heatWidth ν s)⁻¹ ^ 2 * radiusSq z / 4) *
          gw (heatWidth ν s) z := by
  change partialX (partialX (fun w => (heatVelocity ν s w).1)) z +
    partialY (partialY (fun w => (heatVelocity ν s w).1)) z = _
  rw [heatVelocity_eq ha]
  exact vExp1_lap _ z

theorem lap_heatVelocityY {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (heatVelocityY ν) s z =
      (heatWidth ν s)⁻¹ ^ 2 * z.1 *
        ((heatWidth ν s)⁻¹ ^ 2 * radiusSq z / 4 - 2 * (heatWidth ν s)⁻¹) *
          gw (heatWidth ν s) z := by
  change partialX (partialX (fun w => (heatVelocity ν s w).2)) z +
    partialY (partialY (fun w => (heatVelocity ν s w).2)) z = _
  rw [heatVelocity_eq ha]
  exact vExp2_lap _ z

theorem lap_heatVorticity {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    lap (heatVorticity ν) s z =
      (2 * (heatWidth ν s)⁻¹ ^ 4 * radiusSq z - 4 * (heatWidth ν s)⁻¹ ^ 3 -
        (heatWidth ν s)⁻¹ ^ 5 * radiusSq z ^ 2 / 8) * gw (heatWidth ν s) z := by
  change partialX (partialX (heatVorticity ν s)) z +
    partialY (partialY (heatVorticity ν s)) z = _
  rw [heatVorticity_eq ha]
  exact eExp_lap _ z

/-! ### Time derivatives: the heat equations -/

theorem hasDerivAt_heatVelocityX {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    HasDerivAt (fun t => heatVelocityX ν t z) (ν * lap (heatVelocityX ν) s z) s := by
  have hc := (vExp1_a ha.ne' z).comp s (hasDerivAt_heatWidth ν s)
  have hev : (fun t => heatVelocityX ν t z) =ᶠ[𝓝 s]
      ((fun b => (vExp b z).1) ∘ heatWidth ν) :=
    (eventually_heatWidth_pos ha).mono fun t ht => by
      simp only [heatVelocityX, Function.comp_apply, heatVelocity_eq ht]
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [lap_heatVelocityX ha]
  ring

theorem hasDerivAt_heatVelocityY {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    HasDerivAt (fun t => heatVelocityY ν t z) (ν * lap (heatVelocityY ν) s z) s := by
  have hc := (vExp2_a ha.ne' z).comp s (hasDerivAt_heatWidth ν s)
  have hev : (fun t => heatVelocityY ν t z) =ᶠ[𝓝 s]
      ((fun b => (vExp b z).2) ∘ heatWidth ν) :=
    (eventually_heatWidth_pos ha).mono fun t ht => by
      simp only [heatVelocityY, Function.comp_apply, heatVelocity_eq ht]
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [lap_heatVelocityY ha]
  ring

theorem hasDerivAt_heatVorticity {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    HasDerivAt (fun t => heatVorticity ν t z) (ν * lap (heatVorticity ν) s z) s := by
  have hc := (eExp_a ha.ne' z).comp s (hasDerivAt_heatWidth ν s)
  have hev : (fun t => heatVorticity ν t z) =ᶠ[𝓝 s] ((fun b => eExp b z) ∘ heatWidth ν) :=
    (eventually_heatWidth_pos ha).mono fun t ht => by
      simp only [Function.comp_apply, heatVorticity_eq ht]
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [lap_heatVorticity ha]
  ring

theorem hasDerivAt_heatStreamfunction {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    HasDerivAt (fun t => heatStreamfunction ν t z)
      (ν * lap (heatStreamfunction ν) s z) s := by
  have hc := (ψExp_a ha.ne' z).comp s (hasDerivAt_heatWidth ν s)
  have hev : (fun t => heatStreamfunction ν t z) =ᶠ[𝓝 s]
      ((fun b => ψExp b z) ∘ heatWidth ν) :=
    (eventually_heatWidth_pos ha).mono fun t ht => by
      simp only [Function.comp_apply, heatStreamfunction_eq ht]
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [lap_heatStreamfunction ha, heatVorticity_eq ha]
  ring

theorem hasDerivAt_heatVelocity {ν s : ℝ} (ha : 0 < heatWidth ν s) (z : Plane) :
    HasDerivAt (fun t => heatVelocity ν t z)
      (ν • (lap (heatVelocityX ν) s z, lap (heatVelocityY ν) s z)) s :=
  ((hasDerivAt_heatVelocityX ha z).prodMk (hasDerivAt_heatVelocityY ha z)).congr_deriv rfl

/-! ### Main statements of `eq:st18-t00086` -/

/-- Tex line 1727: `(V, P)` is an unforced two-dimensional Navier–Stokes solution with
viscosity `ν`, in classical pointwise form:
`∂ₛV = νΔV - (V·∇)V - ∇P` with `div V = 0`, for `ν > 0`, `s ≥ 0`. -/
theorem heatVortex_navierStokes {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => heatVelocity ν t z)
      (ν • (lap (heatVelocityX ν) s z, lap (heatVelocityY ν) s z) -
        advection (heatVelocity ν s) z - gradient (heatPressure ν s) z) s ∧
    divergence (heatVelocity ν s) z = 0 := by
  have ha := heatWidth_pos hν hs
  refine ⟨(hasDerivAt_heatVelocity ha z).congr_deriv ?_, heatVelocity_divergence ha z⟩
  rw [sub_sub, heatVelocity_euler ha z, sub_zero]

/-- Tex line 1727: the radial vorticity is not advected by its tangential velocity,
`V·∇E = 0`, and `E = curl V`. -/
theorem heatVortex_vorticity_not_advected {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    curl (heatVelocity ν s) z = heatVorticity ν s z ∧
    scalarAdvection (heatVelocity ν s) (heatVorticity ν s) z = 0 :=
  ⟨curl_heatVelocity (heatWidth_pos hν hs) z,
    heatVorticity_advection (heatWidth_pos hν hs) z⟩

/-- Tex line 1727: `eq:st18-t00086` solves the heat equation, `∂ₛE = νΔE`; the velocity
components solve it as well. -/
theorem heatVortex_heat_equation {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    HasDerivAt (fun t => heatVorticity ν t z) (ν * lap (heatVorticity ν) s z) s ∧
    HasDerivAt (fun t => heatVelocityX ν t z) (ν * lap (heatVelocityX ν) s z) s ∧
    HasDerivAt (fun t => heatVelocityY ν t z) (ν * lap (heatVelocityY ν) s z) s :=
  ⟨hasDerivAt_heatVorticity (heatWidth_pos hν hs) z,
    hasDerivAt_heatVelocityX (heatWidth_pos hν hs) z,
    hasDerivAt_heatVelocityY (heatWidth_pos hν hs) z⟩

/-- Tex lines 1720–1727 in the library's classical planar form: for `ν > 0` the fields
`(V₁, V₂, P)` solve the unforced two-dimensional Navier–Stokes equations on `s ≥ 0`, and the
vorticity `E` solves the vorticity (transport–diffusion) equation
`∂ₛE + V·∇E = νΔE`. -/
theorem heatVortex_classicalSystem {ν : ℝ} (hν : 0 < ν) :
    ClassicalMeridionalSystem ν (heatVelocityX ν) (heatVelocityY ν) (heatPressure ν)
      (heatVorticity ν) where
  momentum_x := by
    intro s z hs
    have ha := heatWidth_pos hν hs
    have he := congrArg Prod.fst (heatVelocity_euler ha z)
    simp only [advection, scalarAdvection, gradient, Prod.fst_add, Prod.fst_zero] at he
    unfold momentumXResidual timeD dx dy
    rw [(hasDerivAt_heatVelocityX ha z).deriv]
    have e1 : partialX (heatVelocityX ν s) z = partialX (fun w => (heatVelocity ν s w).1) z :=
      rfl
    have e2 : partialY (heatVelocityX ν s) z = partialY (fun w => (heatVelocity ν s w).1) z :=
      rfl
    rw [e1, e2]
    simp only [heatVelocityX, heatVelocityY]
    linarith
  momentum_y := by
    intro s z hs
    have ha := heatWidth_pos hν hs
    have he := congrArg Prod.snd (heatVelocity_euler ha z)
    simp only [advection, scalarAdvection, gradient, Prod.snd_add, Prod.snd_zero] at he
    unfold momentumYResidual timeD dx dy
    rw [(hasDerivAt_heatVelocityY ha z).deriv]
    have e1 : partialX (heatVelocityY ν s) z = partialX (fun w => (heatVelocity ν s w).2) z :=
      rfl
    have e2 : partialY (heatVelocityY ν s) z = partialY (fun w => (heatVelocity ν s w).2) z :=
      rfl
    rw [e1, e2]
    simp only [heatVelocityX, heatVelocityY]
    linarith
  divergence_free := by
    intro s z hs
    exact heatVelocity_divergence (heatWidth_pos hν hs) z
  passive_scalar := by
    intro s z hs
    have ha := heatWidth_pos hν hs
    have he := heatVorticity_advection ha z
    simp only [scalarAdvection] at he
    unfold scalarResidual timeD dx dy
    rw [(hasDerivAt_heatVorticity ha z).deriv]
    simp only [heatVelocityX, heatVelocityY] at ⊢
    linarith

/-- The full unit `eq:st18-t00086` (tex lines 1720–1727), pointwise at every `s ≥ 0` and
`x ∈ ℝ²`, for `ν > 0`: `V` is divergence free with curl `E`; `∂ₛV + (V·∇)V - νΔV + ∇P = 0`;
`V·∇E = 0`; and `∂ₛE = νΔE`. -/
theorem exact_heat_scaling {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (z : Plane) :
    divergence (heatVelocity ν s) z = 0 ∧
    curl (heatVelocity ν s) z = heatVorticity ν s z ∧
    HasDerivAt (fun t => heatVelocity ν t z)
      (ν • (lap (heatVelocityX ν) s z, lap (heatVelocityY ν) s z) -
        advection (heatVelocity ν s) z - gradient (heatPressure ν s) z) s ∧
    scalarAdvection (heatVelocity ν s) (heatVorticity ν s) z = 0 ∧
    HasDerivAt (fun t => heatVorticity ν t z) (ν * lap (heatVorticity ν) s z) s :=
  ⟨(heatVortex_navierStokes hν hs z).2, (heatVortex_vorticity_not_advected hν hs z).1,
    (heatVortex_navierStokes hν hs z).1, (heatVortex_vorticity_not_advected hν hs z).2,
    (heatVortex_heat_equation hν hs z).1⟩

end UnforcedLeray.B0113
