import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Exact Cartesian differential identities for the actual Gaussian vortex. -/
noncomputable section
namespace UnforcedLeray.GaussianVortex

theorem hasDerivAt_planarGaussian_x (x y : ℝ) :
    HasDerivAt (fun a => planarGaussian (a, y))
      (-x / 2 * planarGaussian (x, y)) x := by
  convert (((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).div_const 4).neg).exp using 1 <;>
    first | rfl | (dsimp [planarGaussian, radiusSq]; ring)

theorem hasDerivAt_planarGaussian_y (x y : ℝ) :
    HasDerivAt (fun a => planarGaussian (x, a))
      (-y / 2 * planarGaussian (x, y)) y := by
  convert (((((hasDerivAt_id y).pow 2).const_add (x ^ 2)).div_const 4).neg).exp using 1 <;>
    first | rfl | (dsimp [planarGaussian, radiusSq]; ring)

theorem partialX_planarGaussian (z : Plane) :
    partialX planarGaussian z = -z.1 / 2 * planarGaussian z :=
  (hasDerivAt_planarGaussian_x z.1 z.2).deriv

theorem partialY_planarGaussian (z : Plane) :
    partialY planarGaussian z = -z.2 / 2 * planarGaussian z :=
  (hasDerivAt_planarGaussian_y z.1 z.2).deriv

theorem partialX_streamfunction (z : Plane) :
    partialX streamfunction z = z.1 * planarGaussian z := by
  change deriv (fun x => -2 * planarGaussian (x, z.2)) z.1 = _
  rw [((hasDerivAt_planarGaussian_x z.1 z.2).const_mul (-2)).deriv]
  ring

theorem partialY_streamfunction (z : Plane) :
    partialY streamfunction z = z.2 * planarGaussian z := by
  change deriv (fun y => -2 * planarGaussian (z.1, y)) z.2 = _
  rw [((hasDerivAt_planarGaussian_y z.1 z.2).const_mul (-2)).deriv]
  ring

theorem perpendicularGradient_streamfunction (z : Plane) :
    perpendicularGradient streamfunction z = velocity z := by
  simp only [perpendicularGradient, partialY_streamfunction, partialX_streamfunction, velocity]
  congr 1
  ring

theorem partialX_velocity_one (z : Plane) :
    partialX (fun w => (velocity w).1) z = z.1 * z.2 / 2 * planarGaussian z := by
  change deriv (fun x => -z.2 * planarGaussian (x, z.2)) z.1 = _
  rw [((hasDerivAt_planarGaussian_x z.1 z.2).const_mul (-z.2)).deriv]
  ring

theorem partialY_velocity_one (z : Plane) :
    partialY (fun w => (velocity w).1) z = (z.2 ^ 2 / 2 - 1) * planarGaussian z := by
  change deriv (fun y => -y * planarGaussian (z.1, y)) z.2 = _
  convert ((hasDerivAt_id z.2).neg.mul (hasDerivAt_planarGaussian_y z.1 z.2)).deriv using 1 <;>
    first | rfl | (dsimp; ring)

theorem partialX_velocity_two (z : Plane) :
    partialX (fun w => (velocity w).2) z = (1 - z.1 ^ 2 / 2) * planarGaussian z := by
  change deriv (fun x => x * planarGaussian (x, z.2)) z.1 = _
  convert ((hasDerivAt_id z.1).mul (hasDerivAt_planarGaussian_x z.1 z.2)).deriv using 1 <;>
    first | rfl | (dsimp; ring)

theorem partialY_velocity_two (z : Plane) :
    partialY (fun w => (velocity w).2) z = -z.1 * z.2 / 2 * planarGaussian z := by
  change deriv (fun y => z.1 * planarGaussian (z.1, y)) z.2 = _
  rw [((hasDerivAt_planarGaussian_y z.1 z.2).const_mul z.1).deriv]
  ring

/-- The actual Gaussian velocity is divergence free everywhere, including the origin. -/
theorem divergence_velocity (z : Plane) : divergence velocity z = 0 := by
  simp only [divergence, partialX_velocity_one, partialY_velocity_two]
  ring

/-- Its Cartesian curl is exactly the manuscript's Gaussian vorticity. -/
theorem curl_velocity (z : Plane) : curl velocity z = vorticity z := by
  simp only [curl, partialX_velocity_two, partialY_velocity_one, vorticity, radiusSq]
  ring

theorem planarGaussian_sq (z : Plane) :
    planarGaussian z ^ 2 = Real.exp (-(radiusSq z / 2)) := by
  rw [planarGaussian, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem partialX_pressure (z : Plane) :
    partialX pressure z = z.1 * planarGaussian z ^ 2 := by
  have h := ((((((hasDerivAt_id z.1).pow 2).add_const (z.2 ^ 2)).div_const 2).neg).exp).neg
  change deriv (fun x => -Real.exp (-((x ^ 2 + z.2 ^ 2) / 2))) z.1 = _
  rw [planarGaussian_sq]
  convert h.deriv using 1 <;> first | rfl | (dsimp [radiusSq]; ring)

theorem partialY_pressure (z : Plane) :
    partialY pressure z = z.2 * planarGaussian z ^ 2 := by
  have h := ((((((hasDerivAt_id z.2).pow 2).const_add (z.1 ^ 2)).div_const 2).neg).exp).neg
  change deriv (fun y => -Real.exp (-((z.1 ^ 2 + y ^ 2) / 2))) z.2 = _
  rw [planarGaussian_sq]
  convert h.deriv using 1 <;> first | rfl | (dsimp [radiusSq]; ring)

/-- The exact centripetal acceleration. -/
theorem advection_velocity (z : Plane) :
    advection velocity z = (-z.1 * planarGaussian z ^ 2, -z.2 * planarGaussian z ^ 2) := by
  simp only [advection, scalarAdvection]
  rw [partialX_velocity_one, partialY_velocity_one, partialX_velocity_two, partialY_velocity_two]
  simp only [velocity]
  apply Prod.ext <;> ring

/-- The actual unit-amplitude Gaussian vortex solves the stationary Euler momentum equation. -/
theorem stationary_euler (z : Plane) :
    advection velocity z + gradient pressure z = 0 := by
  apply Prod.ext <;>
    simp [advection_velocity, gradient, partialX_pressure, partialY_pressure]

theorem partialX_vorticity (z : Plane) :
    partialX vorticity z = z.1 * (radiusSq z / 4 - 2) * planarGaussian z := by
  have h := (((((hasDerivAt_id z.1).pow 2).add_const (z.2 ^ 2)).div_const 2).const_sub 2).mul
    (hasDerivAt_planarGaussian_x z.1 z.2)
  change deriv (fun x => (2 - (x ^ 2 + z.2 ^ 2) / 2) * planarGaussian (x, z.2)) z.1 = _
  convert h.deriv using 1 <;> first | rfl | (dsimp [radiusSq]; ring)

theorem partialY_vorticity (z : Plane) :
    partialY vorticity z = z.2 * (radiusSq z / 4 - 2) * planarGaussian z := by
  have h := (((((hasDerivAt_id z.2).pow 2).const_add (z.1 ^ 2)).div_const 2).const_sub 2).mul
    (hasDerivAt_planarGaussian_y z.1 z.2)
  change deriv (fun y => (2 - (z.1 ^ 2 + y ^ 2) / 2) * planarGaussian (z.1, y)) z.2 = _
  convert h.deriv using 1 <;> first | rfl | (dsimp [radiusSq]; ring)

/-- The background vorticity is stationary under its actual velocity field. -/
theorem scalarAdvection_vorticity (z : Plane) :
    scalarAdvection velocity vorticity z = 0 := by
  simp only [scalarAdvection, partialX_vorticity, partialY_vorticity, velocity]
  ring

/-- The Cartesian partials are evaluations of the actual Fréchet derivative. -/
theorem partialX_eq_fderiv {f : Plane → ℝ} {z : Plane}
    (hf : DifferentiableAt ℝ f z) : partialX f z = fderiv ℝ f z (1, 0) := by
  simpa only [Function.comp_def, partialX, id_eq] using
    (hf.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

theorem partialY_eq_fderiv {f : Plane → ℝ} {z : Plane}
    (hf : DifferentiableAt ℝ f z) : partialY f z = fderiv ℝ f z (0, 1) := by
  simpa only [Function.comp_def, partialY, id_eq] using
    (hf.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

/-- Coordinate advection equals the ordinary directional derivative. -/
theorem scalarAdvection_eq_fderiv (u : Plane → Plane) {f : Plane → ℝ} {z : Plane}
    (hf : DifferentiableAt ℝ f z) :
    scalarAdvection u f z = fderiv ℝ f z (u z) := by
  rw [scalarAdvection, partialX_eq_fderiv hf, partialY_eq_fderiv hf]
  have hu : u z = (u z).1 • ((1, 0) : Plane) + (u z).2 • ((0, 1) : Plane) := by
    apply Prod.ext <;> simp
  calc
    _ = fderiv ℝ f z ((u z).1 • ((1, 0) : Plane) + (u z).2 • ((0, 1) : Plane)) := by
      simp only [map_add, map_smul, smul_eq_mul]
    _ = _ := congrArg (fderiv ℝ f z) hu.symm

theorem advection_eq_fderiv {u : Plane → Plane} {z : Plane}
    (hu : DifferentiableAt ℝ u z) : advection u z = fderiv ℝ u z (u z) := by
  apply Prod.ext
  · change scalarAdvection u (fun w => (u w).1) z = _
    rw [scalarAdvection_eq_fderiv u hu.fst, hu.hasFDerivAt.fst.fderiv]
    rfl
  · change scalarAdvection u (fun w => (u w).2) z = _
    rw [scalarAdvection_eq_fderiv u hu.snd, hu.hasFDerivAt.snd.fderiv]
    rfl

/-- Stationary Euler written with the actual Fréchet derivative of the velocity. -/
theorem stationary_euler_fderiv (z : Plane) :
    fderiv ℝ velocity z (velocity z) + gradient pressure z = 0 := by
  rw [← advection_eq_fderiv (contDiff_velocity.differentiable (by simp)).differentiableAt]
  exact stationary_euler z

end UnforcedLeray.GaussianVortex
