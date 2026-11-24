import UnforcedLeray.Blueprint.Construction.Cylinder

/-!
# Step C8, part 1: the natural lift is axisymmetric without swirl

`paper/main.tex` lines 13693–13701 (`eq:st18-t00770`, blueprint unit B1005): the natural
physical lift `w_phys = 𝒩_v b = √s (b_r e_r + b_z e_z)`, with `s = R²/ϱ²`,
`ξ = Rτ/2 - (R/2) log s`, `η = √s y₃`, "has zero azimuthal component"; line 13739 uses
`eq:st18-t00770` for the symmetry of `b_*` required by `prop:unstable-background`
(lines 188–189, blueprint unit B1006).

**Statement proved (unconditionally).** For every ring radius `R`, every meridional field `b`
and every phase `τ`, the lift `cylinderLift R b τ` is invariant under every linear isometry
`g` of `ℝ³` fixing `e₃` (the manuscript's group `𝒪`, rotations about the axis and reflections
in planes containing it): `g (w (g⁻¹ x)) = w x` for every `x`, on the axis included (there the
chart gives `s = 0`, so the lift vanishes).

**Proof.** `g` preserves `x₃ = ⟨x, e₃⟩` and `|x|`, hence `x₁² + x₂²`, so the ring chart is
`g`-invariant; `e_r = ϱ⁻¹ (x - x₃ e₃)` is `g`-equivariant and `e₃` is fixed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.C08

open UnforcedLeray.Blueprint

/-- `(y₁, y₂, 0) = y - y₃ e₃`. -/
theorem toLp_planar_eq (v : Space) :
    (WithLp.toLp 2 ![v 0, v 1, 0] : Space) = v - v 2 • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [coordinateVector]

/-- The third coordinate is the pairing with `e₃`. -/
theorem coord_two_eq_inner (v : Space) : v 2 = inner ℝ (coordinateVector 2) v := by
  rw [coordinateVector, EuclideanSpace.inner_single_left]
  simp

/-- `|y|² = y₁² + y₂² + y₃²`. -/
theorem norm_sq_coords (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

section Group

variable (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g)
include hg

theorem symm_fixes_axis : g.symm (coordinateVector 2) = coordinateVector 2 :=
  g.symm_apply_eq.mpr hg.symm

/-- An isometry fixing `e₃` preserves `x₃`. -/
theorem symm_coord_two (x : Space) : (g.symm x) 2 = x 2 := by
  calc (g.symm x) 2 = inner ℝ (coordinateVector 2) (g.symm x) := coord_two_eq_inner _
    _ = inner ℝ (g.symm (coordinateVector 2)) (g.symm x) := by rw [symm_fixes_axis g hg]
    _ = inner ℝ (coordinateVector 2) x := LinearIsometryEquiv.inner_map_map _ _ _
    _ = x 2 := (coord_two_eq_inner x).symm

/-- An isometry fixing `e₃` preserves `x₁² + x₂²`. -/
theorem symm_planar_sq (x : Space) :
    (g.symm x) 0 ^ 2 + (g.symm x) 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  have h1 := norm_sq_coords (g.symm x)
  have h2 := norm_sq_coords x
  rw [LinearIsometryEquiv.norm_map, symm_coord_two g hg] at h1
  linarith

/-- The ring chart is invariant. -/
theorem ringChart_symm (R τ : ℝ) (x : Space) : ringChart R τ (g.symm x) = ringChart R τ x := by
  unfold ringChart
  rw [symm_planar_sq g hg, symm_coord_two g hg]

/-- The radial unit vector is equivariant. -/
theorem map_radialUnit_symm (x : Space) : g (radialUnit (g.symm x)) = radialUnit x := by
  unfold radialUnit
  rw [toLp_planar_eq, toLp_planar_eq, symm_planar_sq g hg, symm_coord_two g hg, map_smul,
    map_sub, map_smul, LinearIsometryEquiv.apply_symm_apply, hg]

/-- The lift commutes with `g` at every point. -/
theorem map_cylinderLift_symm (R : ℝ) (b : CylinderField) (τ : ℝ) (x : Space) :
    g (cylinderLift R b τ (g.symm x)) = cylinderLift R b τ x := by
  unfold cylinderLift
  rw [ringChart_symm g hg, map_smul, map_add, map_smul, map_smul, map_radialUnit_symm g hg, hg]

end Group

/-- **The lift is axisymmetric without swirl** (`eq:st18-t00770`, line 13739; units B1005,
B1006): at every phase, for every ring radius and every meridional field. -/
theorem cylinderLift_axisymmetric (R : ℝ) (b : CylinderField) (τ : ℝ) :
    IsAxisymmetricNoSwirl (cylinderLift R b τ) := fun g hg =>
  Filter.Eventually.of_forall fun x => map_cylinderLift_symm g hg R b τ x

end UnforcedLeray.Cons.C08
