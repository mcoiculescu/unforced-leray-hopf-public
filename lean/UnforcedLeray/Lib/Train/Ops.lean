import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Units.B0146
import UnforcedLeray.Lib.Train.Params

/-!
# Vector fields on the cylinder carrier and the planar Navier–Stokes residual (INF16 T0–T2)


(shared notation and target T2); decision D1 of `scoping/README.md` (cylinder fields are
`c`-periodic functions on `Plane = ℝ × ℝ`, vector values in `Vec = EuclideanSpace ℝ (Fin 2)`).

The manuscript's equation (`eq:m3-train`, `paper/main.tex` lines 2045–2050; `eq:st18-t00140`,
lines 2141–2147; blueprint units B0140, B0146) is
`∂ₛv + v·∇v - νΔv + ∇p = 0`, `div v = 0`.

All spatial derivatives are the classical one-variable partials `Cyl.partialQ`,
`Cyl.partialEta` (the same as the library's `GaussianVortex.partialX`, `partialY`). Since
`deriv` takes the junk value `0` at non-differentiable points, every statement in which these
operators occur is accompanied, in `PeriodizedVortex.lean` and `Datum.lean`, by the
`HasDerivAt` facts saying that the partials involved are genuine.

Main declarations: `Vec`, `toVecL` (the coordinate equivalence
`ℝ × ℝ ≃L Vec`), `toVec`, `lapS`, `vecLaplacian`, `gradS`, `advection`, `matDiv`
(`(div Q)^l = ∂_k Q^{kl}`), `momentumResidual`, and the transfer lemmas from the unit B0146
operators on `ℝ × ℝ`-valued fields (`advection_toVec`, `vecLaplacian_toVec`, `gradS_eq`,
`matDiv_eq`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Train

open UnforcedLeray.Cyl (Plane Vec2 partialQ partialEta)

/-- Meridional vectors: the Euclidean plane (decision D1). -/
abbrev Vec := Cyl.Vec2

/-- The coordinate equivalence `ℝ × ℝ ≃L[ℝ] Vec`, `(x, y) ↦ (x, y)`. -/
def toVecL : (ℝ × ℝ) ≃L[ℝ] Vec :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- The vector with Cartesian components `(v.1, v.2)`. -/
def toVec (v : ℝ × ℝ) : Vec := toVecL v

@[simp] theorem toVecL_apply (v : ℝ × ℝ) : toVecL v = toVec v := rfl

@[simp] theorem toVec_zero (v : ℝ × ℝ) : toVec v 0 = v.1 := rfl

@[simp] theorem toVec_one (v : ℝ × ℝ) : toVec v 1 = v.2 := rfl

theorem toVec_apply_eq_vcomp (v : ℝ × ℝ) (k : Fin 2) : toVec v k = B0146.vcomp v k := by
  fin_cases k <;> rfl

theorem toVec_add (v w : ℝ × ℝ) : toVec (v + w) = toVec v + toVec w := map_add toVecL v w

theorem toVec_sub (v w : ℝ × ℝ) : toVec (v - w) = toVec v - toVec w := map_sub toVecL v w

theorem toVec_neg (v : ℝ × ℝ) : toVec (-v) = -toVec v := map_neg toVecL v

theorem toVec_smul (r : ℝ) (v : ℝ × ℝ) : toVec (r • v) = r • toVec v := map_smul toVecL r v

theorem toVec_injective : Function.Injective toVec := toVecL.injective

/-- A vector is determined by its two components. -/
theorem Vec.ext {x y : Vec} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem eq_toVec (x : Vec) : x = toVec (x 0, x 1) := Vec.ext rfl rfl

/-- The Euclidean norm: `‖toVec (x, y)‖² = x² + y²`. -/
theorem norm_toVec_sq (v : ℝ × ℝ) : ‖toVec v‖ ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; rfl

theorem norm_toVec (v : ℝ × ℝ) : ‖toVec v‖ = Real.sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  rw [← norm_toVec_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ### Differential operators (classical partials) -/

/-- The scalar Laplacian `∂_q² f + ∂_η² f`. -/
def lapS (f : Plane → ℝ) (z : Plane) : ℝ :=
  partialQ (partialQ f) z + partialEta (partialEta f) z

/-- The componentwise vector Laplacian `Δu`. -/
def vecLaplacian (u : Plane → Vec) (z : Plane) : Vec :=
  toVec (lapS (fun w => u w 0) z, lapS (fun w => u w 1) z)

/-- The gradient `∇p = (∂_q p, ∂_η p)`. -/
def gradS (p : Plane → ℝ) (z : Plane) : Vec := toVec (partialQ p z, partialEta p z)

/-- The transport term `(u·∇)u`. -/
def advection (u : Plane → Vec) (z : Plane) : Vec :=
  toVec (u z 0 * partialQ (fun w => u w 0) z + u z 1 * partialEta (fun w => u w 0) z,
    u z 0 * partialQ (fun w => u w 1) z + u z 1 * partialEta (fun w => u w 1) z)

/-- The divergence of a 2-tensor field, `(div Q)^l = ∂_k Q^{kl}` (row index `k`). -/
def matDiv (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) (z : Plane) : Vec :=
  toVec (partialQ (fun w => Q w 0 0) z + partialEta (fun w => Q w 1 0) z,
    partialQ (fun w => Q w 0 1) z + partialEta (fun w => Q w 1 1) z)

/-- The Navier–Stokes momentum residual `∂ₛv + v·∇v - νΔv + ∇p` (tex lines 2045–2050). -/
def momentumResidual (ν : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) :
    Vec :=
  deriv (fun t => v t z) s + advection (v s) z - ν • vecLaplacian (v s) z + gradS (p s) z

/-! ### Transfer from `ℝ × ℝ`-valued fields (units B0113, B0146) -/

open UnforcedLeray.GaussianVortex (partialX partialY)

theorem lapS_eq (f : Plane → ℝ) (z : Plane) :
    lapS f z = partialX (partialX f) z + partialY (partialY f) z := rfl

theorem gradS_eq (p : Plane → ℝ) (z : Plane) :
    gradS p z = toVec (GaussianVortex.gradient p z) := rfl

theorem advection_toVec (U : Plane → ℝ × ℝ) (z : Plane) :
    advection (fun w => toVec (U w)) z = toVec (GaussianVortex.advection U z) := rfl

theorem vecLaplacian_toVec (U : ℝ → Plane → ℝ × ℝ) (s : ℝ) (z : Plane) :
    vecLaplacian (fun w => toVec (U s w)) z =
      toVec (NonlinearBackground.lap (fun t w => (U t w).1) s z,
        NonlinearBackground.lap (fun t w => (U t w).2) s z) := rfl

theorem matDiv_eq (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) (z : Plane) :
    matDiv Q z = toVec (B0146.tensorDiv Q z) := rfl

/-- The residual of a field `toVec ∘ U` is the image of the unit-B0146 residual of `U`, provided
the time derivative exists. -/
theorem momentumResidual_toVec {ν : ℝ} {U : ℝ → Plane → ℝ × ℝ} {p : ℝ → Plane → ℝ} {s : ℝ}
    {z : Plane} {U' : ℝ × ℝ} (hU : HasDerivAt (fun t => U t z) U' s) :
    momentumResidual ν (fun t w => toVec (U t w)) p s z =
      toVec (B0146.nsResidual ν U p s z) := by
  have hd : HasDerivAt (fun t => toVec (U t z)) (toVec U') s :=
    (toVecL : (ℝ × ℝ) →L[ℝ] Vec).hasFDerivAt.comp_hasDerivAt s hU
  rw [momentumResidual, B0146.nsResidual, hd.deriv, hU.deriv, advection_toVec,
    vecLaplacian_toVec, gradS_eq, toVec_add, toVec_sub, toVec_add, toVec_smul]

end UnforcedLeray.Train
