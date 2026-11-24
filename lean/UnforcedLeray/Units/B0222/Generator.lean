import UnforcedLeray.Units.B0222.RadialFrame

/-!
# B0222 helper: the vector generator `A_ε^vec` and its conjugation identity

Blueprint unit B0222 (label `eq:st18-t00115`), `paper/main.tex` lines 3327–3339.

For the meridional vector heat equation the profile `b = (b_r, b_z)` has components in
`(e_r, e_z)` (B0220, tex lines 3294–3295) and (display `eq:st18-t00115`, tex lines 3328–3332)

  `A_ε^vec = -S + ν s diag(Q_ε² + ∂_η² - ε², Q_ε² + ∂_η²)`   (`AepsVec`).

Its radial term `-ε²` is the vector-basis contribution `-r⁻²` of the cylindrical vector
Laplacian (tex lines 3333–3334; `B0222/RadialFrame.lean`), and `A_ε^vec` at `ε = 0` is the
limiting generator `A_0 = -S + ν s Δ_{q,η}` acting componentwise (tex lines 3335–3338;
`AepsVec_zero`).

**Conjugation identity** (`outerGenVec_fieldU`): the Cartesian vector operator
`ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` (componentwise, `outerGenVec`; tex lines 3343–3347) applied to
the meridional lift `U = a (b_r e_r + b_z e_z)` (B0220, `fieldU`) is the lift of `A_ε^vec b`, at
every point off the axis, for `b` of class `C²` at the chart point.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220 UnforcedLeray.B0221

namespace UnforcedLeray.B0222

/-! ### The vector generator (tex lines 3327–3338) -/

/-- The radial selector `diag(1, 0)` on meridional components `(b_r, b_z)`. -/
def radialSel (i : Fin 2) : ℝ := if i = 0 then 1 else 0

@[simp] theorem radialSel_zero : radialSel 0 = 1 := by simp [radialSel]

@[simp] theorem radialSel_one : radialSel 1 = 0 := by simp [radialSel]

/-- **The exact meridional vector generator** (display `eq:st18-t00115`, tex lines 3328–3332):
`A_ε^vec b = -S b + ν s diag(Q_ε² + ∂_η² - ε², Q_ε² + ∂_η²) b` on profiles
`b = (b_r, b_z) : (s, q, η) ↦ ℝ²`, componentwise in `(e_r, e_z)`. The operators `S`, `Q_ε`,
`∂_η` are those of `eq:st18-t00114` (B0221: `opS`, `opQ`, `dEta`). -/
def AepsVec (ν ε : ℝ) (b : Profile → Merid) (p : Profile) : Merid :=
  WithLp.toLp 2 fun i =>
    -opS (fun p' => b p' i) p +
      ν * p.1 * (opQ ε (opQ ε fun p' => b p' i) p + dEta (dEta fun p' => b p' i) p -
        radialSel i * ε ^ 2 * b p i)

/-- The radial component of `A_ε^vec b`: the scalar generator `A_ε` of `eq:st18-t00114` plus
the frame term `-ν s ε² b_r`. -/
theorem AepsVec_apply_zero (ν ε : ℝ) (b : Profile → Merid) (p : Profile) :
    AepsVec ν ε b p 0 = Aeps ν ε (fun p' => b p' 0) p - ν * p.1 * ε ^ 2 * b p 0 := by
  simp only [AepsVec, PiLp.toLp_apply, radialSel_zero, Aeps, opS]
  ring

/-- The axial component of `A_ε^vec b` is the scalar generator `A_ε b_z`. -/
theorem AepsVec_apply_one (ν ε : ℝ) (b : Profile → Merid) (p : Profile) :
    AepsVec ν ε b p 1 = Aeps ν ε (fun p' => b p' 1) p := by
  simp only [AepsVec, PiLp.toLp_apply, radialSel_one, Aeps, opS]
  ring

/-- **The limiting generator acts componentwise** (tex lines 3335–3338): at `ε = 0`,
`A_0^vec b = (A_0 b_r, A_0 b_z)` with `A_0 = -S + ν s Δ_{q,η}`. -/
theorem AepsVec_zero (ν : ℝ) (b : Profile → Merid) (p : Profile) :
    AepsVec ν 0 b p = WithLp.toLp 2 fun i => A0 ν (fun p' => b p' i) p := by
  ext i
  simp only [AepsVec, PiLp.toLp_apply, A0, opQ_zero, opS]
  ring

/-- The radial frame term of `A_ε^vec` is `-ν s ε² b_r` (the image of the vector-basis term
`-ν ε² r⁻² U_r`, tex lines 3333–3334): `A_ε^vec b = (A_ε b_r, A_ε b_z) - ν s ε² (b_r, 0)`. -/
theorem AepsVec_eq_scalar_sub (ν ε : ℝ) (b : Profile → Merid) (p : Profile) :
    AepsVec ν ε b p = WithLp.toLp 2 (fun i => Aeps ν ε (fun p' => b p' i) p) -
      (ν * p.1 * ε ^ 2 * b p 0) • (EuclideanSpace.single 0 1 : Merid) := by
  ext i
  fin_cases i
  · simp [AepsVec_apply_zero]
  · simp [AepsVec_apply_one]

/-! ### The outer vector operator (tex lines 3343–3347) -/

/-- The Cartesian outer operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` on vector fields
`V : ℝ³ × ℝ → ℝ³`, acting on each Cartesian component (B0221, `outerGen`). -/
def outerGenVec (ν ε : ℝ) (V : Space × ℝ → Space) (y : Space × ℝ) : Space :=
  WithLp.toLp 2 fun j => outerGen ν ε (fun y' => V y' j) y

/-! ### The scalar lift has no angular derivative -/

section Angular

variable {ε : ℝ} {b : Profile → ℝ} {x : Space} {τ : ℝ}

theorem spatialPartial_liftU_zero (hε : ε ≠ 0) (hx : radius x ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    spatialPartial (liftU ε b) 0 (x, τ) = x 0 * radAlpha b ε τ (x 2) (radius x) := by
  have hU1 : DifferentiableAt ℝ (fun y => liftU ε b (y, τ)) x :=
    (contDiffAt_liftU_slice hε hx hb).differentiableAt (by norm_num)
  have hb1 : DifferentiableAt ℝ b (Gm ε τ (x 2) (radius x)) := hb.differentiableAt (by norm_num)
  have hl0 : (fun t : ℝ => liftU ε b (x + t • coordinateVector 0, τ)) =
      fun t => (lineR (radius x) (x 0) t)⁻¹ * b (Gm ε τ (x 2) (lineR (radius x) (x 0) t)) := by
    funext t
    rw [liftU_eq, radius_line0]
    simp [coordinateVector]
  simp only [spatialPartial]
  rw [fderiv_eq_deriv_line hU1, hl0, radial_first (radius_pos hx) hε hb1]

theorem spatialPartial_liftU_one (hε : ε ≠ 0) (hx : radius x ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    spatialPartial (liftU ε b) 1 (x, τ) = x 1 * radAlpha b ε τ (x 2) (radius x) := by
  have hU1 : DifferentiableAt ℝ (fun y => liftU ε b (y, τ)) x :=
    (contDiffAt_liftU_slice hε hx hb).differentiableAt (by norm_num)
  have hb1 : DifferentiableAt ℝ b (Gm ε τ (x 2) (radius x)) := hb.differentiableAt (by norm_num)
  have hl1 : (fun t : ℝ => liftU ε b (x + t • coordinateVector 1, τ)) =
      fun t => (lineR (radius x) (x 1) t)⁻¹ * b (Gm ε τ (x 2) (lineR (radius x) (x 1) t)) := by
    funext t
    rw [liftU_eq, radius_line1]
    simp [coordinateVector]
  simp only [spatialPartial]
  rw [fderiv_eq_deriv_line hU1, hl1, radial_first (radius_pos hx) hε hb1]

/-- The lift `a b(s,q,η)` of a scalar profile is axisymmetric: `∂_φ (a b) = 0` off the axis. -/
theorem angularPartial_liftU (hε : ε ≠ 0) (hx : radius x ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) : angularPartial (liftU ε b) (x, τ) = 0 := by
  simp only [angularPartial]
  rw [spatialPartial_liftU_zero hε hx hb, spatialPartial_liftU_one hε hx hb]
  ring

end Angular

/-! ### The conjugation identity -/

/-- The meridional lift as `U_r e_r + U_z e_z` with `U_r = a b_r`, `U_z = a b_z`. -/
theorem fieldU_eq (ε : ℝ) (b : Profile → Merid) (y : Space × ℝ) :
    fieldU ε b y = liftU ε (fun p => b p 0) y • unitR y.1 + liftU ε (fun p => b p 1) y • unitZ := by
  simp only [fieldU, frame_apply, liftU, smul_add, smul_smul, smul_eq_mul]

/-- The Cartesian components of a `C²` meridional profile are `C²`. -/
theorem contDiffAt_comp {b : Profile → Merid} {p : Profile} (hb : ContDiffAt ℝ 2 b p)
    (i : Fin 2) : ContDiffAt ℝ 2 (fun p' => b p' i) p :=
  ((EuclideanSpace.proj i : Merid →L[ℝ] ℝ).contDiff.contDiffAt).comp p hb

/-- **Conjugation identity for the vector generator** (tex lines 3327–3347, blueprint B0222).
For the meridional lift `U = a (b_r e_r + b_z e_z)` of `eq:st18-t00113` (`a = 1/r`, `s = r⁻²`,
`q = ε⁻¹ log r + τ/(2ε)`, `η = z/(εr)`) and a profile `b = (b_r, b_z)` of class `C²` at the chart
point, at every `x` off the axis
`(ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ) U (x, τ) = a (A_ε^vec b)_r e_r + a (A_ε^vec b)_z e_z`,
the Cartesian operator acting componentwise. -/
theorem outerGenVec_fieldU {ν ε : ℝ} (hε : ε ≠ 0) {b : Profile → Merid} {x : Space} {τ : ℝ}
    (hx : radius x ≠ 0) (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    outerGenVec ν ε (fieldU ε b) (x, τ) = fieldU ε (AepsVec ν ε b) (x, τ) := by
  have hb0 := contDiffAt_comp hb 0
  have hb1 := contDiffAt_comp hb 1
  have hW0 := contDiffAt_liftU_slice hε hx hb0
  have hφ := angularPartial_liftU hε hx hb0
  have hr := radius_pos hx
  have hp1 : (chart ε (x, τ)).1 = (radius x ^ 2)⁻¹ := rfl
  have hrad : ∀ j : Fin 3, unitZ j = 0 →
      (fun y' : Space × ℝ => fieldU ε b y' j) = fun y => unitR y.1 j * liftU ε (fun p => b p 0) y := by
    intro j hj
    funext y'
    rw [fieldU_eq, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, hj, smul_eq_mul,
      smul_eq_mul]
    ring
  ext j
  simp only [outerGenVec, PiLp.toLp_apply]
  rw [fieldU_eq ε (AepsVec ν ε b), PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply]
  simp only [liftU, smul_eq_mul]
  rw [AepsVec_apply_zero, AepsVec_apply_one]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [hrad 0 unitZ_apply_zero, outerGen_unitR_mul ν ε 0 hx hW0 hφ, outerGen_liftU hε hx hb0,
      unitZ_apply_zero, hp1]
    simp only [liftU, liftA]
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [hrad 1 unitZ_apply_one, outerGen_unitR_mul ν ε 1 hx hW0 hφ, outerGen_liftU hε hx hb0,
      unitZ_apply_one, hp1]
    simp only [liftU, liftA]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have h2 : (fun y' : Space × ℝ => fieldU ε b y' 2) = liftU ε (fun p => b p 1) := by
      funext y'
      rw [fieldU_eq, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, unitR_apply_two,
        unitZ_apply_two, smul_eq_mul, smul_eq_mul]
      ring
    rw [h2, outerGen_liftU hε hx hb1, unitR_apply_two, unitZ_apply_two]
    ring

end UnforcedLeray.B0222
