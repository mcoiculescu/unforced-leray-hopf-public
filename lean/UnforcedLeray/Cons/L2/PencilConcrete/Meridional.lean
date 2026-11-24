import UnforcedLeray.Cons.L2.PencilConcrete.RingNull

/-!
# C7 concrete pencil, helper: meridional fields and the inverse natural lift

`paper/main.tex`: the group `𝒪` of orthogonal maps fixing `e₃` and "axisymmetric without
swirl exactly when `𝒪`-invariant" (lines 112–115); the natural lift `𝒩_vb = √sb`
(`eq:m4-free-spaces`, lines 7275–7283, B0550) and its inverse `𝒩_v⁻¹` used in
`J_μ = 𝒩_v⁻¹J^phys_μ` (`eq:stress-setup:3.18`, lines 9169–9187, B0576); the inlet
`a_φ = 0` (`eq:stress-setup:3.22`, lines 9223–9234, B0571) and its heat evolution
`J^phys_μ = e^{νΔ}a`.

* `IsMeridional f`: off the axis `f(y) = f_r(y*)e_r + f_z(y*)e_z` with `y* = (ϱ, 0, y₃)`, the
  meridian point (`meridianPoint`). This is "axisymmetric without swirl", read off the
  meridian half-plane.
* `FixesAxis g`, `Equivariant g f`: the action of `𝒪`. `isMeridional_of_equivariant`: an
  `𝒪`-equivariant field is meridional (a rotation carries `y*` to `y`; the reflection
  `y₂ ↦ -y₂` fixes `y*` and kills the azimuthal component there).
* `inletField_equivariant`: the modulated inlet `a` is `𝒪`-equivariant;
  `heatAverage_equivariant`: so is its Gaussian average (the kernel is radial and isometries
  preserve Lebesgue measure; no integrability is needed, both sides being Bochner integrals
  related by a change of variables). Hence `inletColumn_isMeridional`: the free inlet column
  `J^phys_μα` is meridional at every phase, for every `α`.
* `unlift R v` is `𝒩_v⁻¹v`: `b(s, ξ, η) = s^{-1/2}(v_r, v_z)(τ*, y*)` with
  `τ* = 2ξ/R + log s`, `y* = (R/√s, 0, η/√s)` (the inverse of the chart on the meridian
  half-plane). `cylinderLift_unlift`: for `R > 0` and meridional `v`, `𝒩_v𝒩_v⁻¹v = v` off the
  axis.

Everything here is proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Blueprint.C07.PencilConcrete

open MatrixCrossing

/-! ## Meridional fields -/

/-- The meridian point `y* = (ϱ, 0, y₃)` of `y`, `ϱ = (y₁² + y₂²)^{1/2}`. -/
def meridianPoint (y : Space) : Space :=
  WithLp.toLp 2 ![Real.sqrt (y 0 ^ 2 + y 1 ^ 2), 0, y 2]

/-- **Axisymmetric without swirl** (lines 112–115), read off the meridian half-plane: off the
axis, `f(y) = f_r(y*)e_r + f_z(y*)e_z`. -/
def IsMeridional (f : SpatialField) : Prop :=
  ∀ y : Space, y 0 ^ 2 + y 1 ^ 2 ≠ 0 →
    f y = (f (meridianPoint y)) 0 • radialUnit y + (f (meridianPoint y)) 2 • coordinateVector 2

/-- An orthogonal map of `ℝ³` fixing `e₃` (the group `𝒪`, line 112), in the form used. -/
structure FixesAxis (g : Space ≃ₗᵢ[ℝ] Space) : Prop where
  third : ∀ x : Space, (g x) 2 = x 2
  planar : ∀ x : Space, (g x) 0 ^ 2 + (g x) 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2
  axis : g (coordinateVector 2) = coordinateVector 2

/-- `f(gx) = g f(x)`. -/
def Equivariant (g : Space ≃ₗᵢ[ℝ] Space) (f : SpatialField) : Prop := ∀ x, f (g x) = g (f x)

theorem coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i : Space) j = if j = i then 1 else 0 := by
  simp [coordinateVector, PiLp.single_apply]

theorem eq_coords (v : Space) :
    v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 + v 2 • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [coordinateVector_apply]

theorem horizontal_eq (y : Space) :
    (WithLp.toLp 2 ![y 0, y 1, 0] : Space) = y - y 2 • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [coordinateVector_apply]

theorem ringChart_fixesAxis {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (R τ : ℝ) (y : Space) :
    ringChart R τ (g y) = ringChart R τ y := by
  simp only [ringChart, hg.third, hg.planar]

theorem radialUnit_fixesAxis {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (y : Space) :
    radialUnit (g y) = g (radialUnit y) := by
  simp only [radialUnit, hg.planar, map_smul, horizontal_eq, map_sub, hg.axis, hg.third]

theorem inletField_equivariant {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (R μ : ℝ)
    (ψ : ℝ × ℝ → ℝ) (τ : ℝ) : Equivariant g (inletField R μ ψ τ) := by
  intro x
  simp only [inletField, ringChart_fixesAxis hg, radialUnit_fixesAxis hg, map_add, map_smul,
    hg.axis]

theorem equivariant_add {g : Space ≃ₗᵢ[ℝ] Space} {f f' : SpatialField} (hf : Equivariant g f)
    (hf' : Equivariant g f') : Equivariant g (fun y => f y + f' y) := by
  intro x
  simp only [hf x, hf' x, map_add]

theorem equivariant_smul {g : Space ≃ₗᵢ[ℝ] Space} {f : SpatialField} (c : ℝ)
    (hf : Equivariant g f) : Equivariant g (fun y => c • f y) := by
  intro x
  simp only [hf x, map_smul]

/-- **The Gaussian average of an equivariant field is equivariant.** -/
theorem heatAverage_equivariant {g : Space ≃ₗᵢ[ℝ] Space} {f : SpatialField} (t : ℝ)
    (hf : Equivariant g f) : Equivariant g (Heat.average t f) := by
  intro x
  have hmp : MeasurePreserving g volume volume := g.measurePreserving
  have h1 := hmp.integral_comp g.toHomeomorph.measurableEmbedding
    (fun z => Heat.kernel t z • f (g x - z))
  simp only [Heat.average]
  rw [← h1]
  have e : ∀ w : Space, Heat.kernel t (g w) • f (g x - g w) =
      g.toLinearIsometry (Heat.kernel t w • f (x - w)) := by
    intro w
    have hk : Heat.kernel t (g w) = Heat.kernel t w := by
      simp only [Heat.kernel, Heat.Gaussian.kernel, LinearIsometryEquiv.norm_map]
    rw [hk, ← map_sub, hf]
    simp
  simp only [e]
  exact LinearIsometry.integral_comp_comm g.toLinearIsometry _

/-! ## Rotations about the axis and the reflection -/

/-- The rotation `(y₁, y₂, y₃) ↦ (cy₁ - sy₂, sy₁ + cy₂, y₃)`. -/
def rotLin (c s : ℝ) : Space →ₗ[ℝ] Space where
  toFun y := WithLp.toLp 2 ![c * y 0 - s * y 1, s * y 0 + c * y 1, y 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem rotLin_apply (c s : ℝ) (y : Space) :
    rotLin c s y = WithLp.toLp 2 ![c * y 0 - s * y 1, s * y 0 + c * y 1, y 2] := rfl

theorem rotLin_comp {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    rotLin c s ∘ₗ rotLin c (-s) = LinearMap.id := by
  ext y i
  fin_cases i <;> simp [rotLin_apply]
  · linear_combination y 0 * h
  · linear_combination y 1 * h

theorem rotLin_comp' {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    rotLin c (-s) ∘ₗ rotLin c s = LinearMap.id := by
  have := rotLin_comp (c := c) (s := -s) (by rw [neg_sq]; exact h)
  rwa [neg_neg] at this

/-- The rotation about the axis as a linear isometry equivalence. -/
def rotation (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := LinearEquiv.ofLinearMap (rotLin c s) (rotLin c (-s)) (rotLin_comp h)
    (rotLin_comp' h)
  norm_map' y := by
    show ‖rotLin c s y‖ = ‖y‖
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    simp only [Fin.sum_univ_three, rotLin_apply, Real.norm_eq_abs, sq_abs]
    simp
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * h

theorem rotation_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (y : Space) :
    rotation c s h y = WithLp.toLp 2 ![c * y 0 - s * y 1, s * y 0 + c * y 1, y 2] := rfl

theorem rotation_fixesAxis (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : FixesAxis (rotation c s h) where
  third x := by simp [rotation_apply]
  planar x := by
    simp [rotation_apply]
    linear_combination (x 0 ^ 2 + x 1 ^ 2) * h
  axis := by
    ext i
    fin_cases i <;> simp [rotation_apply, coordinateVector_apply]

/-- The reflection `(y₁, y₂, y₃) ↦ (y₁, -y₂, y₃)` in the meridian plane `y₂ = 0`. -/
def reflLin : Space →ₗ[ℝ] Space where
  toFun y := WithLp.toLp 2 ![y 0, -y 1, y 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

theorem reflLin_apply (y : Space) : reflLin y = WithLp.toLp 2 ![y 0, -y 1, y 2] := rfl

theorem reflLin_comp : reflLin ∘ₗ reflLin = LinearMap.id := by
  ext y i
  fin_cases i <;> simp [reflLin_apply]

/-- The reflection as a linear isometry equivalence. -/
def reflection : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := LinearEquiv.ofLinearMap reflLin reflLin reflLin_comp reflLin_comp
  norm_map' y := by
    show ‖reflLin y‖ = ‖y‖
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    simp [Fin.sum_univ_three, reflLin_apply]

theorem reflection_apply (y : Space) : reflection y = WithLp.toLp 2 ![y 0, -y 1, y 2] := rfl

theorem reflection_fixesAxis : FixesAxis reflection where
  third x := by simp [reflection_apply]
  planar x := by simp [reflection_apply]
  axis := by
    ext i
    fin_cases i <;> simp [reflection_apply, coordinateVector_apply]

/-- **An `𝒪`-equivariant field is meridional.** -/
theorem isMeridional_of_equivariant {f : SpatialField}
    (hf : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → Equivariant g f) : IsMeridional f := by
  intro y hy
  have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
  set ρ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρsq : ρ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hpos.le
  have hcs : (y 0 / ρ) ^ 2 + (y 1 / ρ) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hρsq, div_self (by positivity)]
  set g := rotation (y 0 / ρ) (y 1 / ρ) hcs with hg
  have hgy : g (meridianPoint y) = y := by
    ext i
    fin_cases i <;> simp [hg, rotation_apply, meridianPoint, ← hρ] <;> field_simp
  have hge0 : g (coordinateVector 0) = radialUnit y := by
    ext i
    fin_cases i <;> simp [hg, rotation_apply, coordinateVector_apply, radialUnit, ← hρ] <;>
      field_simp
  -- no swirl at the meridian point
  have hrefl : reflection (meridianPoint y) = meridianPoint y := by
    ext i
    fin_cases i <;> simp [reflection_apply, meridianPoint]
  have h1 : (f (meridianPoint y)) 1 = 0 := by
    have := hf reflection reflection_fixesAxis (meridianPoint y)
    rw [hrefl] at this
    have h := congrArg (fun v : Space => v 1) this
    simp only [reflection_apply] at h
    simp at h
    linarith
  have key := hf g (rotation_fixesAxis _ _ hcs) (meridianPoint y)
  rw [hgy] at key
  rw [key]
  conv_lhs => rw [eq_coords (f (meridianPoint y)), h1]
  rw [map_add, map_add, map_smul, map_smul, map_smul, hge0, (rotation_fixesAxis _ _ hcs).axis,
    zero_smul, add_zero]

/-- **The free inlet column is meridional** at every phase, for every inlet `α`
(`eq:stress-setup:3.22`: `a_φ = 0`, the inlet is axisymmetric; `J^phys = e^{νΔ}a`). -/
theorem inletColumn_isMeridional (ν R μ : ℝ) (ψ : Fin 2 → ℝ × ℝ → ℝ) (α : Vector2) (τ : ℝ) :
    IsMeridional (inletColumn ν R μ ψ α τ) := by
  refine isMeridional_of_equivariant fun g hg => ?_
  exact heatAverage_equivariant ν (equivariant_add
    (equivariant_smul _ (inletField_equivariant hg R μ (ψ 0) τ))
    (equivariant_smul _ (inletField_equivariant hg R μ (ψ 1) τ)))

/-! ## The inverse natural lift -/

/-- **The inverse natural lift** `𝒩_v⁻¹v`: `b(s, ξ, η) = s^{-1/2}(v_r, v_z)(τ*, y*)` with
`τ* = 2ξ/R + log s` and `y* = (R/√s, 0, η/√s)` (the chart inverted on the meridian
half-plane; `v_r = v₁`, `v_z = v₃` there). For `s ≤ 0` (outside the chart) it takes Lean's
values; the lift never reads them. -/
def unlift (R : ℝ) (v : ℝ → SpatialField) : CylinderField := fun x =>
  ((Real.sqrt x.1)⁻¹ * (v (2 * x.2.1 / R + Real.log x.1)
      (WithLp.toLp 2 ![R / Real.sqrt x.1, 0, x.2.2 / Real.sqrt x.1])) 0,
    (Real.sqrt x.1)⁻¹ * (v (2 * x.2.1 / R + Real.log x.1)
      (WithLp.toLp 2 ![R / Real.sqrt x.1, 0, x.2.2 / Real.sqrt x.1])) 2)

theorem ringChart_fst_pos {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {y : Space}
    (hy : y 0 ^ 2 + y 1 ^ 2 ≠ 0) : 0 < (ringChart R τ y).1 := by
  have : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
  simp only [ringChart]
  positivity

/-- The chart inverted on the meridian half-plane: `τ* = τ` and `y* = (ϱ, 0, y₃)`. -/
theorem unlift_point {R : ℝ} (hR : 0 < R) (τ : ℝ) {y : Space} (hy : y 0 ^ 2 + y 1 ^ 2 ≠ 0) :
    2 * (ringChart R τ y).2.1 / R + Real.log (ringChart R τ y).1 = τ ∧
      (WithLp.toLp 2 ![R / Real.sqrt (ringChart R τ y).1, 0,
        (ringChart R τ y).2.2 / Real.sqrt (ringChart R τ y).1] : Space) = meridianPoint y := by
  have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
  have hs : 0 < R ^ 2 / (y 0 ^ 2 + y 1 ^ 2) := by positivity
  have hq : Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hsq : Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) = R / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
    rw [Real.sqrt_div' _ hpos.le, Real.sqrt_sq hR.le]
  have hρ : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ⟨?_, ?_⟩
  · simp only [ringChart]
    field_simp
    ring
  · ext i
    fin_cases i
    · simp only [ringChart, meridianPoint]
      simp only [Fin.zero_eta, Fin.isValue, WithLp.ofLp_toLp, Matrix.cons_val_zero]
      rw [hsq]
      field_simp
    · simp [meridianPoint]
    · simp only [ringChart, meridianPoint]
      simp
      field_simp

/-- **`𝒩_v𝒩_v⁻¹v = v` off the axis** for a meridional `v` and `R > 0`. -/
theorem cylinderLift_unlift {R : ℝ} (hR : 0 < R) {v : ℝ → SpatialField}
    (hv : ∀ τ, IsMeridional (v τ)) (τ : ℝ) {y : Space} (hy : y 0 ^ 2 + y 1 ^ 2 ≠ 0) :
    cylinderLift R (unlift R v) τ y = v τ y := by
  obtain ⟨hτ, hpt⟩ := unlift_point hR τ hy
  have hs := ringChart_fst_pos hR.ne' τ hy
  have hq : Real.sqrt (ringChart R τ y).1 ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  simp only [cylinderLift, unlift, hτ, hpt]
  rw [hv τ y hy, smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ hq, one_mul, one_mul]

/-! ## Pointwise linearity of the lift -/

theorem cylinderLift_add (R : ℝ) (b b' : CylinderField) (τ : ℝ) (y : Space) :
    cylinderLift R (b + b') τ y = cylinderLift R b τ y + cylinderLift R b' τ y := by
  simp only [cylinderLift, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  module

theorem cylinderLift_smul (R c : ℝ) (b : CylinderField) (τ : ℝ) (y : Space) :
    cylinderLift R (c • b) τ y = c • cylinderLift R b τ y := by
  simp only [cylinderLift, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  module

/-- Off the axis the lift vanishes exactly where the field does (`e_r ⊥ e_z`, `√s > 0`). -/
theorem cylinderLift_eq_zero_iff {R : ℝ} (hR : R ≠ 0) (b : CylinderField) (τ : ℝ) {y : Space}
    (hy : y 0 ^ 2 + y 1 ^ 2 ≠ 0) :
    cylinderLift R b τ y = 0 ↔ b (ringChart R τ y) = 0 := by
  have hs := ringChart_fst_pos hR τ hy
  have hq : Real.sqrt (ringChart R τ y).1 ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
  have hρ : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  constructor
  · intro h
    simp only [cylinderLift, smul_eq_zero, hq, false_or] at h
    set u := (b (ringChart R τ y)).1
    set w := (b (ringChart R τ y)).2
    have c0 : (u • radialUnit y + w • coordinateVector 2 : Space) 0 =
        u * ((Real.sqrt (y 0 ^ 2 + y 1 ^ 2))⁻¹ * y 0) := by
      simp [radialUnit, coordinateVector_apply]
    have c1 : (u • radialUnit y + w • coordinateVector 2 : Space) 1 =
        u * ((Real.sqrt (y 0 ^ 2 + y 1 ^ 2))⁻¹ * y 1) := by
      simp [radialUnit, coordinateVector_apply]
    have c2 : (u • radialUnit y + w • coordinateVector 2 : Space) 2 = w := by
      simp [radialUnit, coordinateVector_apply]
    have h0 := congrArg (fun v : Space => v 0) h
    have h1 := congrArg (fun v : Space => v 1) h
    have h2 := congrArg (fun v : Space => v 2) h
    simp only at h0 h1 h2
    rw [c0] at h0
    rw [c1] at h1
    rw [c2] at h2
    refine Prod.ext ?_ h2
    by_contra hu
    have hy0 : y 0 = 0 := by
      have := (mul_eq_zero.1 h0).resolve_left hu
      exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hρ)
    have hy1 : y 1 = 0 := by
      have := (mul_eq_zero.1 h1).resolve_left hu
      exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hρ)
    exact hy (by rw [hy0, hy1]; ring)
  · intro h
    simp [cylinderLift, h]

end UnforcedLeray.Blueprint.C07.PencilConcrete
