import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# The Cartesian weak-stress inverse and its kernel field (source 1533-1537, 1638-1679,
2664-2683, 3582-3621, 3888-3897)

Source of record: `the November 2 reference manuscript`.

The kernel realization `StressKernelRealization` (`NearInst/Masked/Lemmas.lean`) identifies the curved
free inverse `S_ε = T_ε s div_ε` of `PartII-a` (`PartIIa.Teps = B0223.RepsVec ∘ PartIIa.PepsC`) on box
tensors with the unmasked kernel `fullOut` (`sep:resolvent`, `IIIa.sepW`).  The bridge is the source's
remark "the finite-curvature free inverse is the conjugate of the Cartesian weak-stress inverse"
(3888-3891).  This file defines that Cartesian inverse on the Cartesian objects of B0223/B0226.

## Variables

B0223 works in the outer Cartesian variable `x` with the outer semigroup
`S_ε(t)F(x,τ) = e^{t/2}[e^{νε²(e^t-1)Δ}F(·,τ-t)](e^{t/2}x)` on `X ℂ³ P = L²(ℝ³ × ℝ/Pℤ; ℂ³)`,
`P = 2εc`, and `physRes = ∫_0^∞ e^{-μt}S_ε(t) dt = (μ - A)^{-1}`, `A` its generator.  The similarity
variable of `sep:resolvent` and of `NearInst.cartLift` is `z = R x`, `R = ε⁻¹` (the chart
`s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ` with `ρ = |z'|`, source 1640-1641, 2666-2668,
is B0220's `s = r⁻²`, `q = ε⁻¹ log r + τ/(2ε)`, `η = x₃/(εr)` with `r = |x'| = ρ/R`).  Under
`x = z/R` the outer semigroup is the similarity semigroup `e^{h/2}[e^{ν(e^h-1)Δ}f(τ-h)](e^{h/2}y)` of
`sep:resolvent` (3606-3608), and `μ - A` is `D_μ = B - νΔ + μ - 1/2`.

## Objects

* `cplx3` : the complexification `ℝ³ → ℂ³`; `toX hP` : real `L²(dx dτ; ℝ³)` over one period
  (`B0220.PhysL2 ε c`) complexified and moved to the periodic space `X ℂ³ P` by `B0223.toCell`
  (measure preserving, `mp_toCell_phys`).
* `cartRes hν hP μ = (μ - A)^{-1} P_3D : PhysL2 ε c → X ℂ³ P` : the Cartesian projected free
  resolvent on real body forces; `P_3D = B0226.P3D` is the Cartesian Leray projection
  (`B0226.Peps_eq_starProjection`: its conjugate by the lift `J_ε` is the orthogonal projection of
  `H` onto the exact solenoidal fields, the real form of `PartIIa.PepsC`).
* `cartDiv M` : the row divergence `(div M)_i = Σ_j ∂_{x_j} M_ij` of a tensor field `M(x, τ)`.
* `CartStress hν hP μ M hM = (μ - A)^{-1} P_3D div M` : the Cartesian weak-stress inverse
  (`S_μ = R_μ div`, source 1533-1537) of a tensor field whose divergence is in `L²(dx dτ)`
  (`hM`); on smooth tensors this is the source's definition before completion.
* `IsCartTest P T` : smooth tensor fields `T(τ, z)` in the similarity variables, `P`-periodic in
  `τ`, with bounded spatial support ("we begin with smooth tensors", 3594-3596).
* `outerField R T (x, τ) = T(τ, R x)` : a similarity-variable tensor in the outer variable.
  For a chart tensor `m`, `outerField R (cartLift R c m)` is the tensor lift `𝒩_T m = s m`
  (source 2683) in outer Cartesian components.
* `kernelField ν μ R T (x, τ) = R · (-W_μ[T])(R x, τ)` with `W_μ = IIIa.sepW` (`sep:resolvent`,
  3611-3617; the factor `R` is the divergence `∂_x = R ∂_z`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

/-! ## Complexification and the periodic space -/

/-- The complexification `ℝ³ → ℂ³`, real-linear. -/
def cplx3Lin : Space →ₗ[ℝ] UnforcedLeray.B0223.SpaceC where
  toFun v := WithLp.toLp 2 fun i => ((v i : ℝ) : ℂ)
  map_add' v w := by
    ext i
    simp
  map_smul' a v := by
    ext i
    simp

/-- The complexification `ℝ³ → ℂ³`, continuous. -/
def cplx3 : Space →L[ℝ] UnforcedLeray.B0223.SpaceC :=
  LinearMap.toContinuousLinearMap cplx3Lin

theorem cplx3_apply (v : Space) (i : Fin 3) : cplx3 v i = ((v i : ℝ) : ℂ) := rfl

/-- `B0223.toCell` carries the periodic Lebesgue measure to `dx dτ` on one period `(0, 2εc]`. -/
theorem mp_toCell_phys {P ε c : ℝ} [Fact (0 < P)] (hP : P = 2 * ε * c) :
    MeasurePreserving (UnforcedLeray.B0223.toCell P) volume
      (UnforcedLeray.B0220.physMeasure ε c) := by
  rw [UnforcedLeray.B0223.physMeasure_eq hP]
  exact UnforcedLeray.B0223.mp_toCell

/-- Real `L²(dx dτ; ℝ³)` over one period `(0, P]`, complexified, as an element of the periodic space
`X ℂ³ P` (the phase `τ mod P` represented in `(0, P]`). -/
def toX {P ε c : ℝ} [Fact (0 < P)] (hP : P = 2 * ε * c) :
    UnforcedLeray.B0220.PhysL2 ε c →L[ℝ] UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P :=
  (Lp.compMeasurePreservingₗᵢ ℝ (UnforcedLeray.B0223.toCell P)
      (mp_toCell_phys hP)).toContinuousLinearMap.comp
    (cplx3.compLpL 2 (UnforcedLeray.B0220.physMeasure ε c))

theorem toX_ae {P ε c : ℝ} [Fact (0 < P)] (hP : P = 2 * ε * c)
    (g : UnforcedLeray.B0220.PhysL2 ε c) :
    (toX hP g : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun w => cplx3 ((g : Space × ℝ → Space) (UnforcedLeray.B0223.toCell P w)) := by
  have hmp := mp_toCell_phys (P := P) hP
  have h1 := Lp.coeFn_compMeasurePreserving
    (cplx3.compLpL 2 (UnforcedLeray.B0220.physMeasure ε c) g) hmp
  have h2 : ∀ᵐ y ∂UnforcedLeray.B0220.physMeasure ε c,
      (cplx3.compLpL 2 (UnforcedLeray.B0220.physMeasure ε c) g : Space × ℝ → _) y =
        cplx3 ((g : Space × ℝ → Space) y) := cplx3.coeFn_compLpL g
  have h3 := hmp.quasiMeasurePreserving.ae h2
  have he : toX hP g = Lp.compMeasurePreserving (UnforcedLeray.B0223.toCell P) hmp
      (cplx3.compLpL 2 (UnforcedLeray.B0220.physMeasure ε c) g) := rfl
  filter_upwards [h1, h3] with w hw1 hw3
  rw [he, hw1, Function.comp_apply, hw3]

/-! ## The Cartesian projected free resolvent -/

/-- **The Cartesian projected free resolvent** `g ↦ (μ - A)^{-1} P_3D g` on real body forces
`g ∈ L²(dx dτ; ℝ³)` over one period (source 1355-1368, 1640-1679): `P_3D = B0226.P3D` the Cartesian
Leray projection, then the complexification, then `B0223.physRes = ∫_0^∞ e^{-μt}S_ε(t) dt`. -/
def cartRes {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hP : P = 2 * ε * c) (μ : ℂ) :
    UnforcedLeray.B0220.PhysL2 ε c →L[ℝ] UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P :=
  ((UnforcedLeray.B0223.physRes (E := UnforcedLeray.B0223.SpaceC) (P := P) hν ε μ).restrictScalars
      ℝ).comp ((toX hP).comp (UnforcedLeray.B0226.P3D ε c))

/-- The row divergence `(div M)_i = Σ_j ∂_{x_j} M_ij(x, τ)` of a tensor field in the outer
variables. -/
def cartDiv (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (y : Space × ℝ) : Space :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3,
    fderiv ℝ (fun x : Space => M (x, y.2) i j) y.1 (UnforcedLeray.coordinateVector j)

/-- **The Cartesian weak-stress inverse** `(μ - A)^{-1} P_3D div M` (source 1533-1537:
`S_μ = R_μ div` on smooth tensors; 3888-3891) of a tensor field `M(x, τ)` in the outer variables
whose divergence `div M` lies in `L²(dx dτ)` over one period (`hM`). -/
def CartStress {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hP : P = 2 * ε * c) (μ : ℂ)
    (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : MemLp (cartDiv M) 2 (UnforcedLeray.B0220.physMeasure ε c)) :
    UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P :=
  cartRes hν hP μ (hM.toLp (cartDiv M))

/-! ## Smooth Cartesian tensors and the kernel field -/

/-- **Smooth Cartesian tensors** (source 3594-3596, "we begin with smooth tensors"): a tensor field
`T(τ, z)` of the similarity variables (the argument order of `IIIa.sepW` and `NearInst.cartLift`),
each entry smooth in `(z, τ)`, `P`-periodic in `τ`, with bounded spatial support. -/
structure IsCartTest (P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  smooth : ∀ i j : Fin 3, ContDiff ℝ ∞ fun y : Space × ℝ => T y.2 y.1 i j
  periodic : ∀ (τ : ℝ) (z : Space), T (τ + P) z = T τ z
  bounded : ∃ r : ℝ, ∀ (τ : ℝ) (z : Space), T τ z ≠ 0 → ‖z‖ ≤ r

/-- A similarity-variable tensor `T(τ, z)` as a field of the outer variables, `x = z/R`:
`M(x, τ) = T(τ, R x)`.  For a chart tensor `m`, `outerField R (cartLift R c m)` is the tensor lift
`𝒩_T m = s m` (source 2683) in outer Cartesian components. -/
def outerField (R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space × ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  T y.2 (R • y.1)

/-- **The kernel field** of `sep:resolvent` (source 3611-3617) in the outer variables:
`R · (-W_μ[T])(R x, τ)` at `w = (x, τ mod P)`, `W_μ = IIIa.sepW`, with `τ ∈ (0, P]` the
representative `B0223.toCell` of the phase (`T` is `P`-periodic) and the factor `R` from
`∂_x = R ∂_z`. -/
def kernelField {P : ℝ} [Fact (0 < P)] (ν : ℝ) (μ : ℂ) (R : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (w : UnforcedLeray.B0223.PSpace P) :
    UnforcedLeray.B0223.SpaceC :=
  WithLp.toLp 2 fun i => (R : ℂ) *
    -UnforcedLeray.Short.IIIa.sepW ν μ T (R • w.1) (UnforcedLeray.B0223.toCell P w).2 i

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
