import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6

/-!
# Decomposition of `SepX0Comb` (`ward:shifted-resolvent`, source 4199-4200, 5223, 3800-3807)

Source `the November 2 reference manuscript`.
`X₀ = Re (kerInt Kd)` (3611-3626, 4171-4174), `Kd(0) = 0` so differentiating the convolution in `τ`
has no instantaneous term, and `D_{μ+1} = ∂_τ - ½y·∇ - νΔ + (μ+½)` acts under the integral:
the integrand becomes `KdOp = ∂_hKd - L Kd + (μ+½)Kd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∂_h Kd`. -/
def kdDh (ν μ : ℝ) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  deriv (fun h' => Kd ν μ h' y z i j k) h

/-- `y·∇_y Kd`. -/
def kdYGrad (ν μ : ℝ) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  fderiv ℝ (fun y' => Kd ν μ h y' z i j k) y y

/-- `∂_l∂_l Kd` (second derivative in the `y`-direction `e_l`). -/
def kdLap (ν μ : ℝ) (l : Fin 3) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y'
    (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l)

/-- Data of a separated source (as in `SepX0Comb`). -/
def SepData (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  0 < ν ∧ -(1 / 4) < μ ∧ 0 ≤ rOut ∧ 0 < P ∧ IIIa.IsSepSource P rOut T ∧ SepMoment P T

/-- **(S1)** `X₀ = Re kerInt Kd` off the old disk (`sepWHRep` for `m = μ, μ+1` and linearity of the
integral; integrability from `SepMoment` and the kernel bounds, cf. `sepWSmoothOn_of`). -/
def SepX0KerInt : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      sepX0 ν μ T τ y = WithLp.toLp 2 fun i => (kerInt T (Kd ν μ) τ y i).re

/-- **(S2)** `τ`-derivative under the integral (`Kd(0) = 0`, `Kd` Lipschitz in `h` with an
integrable envelope; the difference quotient of the extended `Kd` is dominated, `T ∈ L²_τ`). -/
def SepX0TauDeriv : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      HasDerivAt (fun t => sepX0 ν μ T t y)
        (WithLp.toLp 2 fun i => (kerInt T (kdDh ν μ) τ y i).re) τ

/-- **(S3a)** `y·∇_y` under the integral (kernel smooth in `y` off the source disk). -/
def SepX0YGrad : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      fderiv ℝ (sepX0 ν μ T τ) y y = WithLp.toLp 2 fun i => (kerInt T (kdYGrad ν μ) τ y i).re

/-- **(S3b)** the second derivatives `∂_l∂_l` under the integral. -/
def SepX0Lap : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ l : Fin 3,
      fderiv ℝ (fun y' => fderiv ℝ (sepX0 ν μ T τ) y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l) =
      WithLp.toLp 2 fun i => (kerInt T (kdLap ν μ l) τ y i).re

/-- **(S4)** linearity of `kerInt` over `KdOp = ∂_hKd - ½y·∇Kd - νΣ∂_l²Kd + (μ+½)Kd`
(the six integrands are integrable on `Ioi 0 × ℝ³`; they are dominated like `Kd` itself). -/
def KdOpSplit : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
      kerInt T (KdOp ν μ) τ y i =
        kerInt T (kdDh ν μ) τ y i - (1 / 2 : ℂ) * kerInt T (kdYGrad ν μ) τ y i
          - (ν : ℂ) * ∑ l : Fin 3, kerInt T (kdLap ν μ l) τ y i
          + ((μ : ℂ) + 1 / 2) * kerInt T (Kd ν μ) τ y i

theorem sepX0Comb_of (h1 : SepX0KerInt) (h2 : SepX0TauDeriv) (h3 : SepX0YGrad) (h4 : SepX0Lap)
    (h5 : KdOpSplit) : SepX0Comb := by
  intro ν μ rOut P hν hμ hr hP T hT hM τ y hy i
  have hd : SepData ν μ rOut P T := ⟨hν, hμ, hr, hP, hT, hM⟩
  have e1 := h1 ν μ rOut P T hd τ y hy
  have e2 := (h2 ν μ rOut P T hd τ y hy).deriv
  have e3 := h3 ν μ rOut P T hd τ y hy
  have e4 := fun l => h4 ν μ rOut P T hd τ y hy l
  have e5 := h5 ν μ rOut P T hd τ y hy i
  rw [e5]
  simp only [physDmu, physLap, physPd2, physPd, e2, e3, e4, e1]
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_sum]
  left; ring

end UnforcedLeray.Short.PartIIIb.Concrete
