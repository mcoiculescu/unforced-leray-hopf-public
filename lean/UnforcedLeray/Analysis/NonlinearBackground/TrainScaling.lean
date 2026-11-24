import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Exact age and amplitude transport for the cylinder train

The manuscript obtains the small-viscosity train from a reference cylinder solution by
changing the age variable and all field amplitudes. These identities use the actual
Cartesian and temporal derivatives and can be applied to a subsequently constructed
reference solution. They make no existence assertion.
-/

noncomputable section
namespace UnforcedLeray.NonlinearBackground
open GaussianVortex

abbrev ScalarField := ℝ → Plane → ℝ

/-- Pull back the age by `γ` and multiply by `a`. -/
def ageScale (γ a : ℝ) (f : ScalarField) : ScalarField :=
  fun s z => a * f (s / γ) z

def timeD (f : ScalarField) (s : ℝ) (z : Plane) : ℝ :=
  deriv (fun t => f t z) s

def dx (f : ScalarField) (s : ℝ) (z : Plane) : ℝ := partialX (f s) z

def dy (f : ScalarField) (s : ℝ) (z : Plane) : ℝ := partialY (f s) z

def lap (f : ScalarField) (s : ℝ) (z : Plane) : ℝ :=
  partialX (partialX (f s)) z + partialY (partialY (f s)) z

@[simp] theorem ageScale_apply (γ a : ℝ) (f : ScalarField) (s : ℝ) (z : Plane) :
    ageScale γ a f s z = a * f (s / γ) z := rfl

theorem timeD_ageScale (γ a : ℝ) (f : ScalarField) (s : ℝ) (z : Plane) :
    timeD (ageScale γ a f) s z = a * γ⁻¹ * timeD f (s / γ) z := by
  unfold timeD ageScale
  have h := deriv_comp_mul_left γ⁻¹ (fun t => f t z) s
  rw [show (fun t => a * f (t / γ) z) = fun t => a * (fun q => f q z) (γ⁻¹ * t) by
    funext t; simp only [div_eq_mul_inv, mul_comm]]
  rw [deriv_const_mul_field a, h]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem dx_ageScale (γ a : ℝ) (f : ScalarField) (s : ℝ) (z : Plane) :
    dx (ageScale γ a f) s z = a * dx f (s / γ) z := by
  unfold dx partialX ageScale
  exact deriv_const_mul_field a

theorem dy_ageScale (γ a : ℝ) (f : ScalarField) (s : ℝ) (z : Plane) :
    dy (ageScale γ a f) s z = a * dy f (s / γ) z := by
  unfold dy partialY ageScale
  exact deriv_const_mul_field a

theorem lap_ageScale (γ a : ℝ) (f : ScalarField) (s : ℝ) (z : Plane) :
    lap (ageScale γ a f) s z = a * lap f (s / γ) z := by
  unfold lap ageScale
  have hx : partialX (fun w : Plane => a * f (s / γ) w) =
      fun w => a * partialX (f (s / γ)) w := by
    funext w
    exact deriv_const_mul_field a
  have hy : partialY (fun w : Plane => a * f (s / γ) w) =
      fun w => a * partialY (f (s / γ)) w := by
    funext w
    exact deriv_const_mul_field a
  rw [hx, hy]
  rw [show partialX (fun w : Plane => a * partialX (f (s / γ)) w) z =
      a * partialX (partialX (f (s / γ))) z from deriv_const_mul_field a]
  rw [show partialY (fun w : Plane => a * partialY (f (s / γ)) w) z =
      a * partialY (partialY (f (s / γ))) z from deriv_const_mul_field a]
  ring_nf

/-- The scalar drift-diffusion residual for actual Cartesian derivatives. -/
def scalarResidual (ν : ℝ) (u₁ u₂ F : ScalarField) (s : ℝ) (z : Plane) : ℝ :=
  timeD F s z + u₁ s z * dx F s z + u₂ s z * dy F s z - ν * lap F s z

/-- Age-scaled meridional velocity at viscosity `h`. -/
def trainVelocity (γ : ℝ) (u : ScalarField) : ScalarField := ageScale γ γ⁻¹ u

/-- Age-scaled pressure. -/
def trainPressure (γ : ℝ) (p : ScalarField) : ScalarField := ageScale γ (γ⁻¹ ^ 2) p

/-- Unit-datum scalar before tuning. -/
def trainBaseScalar (γ : ℝ) (F : ScalarField) : ScalarField := ageScale γ 1 F

/-- Tuned scalar, with reference amplitude `β`. -/
def trainTunedScalar (γ β : ℝ) (F : ScalarField) : ScalarField := ageScale γ (β * γ⁻¹) F

/-- A reference scalar solution transports exactly to the train equation. -/
theorem scalarResidual_trainBase (γ h : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ F : ScalarField) (s : ℝ) (z : Plane) :
    scalarResidual h (trainVelocity γ u₁) (trainVelocity γ u₂)
        (trainBaseScalar γ F) s z =
      γ⁻¹ * scalarResidual (γ * h) u₁ u₂ F (s / γ) z := by
  unfold scalarResidual trainVelocity trainBaseScalar
  rw [timeD_ageScale, dx_ageScale, dy_ageScale, lap_ageScale]
  simp only [ageScale_apply, one_mul]
  field_simp

/-- The tuned scalar has the reference residual multiplied by the exact factor. -/
theorem scalarResidual_trainTuned (γ h β : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ F : ScalarField) (s : ℝ) (z : Plane) :
    scalarResidual h (trainVelocity γ u₁) (trainVelocity γ u₂)
        (trainTunedScalar γ β F) s z =
      β * γ⁻¹ ^ 2 * scalarResidual (γ * h) u₁ u₂ F (s / γ) z := by
  unfold scalarResidual trainVelocity trainTunedScalar
  rw [timeD_ageScale, dx_ageScale, dy_ageScale, lap_ageScale]
  simp only [ageScale_apply]
  field_simp

/-- Exact transport of a momentum component with the x pressure derivative. -/
theorem momentumXComponent_train (γ h : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ i j : ScalarField) (s : ℝ) (z : Plane) :
    (timeD (trainVelocity γ i) s z +
      trainVelocity γ u₁ s z * dx (trainVelocity γ i) s z +
      trainVelocity γ u₂ s z * dy (trainVelocity γ i) s z -
      h * lap (trainVelocity γ i) s z +
      dx (trainPressure γ j) s z) =
      γ⁻¹ ^ 2 * (timeD i (s / γ) z + u₁ (s / γ) z * dx i (s / γ) z +
        u₂ (s / γ) z * dy i (s / γ) z - γ * h * lap i (s / γ) z +
        dx j (s / γ) z) := by
  unfold trainVelocity trainPressure
  rw [timeD_ageScale, dx_ageScale, dy_ageScale, lap_ageScale, dx_ageScale]
  simp only [ageScale_apply]
  field_simp

/-- Exact transport of a momentum component with the y pressure derivative. -/
theorem momentumYComponent_train (γ h : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ i j : ScalarField) (s : ℝ) (z : Plane) :
    (timeD (trainVelocity γ i) s z +
      trainVelocity γ u₁ s z * dx (trainVelocity γ i) s z +
      trainVelocity γ u₂ s z * dy (trainVelocity γ i) s z -
      h * lap (trainVelocity γ i) s z +
      dy (trainPressure γ j) s z) =
      γ⁻¹ ^ 2 * (timeD i (s / γ) z + u₁ (s / γ) z * dx i (s / γ) z +
        u₂ (s / γ) z * dy i (s / γ) z - γ * h * lap i (s / γ) z +
        dy j (s / γ) z) := by
  unfold trainVelocity trainPressure
  rw [timeD_ageScale, dx_ageScale, dy_ageScale, lap_ageScale, dy_ageScale]
  simp only [ageScale_apply]
  field_simp

/-- The actual two Cartesian components of the classical meridional momentum equation. -/
def momentumXResidual (ν : ℝ) (u₁ u₂ p : ScalarField) (s : ℝ) (z : Plane) : ℝ :=
  timeD u₁ s z + u₁ s z * dx u₁ s z + u₂ s z * dy u₁ s z -
    ν * lap u₁ s z + dx p s z

def momentumYResidual (ν : ℝ) (u₁ u₂ p : ScalarField) (s : ℝ) (z : Plane) : ℝ :=
  timeD u₂ s z + u₁ s z * dx u₂ s z + u₂ s z * dy u₂ s z -
    ν * lap u₂ s z + dy p s z

theorem momentumXResidual_train (γ h : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ p : ScalarField) (s : ℝ) (z : Plane) :
    momentumXResidual h (trainVelocity γ u₁) (trainVelocity γ u₂)
      (trainPressure γ p) s z =
      γ⁻¹ ^ 2 * momentumXResidual (γ * h) u₁ u₂ p (s / γ) z := by
  exact momentumXComponent_train γ h hγ u₁ u₂ u₁ p s z

theorem momentumYResidual_train (γ h : ℝ) (hγ : γ ≠ 0)
    (u₁ u₂ p : ScalarField) (s : ℝ) (z : Plane) :
    momentumYResidual h (trainVelocity γ u₁) (trainVelocity γ u₂)
      (trainPressure γ p) s z =
      γ⁻¹ ^ 2 * momentumYResidual (γ * h) u₁ u₂ p (s / γ) z := by
  exact momentumYComponent_train γ h hγ u₁ u₂ u₂ p s z

/-- The physical two-dimensional train remains divergence-free under age scaling. -/
theorem divergence_train (γ : ℝ) (u₁ u₂ : ScalarField) (s : ℝ) (z : Plane) :
    dx (trainVelocity γ u₁) s z + dy (trainVelocity γ u₂) s z =
      γ⁻¹ * (dx u₁ (s / γ) z + dy u₂ (s / γ) z) := by
  unfold trainVelocity
  rw [dx_ageScale, dy_ageScale]
  ring

/-- Classical meridional Navier–Stokes coupled to a passive scalar on
nonnegative age. This records the equations for a concrete quadruple; no
solution is introduced by the definition. Periodicity is a separate property. -/
structure ClassicalMeridionalSystem (ν : ℝ) (u₁ u₂ p F : ScalarField) : Prop where
  momentum_x : ∀ s z, 0 ≤ s → momentumXResidual ν u₁ u₂ p s z = 0
  momentum_y : ∀ s z, 0 ≤ s → momentumYResidual ν u₁ u₂ p s z = 0
  divergence_free : ∀ s z, 0 ≤ s → dx u₁ s z + dy u₂ s z = 0
  passive_scalar : ∀ s z, 0 ≤ s → scalarResidual ν u₁ u₂ F s z = 0

/-- A proved reference solution at viscosity `γ h` yields the exact train PDE
at viscosity `h`, including the tuned scalar. The existence of that reference
solution is a distinct mathematical obligation. -/
theorem ClassicalMeridionalSystem.train
    {γ h β : ℝ} (hγ : 0 < γ) {u₁ u₂ p F : ScalarField}
    (href : ClassicalMeridionalSystem (γ * h) u₁ u₂ p F) :
    ClassicalMeridionalSystem h
      (trainVelocity γ u₁) (trainVelocity γ u₂)
      (trainPressure γ p) (trainTunedScalar γ β F) := by
  constructor
  · intro s z hs
    rw [momentumXResidual_train γ h hγ.ne']
    rw [href.momentum_x (s / γ) z (div_nonneg hs hγ.le)]
    simp
  · intro s z hs
    rw [momentumYResidual_train γ h hγ.ne']
    rw [href.momentum_y (s / γ) z (div_nonneg hs hγ.le)]
    simp
  · intro s z hs
    rw [divergence_train]
    rw [href.divergence_free (s / γ) z (div_nonneg hs hγ.le)]
    simp
  · intro s z hs
    rw [scalarResidual_trainTuned γ h β hγ.ne']
    rw [href.passive_scalar (s / γ) z (div_nonneg hs hγ.le)]
    simp

end UnforcedLeray.NonlinearBackground
