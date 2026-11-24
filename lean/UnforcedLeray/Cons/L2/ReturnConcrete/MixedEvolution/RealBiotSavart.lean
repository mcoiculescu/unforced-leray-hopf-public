import UnforcedLeray.Units.B0583
import UnforcedLeray.Units.B0610
import UnforcedLeray.Lib.Train.Ops

/-!
# Real projection of the cylinder Biot–Savart reconstruction

B0583 constructs the cylinder Biot–Savart velocity in complex-valued `L²`, while the actual
Gaussian train and the mixed vorticity equation use real meridional vectors. This file begins
that bridge by defining the componentwise real-part map and its induced `L²` map. Taking real
parts is bounded even before proving that the complex output is itself real-valued.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0581 (Vel cellVol)
open UnforcedLeray.Train (Vec)

/-- Componentwise real part from complex Euclidean velocity vectors to real meridional vectors. -/
def realPartVelocityCLM : Vel →L[ℝ] Vec :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 =>
      Complex.reCLM.comp
        ((EuclideanSpace.proj (𝕜 := ℂ) i : Vel →L[ℂ] ℂ).restrictScalars ℝ))

theorem realPartVelocityCLM_apply (u : Vel) (i : Fin 2) :
    realPartVelocityCLM u i = (u i).re := by
  simp [realPartVelocityCLM]

/-- The pointwise real-part projection is contractive in the Euclidean vector norm. -/
theorem norm_realPartVelocityCLM_le (u : Vel) :
    ‖realPartVelocityCLM u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [realPartVelocityCLM_apply, Real.norm_eq_abs, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (u 0).im, sq_nonneg (u 1).im]

/-- The componentwise real-part map has operator norm at most one. -/
theorem opNorm_realPartVelocityCLM_le_one : ‖realPartVelocityCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  simpa using norm_realPartVelocityCLM_le u

/-- The real-part image of B0583's complex cylinder velocity in unweighted cell `L²`. -/
def realPartVelocityLp {c : ℝ} (u : MeasureTheory.Lp Vel 2 (cellVol c)) :
    MeasureTheory.Lp Vec 2 (cellVol c) :=
  realPartVelocityCLM.compLpL 2 (cellVol c) u

/-- The induced real-part projection is contractive on cylinder `L²`. -/
theorem norm_realPartVelocityLp_le {c : ℝ} (u : MeasureTheory.Lp Vel 2 (cellVol c)) :
    ‖realPartVelocityLp u‖ ≤ ‖u‖ := by
  let L : MeasureTheory.Lp Vel 2 (cellVol c) →L[ℝ]
      MeasureTheory.Lp Vec 2 (cellVol c) :=
    realPartVelocityCLM.compLpL 2 (cellVol c)
  have hmap : ‖L‖ ≤ 1 := by
    dsimp [L]
    exact (ContinuousLinearMap.norm_compLpL_le _).trans opNorm_realPartVelocityCLM_le_one
  change ‖L u‖ ≤ ‖u‖
  calc ‖L u‖
      ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hmap (norm_nonneg _)
    _ = ‖u‖ := one_mul _

/-- The value of the real-part velocity is componentwise the real part almost everywhere. -/
theorem coeFn_realPartVelocityLp {c : ℝ} (u : MeasureTheory.Lp Vel 2 (cellVol c)) :
    realPartVelocityLp u =ᵐ[cellVol c] fun x => realPartVelocityCLM (u x) := by
  simpa [realPartVelocityLp] using
    realPartVelocityCLM.coeFn_compLpL (p := 2) (μ := cellVol c) u

/-- The real-valued componentwise weak derivative predicate on the cylinder cell. -/
def HasWeakRealVelDeriv {c : ℝ} (j : Fin 2)
    (u g : MeasureTheory.Lp Vec 2 (cellVol c)) : Prop :=
  ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest c φ → ∀ i : Fin 2,
    ∫ x, B0579.pd j φ x * (u x : Vec) i ∂cellVol c =
      -∫ x, φ x * (g x : Vec) i ∂cellVol c

/-- Taking componentwise real parts transports B0583's complex weak derivative identity to the
real train-vector spaces. The tests are real-valued, so taking `Complex.re` commutes with each
tested product and integral. -/
theorem realPart_preserves_weak_deriv {c : ℝ} (j : Fin 2)
    (u g : MeasureTheory.Lp Vel 2 (cellVol c))
    (hweak : UnforcedLeray.B0583.HasWeakVelDeriv c j u g) :
    HasWeakRealVelDeriv j (realPartVelocityLp u) (realPartVelocityLp g) := by
  intro φ hφ i
  let f : B0579.Plane → ℂ := fun x =>
    ((B0579.pd j φ x : ℝ) : ℂ) * (u x : Vel) i
  let gfun : B0579.Plane → ℂ := fun x =>
    ((φ x : ℝ) : ℂ) * (g x : Vel) i
  have hf : Integrable f (cellVol c) := by
    exact UnforcedLeray.B0583.integrable_testLp_mul c (hφ.pd j) i u
  have hgf : Integrable gfun (cellVol c) := by
    exact UnforcedLeray.B0583.integrable_testLp_mul c hφ i g
  have hu := coeFn_realPartVelocityLp u
  have hg := coeFn_realPartVelocityLp g
  have heqf : (fun x => B0579.pd j φ x * (realPartVelocityLp u x : Vec) i) =ᵐ[cellVol c]
      fun x => (f x).re := by
    filter_upwards [hu] with x hx
    rw [hx]
    simp [f, realPartVelocityCLM_apply]
  have heqg : (fun x => φ x * (realPartVelocityLp g x : Vec) i) =ᵐ[cellVol c]
      fun x => (gfun x).re := by
    filter_upwards [hg] with x hx
    rw [hx]
    simp [gfun, realPartVelocityCLM_apply]
  calc ∫ x, B0579.pd j φ x * (realPartVelocityLp u x : Vec) i ∂cellVol c
      = (∫ x, f x ∂cellVol c).re := by
          rw [integral_congr_ae heqf]
          exact integral_re hf
    _ = (-(∫ x, gfun x ∂cellVol c)).re := by rw [hweak φ hφ i]
    _ = -(∫ x, gfun x ∂cellVol c).re := by simp
    _ = -∫ x, (gfun x).re ∂cellVol c := by
          congr 1
          exact (integral_re hgf).symm
    _ = -∫ x, φ x * (realPartVelocityLp g x : Vec) i ∂cellVol c := by
          rw [integral_congr_ae heqg]

/-- The real meridional cylinder velocity obtained from B0583's actual Biot–Savart reconstruction
of a real weighted vorticity. This is the real-part projection of the concrete Fourier/zero-mode
formula, not an abstract velocity parameter. -/
def realBiotSavart {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    MeasureTheory.Lp Vec 2 (cellVol c) :=
  realPartVelocityLp (UnforcedLeray.B0583.velocity c hm ω hcirc)

/-- Real weak derivatives of the actual B0583 Biot–Savart velocity. -/
theorem realBiotSavart_hasWeakDerivs {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    HasWeakRealVelDeriv 0 (realBiotSavart hm ω hcirc)
        (realPartVelocityLp (UnforcedLeray.B0583.velGradQ c hm ω)) ∧
      HasWeakRealVelDeriv 1 (realBiotSavart hm ω hcirc)
        (realPartVelocityLp (UnforcedLeray.B0583.velGradEta c hm ω hcirc)) := by
  constructor
  · exact realPart_preserves_weak_deriv 0 _ _
      (UnforcedLeray.B0583.hasWeakVelDeriv_velocity_q c hm ω hcirc)
  · exact realPart_preserves_weak_deriv 1 _ _
      (UnforcedLeray.B0583.hasWeakVelDeriv_velocity_eta c hm ω hcirc)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
