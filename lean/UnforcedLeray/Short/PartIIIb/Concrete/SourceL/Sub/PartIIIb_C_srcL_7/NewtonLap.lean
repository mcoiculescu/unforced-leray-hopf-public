import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Lib.Kernels.NewtonDerivatives
import UnforcedLeray.Units.B0635

/-!
# `NewtonLap`: the Newton kernel is harmonic off `0` (task `PartIII-b:C/srcL/7/7`)

Source of record: `the November 2 reference manuscript`, lines 4797-4800
(`ΔN = 0` off `0`, `N = 1/(4π|x|)`).

Route (transfer): `newtonN = newtonPotential ∘ euAeq`, where `euAeq : ℝ³ ≃L EuclideanSpace` is the
coordinate identification.  Composition with a continuous linear equivalence commutes with `fderiv`
without hypotheses (`ContinuousLinearEquiv.comp_right_fderiv`), so each inner directional
derivative is a Euclidean second derivative of `newtonPotential`.  The Euclidean Hessian is the
explicit formula `euHess'` (the proof of `UnforcedLeray.Kernels.newton_second_formula'`, copied
because `Lib/Kernels/NewtonJets.lean` does not compile to an olean), and the coordinate sum is zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Euclidean Hessian of `N` off the origin, in arbitrary directions. -/
theorem euHess' {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) (u v : EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℝ 2 UnforcedLeray.PressureAnalysis.newtonPotential x ![u, v] =
      (3 * inner ℝ x u * inner ℝ x v - ‖x‖ ^ 2 * inner ℝ u v) / (4 * Real.pi * ‖x‖ ^ 5) := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [UnforcedLeray.B0635.iteratedFDeriv_eq_nestedDeriv
    (f := UnforcedLeray.PressureAnalysis.newtonPotential)
    (fun y hy => UnforcedLeray.Kernels.contDiffAt_newton hy) 2 _ x hx]
  show fderiv ℝ (fun y => fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential y v) x u = _
  have hev : (fun y => fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential y v) =ᶠ[𝓝 x]
      fun z => (-(4 * Real.pi)⁻¹ * (innerSL ℝ v) z) * ‖z‖⁻¹ ^ 3 := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    rw [UnforcedLeray.PressureAnalysis.fderiv_newtonPotential_apply hz]
    simp only [innerSL_apply_apply, real_inner_comm v z]
    field_simp
  rw [hev.fderiv_eq]
  have h := UnforcedLeray.B0635.hasFDerivAt_mul_invNorm_pow hx
    (((innerSL ℝ v).hasFDerivAt).const_mul (-(4 * Real.pi)⁻¹)) 3
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, inv_pow]
  rw [real_inner_comm v u, real_inner_comm v x, real_inner_comm u x]
  field_simp
  ring

/-- The coordinate sum of the Euclidean Hessian vanishes off the origin. -/
theorem euLap {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ∑ i, iteratedFDeriv ℝ 2 UnforcedLeray.PressureAnalysis.newtonPotential x
      ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector i] = 0 := by
  have hsq : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hsq' : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [hsq, Fin.sum_univ_three]
  have hii : ∀ i : Fin 3, inner ℝ (UnforcedLeray.coordinateVector i)
      (UnforcedLeray.coordinateVector i) = 1 := fun i => by
    rw [UnforcedLeray.B0635.inner_coordinateVector]
    simp [UnforcedLeray.coordinateVector]
  have hterm : ∀ i : Fin 3,
      iteratedFDeriv ℝ 2 UnforcedLeray.PressureAnalysis.newtonPotential x
        ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector i] =
        (3 * x i * x i - ‖x‖ ^ 2 * 1) / (4 * Real.pi * ‖x‖ ^ 5) := by
    intro i
    rw [euHess' hx, UnforcedLeray.B0635.inner_coordinateVector, hii i]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]
  apply div_eq_zero_iff.mpr
  left
  rw [Fin.sum_univ_three, hsq']
  ring

/-- The coordinate identification `ℝ³ ≃L EuclideanSpace ℝ (Fin 3)` (same coordinates). -/
def euAeq : Vec3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm

theorem euAeq_single (i : Fin 3) :
    euAeq (Pi.single i 1) = UnforcedLeray.coordinateVector i := by
  ext j
  simp [euAeq, UnforcedLeray.coordinateVector, EuclideanSpace.single_apply, Pi.single_apply]

theorem euAeq_ne_zero {w : Vec3} (hw : w ≠ 0) : euAeq w ≠ 0 := by
  intro h
  apply hw
  have := congrArg euAeq.symm h
  simpa using this

theorem norm_euAeq (z : Vec3) : ‖euAeq z‖ = Real.sqrt (∑ i, z i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  rfl

theorem newtonN_eq_pot (z : Vec3) :
    newtonN z = UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z) := by
  unfold newtonN UnforcedLeray.PressureAnalysis.newtonPotential
  rw [norm_euAeq]

theorem newtonLap : NewtonLap := by
  intro w hw
  have hfun : ∀ i : Fin 3, (fun z : Vec3 => fderiv ℝ newtonN z (Pi.single i 1)) =
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential y
          (UnforcedLeray.coordinateVector i)) ∘ euAeq := by
    intro i
    funext z
    have hN : newtonN = fun z => UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z) :=
      funext newtonN_eq_pot
    have hd : fderiv ℝ newtonN z =
        (fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z)).comp
          (euAeq : Vec3 →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
      rw [hN]
      exact ContinuousLinearEquiv.comp_right_fderiv
        (f := UnforcedLeray.PressureAnalysis.newtonPotential) (iso := euAeq)
    show fderiv ℝ newtonN z (Pi.single i 1) = _
    rw [hd]
    show fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z)
      (euAeq (Pi.single i 1)) = _
    rw [euAeq_single i]
    rfl
  have hterm : ∀ i : Fin 3,
      fderiv ℝ (fun z : Vec3 => fderiv ℝ newtonN z (Pi.single i 1)) w (Pi.single i 1) =
        iteratedFDeriv ℝ 2 UnforcedLeray.PressureAnalysis.newtonPotential (euAeq w)
          ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector i] := by
    intro i
    rw [hfun i, ContinuousLinearEquiv.comp_right_fderiv]
    show fderiv ℝ _ (euAeq w) (euAeq (Pi.single i 1)) = _
    rw [euAeq_single i,
      UnforcedLeray.B0635.iteratedFDeriv_eq_nestedDeriv
        (f := UnforcedLeray.PressureAnalysis.newtonPotential)
        (fun y hy => UnforcedLeray.Kernels.contDiffAt_newton hy) 2 _ (euAeq w) (euAeq_ne_zero hw)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact euLap (euAeq_ne_zero hw)

end UnforcedLeray.Short.PartIIIb.Concrete
