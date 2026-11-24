import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.KBound
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.TrainBounds
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.TestBounds
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F4

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CCP

open UnforcedLeray

/-- The integrand is `w a_r - K_0 w ψ_0 - K_1 w ψ_1`. -/
theorem integrand_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (ω : B0579.Plane → ℝ) (r : ℝ)
    (φ : B0579.Plane → ℝ) (x : B0579.Plane) :
    cylCoupledIntegrand tr ω r φ x =
      ω x * (ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x) +
        (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)) -
      Cyl.K c ω x 0 * (φ x * B0579.pd 0 (B0238.Ec tr r) x) -
      Cyl.K c ω x 1 * (φ x * B0579.pd 1 (B0238.Ec tr r) x) := by
  simp only [cylCoupledIntegrand, cylFreeIntegrand, cylAc, lapP]
  ring

theorem continuous_train_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (i : Fin 2) : Continuous fun x : B0579.Plane => tr.v r x i := by
  have h : Continuous fun y : B0579.Plane => tr.v r y :=
    (tr.isTrain.smooth_v.continuousOn.comp_continuous
      (f := fun y : B0579.Plane => ((r, y) : ℝ × B0579.Plane)) (by fun_prop)
      (fun y => ⟨hr, mem_univ _⟩))
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp h

theorem measurable_pd_Ec {ν c : ℝ} (tr : B0140.TrainSol ν c) (r : ℝ) (j : Fin 2) :
    Measurable (B0579.pd j (B0238.Ec tr r)) :=
  measurable_fderiv_apply_const ℝ (B0238.Ec tr r) (B0579.dir j)

end UnforcedLeray.Short.IIb.CCP
