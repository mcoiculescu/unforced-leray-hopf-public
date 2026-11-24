import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianAverageIdentification
import UnforcedLeray.Lib.HeatCylinder.HeatVecCenteredSemigroup

/-!
# Self-adjointness of actual centered-cell vector heat

The positive-age result is proved from the actual B0284 kernel representation as a Gaussian
average of actual cylinder translations. Evenness of the Gaussian and the inverse translation
group law give symmetry on every centered L² class.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- The actual centered planar translation has adjoint the translation by the opposite shift. -/
private theorem inner_planeShiftL2CLM_adjoint {c : ℝ} (hc : 0 < c) (w : Plane)
    (x y : L2v c) :
    inner ℝ (planeShiftL2CLM hc w x) y =
      inner ℝ x (planeShiftL2CLM hc (-w) y) := by
  change inner ℝ
      (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)) y = _
  have hinvq : UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
      (UnforcedLeray.TrainB.qShiftL2 hc w.1 y) = y := by
    exact UnforcedLeray.TrainB.qShiftL2_neg_comp hc y
  have hinve : UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
      (UnforcedLeray.TrainB.etaShiftL2 c w.2
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) =
      UnforcedLeray.TrainB.qShiftL2 hc w.1 y := by
    exact UnforcedLeray.TrainB.etaShiftL2_neg_comp
      (c := c) (a := w.2) (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)
  have hq := (UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).inner_map_map
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
    (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)
  have heta := (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).inner_map_map x
    (UnforcedLeray.TrainB.etaShiftL2 c w.2
      (UnforcedLeray.TrainB.qShiftL2 hc w.1 y))
  have hcomm := UnforcedLeray.HeatCylinder.qShiftL2_etaShiftL2_comm hc
    (a := w.1) (b := w.2) y
  calc
    inner ℝ (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)) y =
      inner ℝ (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x))
        (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
          (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) := by rw [hinvq]
    _ = inner ℝ (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y) := hq
    _ = inner ℝ (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
          (UnforcedLeray.TrainB.etaShiftL2 c w.2
            (UnforcedLeray.TrainB.qShiftL2 hc w.1 y))) := by rw [hinve]
    _ = inner ℝ x (UnforcedLeray.TrainB.etaShiftL2 c w.2
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) := heta
    _ = inner ℝ x (UnforcedLeray.TrainB.qShiftL2 hc w.1
        (UnforcedLeray.TrainB.etaShiftL2 c w.2 y)) := by rw [← hcomm]
    _ = inner ℝ x (planeShiftL2CLM hc (-w) y) := by
      rw [planeShiftL2CLM_apply]
      simp [planeShiftL2]

private theorem integrable_heatKernel_inner_planeShiftCLM {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x y : L2v c) :
    Integrable (fun w : Plane =>
      heatKernel2 θ w * inner ℝ (planeShiftL2CLM hc w x) y) := by
  have hK : Integrable (heatKernel2 θ) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hs := continuous_planeShiftL2_orbit hc x
  have hcont : Continuous (fun w : Plane => inner ℝ (planeShiftL2CLM hc w x) y) := by
    exact continuous_inner.comp (hs.prodMk continuous_const)
  have hbound : ∀ w : Plane,
      ‖inner ℝ (planeShiftL2CLM hc w x) y‖ ≤ ‖x‖ * ‖y‖ := by
    intro w
    calc
      ‖inner ℝ (planeShiftL2CLM hc w x) y‖ ≤
          ‖planeShiftL2CLM hc w x‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by
        change ‖UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)
          (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)‖ * ‖y‖ = _
        rw [(UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).norm_map,
          (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).norm_map]
  have hmul := hK.bdd_mul hcont.aestronglyMeasurable
    (c := ‖x‖ * ‖y‖) (Filter.Eventually.of_forall hbound)
  exact hmul.congr (Filter.Eventually.of_forall fun w => by ring)

/-- The actual centered Gaussian translation average is self-adjoint on vector L². -/
theorem inner_centeredGaussianShiftAverageCLM_symm {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x y : L2v c) :
    inner ℝ (centeredGaussianShiftAverageCLM hc hθ x) y =
      inner ℝ x (centeredGaussianShiftAverageCLM hc hθ y) := by
  have hK : ∀ w : Plane, heatKernel2 θ (-w) = heatKernel2 θ w := by
    intro w
    simp [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0191.heatKernel]
  have hi : Integrable (fun w : Plane =>
      heatKernel2 θ w * inner ℝ (planeShiftL2CLM hc w y) x) :=
    integrable_heatKernel_inner_planeShiftCLM hc hθ y x
  calc
    inner ℝ (centeredGaussianShiftAverageCLM hc hθ x) y =
        ∫ w : Plane, heatKernel2 θ w *
          inner ℝ (planeShiftL2CLM hc w x) y :=
      inner_centeredGaussianShiftAverageCLM hc hθ x y
    _ = ∫ w : Plane, heatKernel2 θ w *
        inner ℝ x (planeShiftL2CLM hc (-w) y) := by
          apply integral_congr_ae
          filter_upwards [] with w
          rw [inner_planeShiftL2CLM_adjoint hc w x y]
    _ = ∫ w : Plane,
        (fun v : Plane => heatKernel2 θ v * inner ℝ (planeShiftL2CLM hc v y) x) (-w) := by
          apply integral_congr_ae
          filter_upwards [] with w
          rw [hK w, real_inner_comm]
    _ = ∫ w : Plane,
        heatKernel2 θ w * inner ℝ (planeShiftL2CLM hc w y) x :=
      by
        exact integral_neg_eq_self
          (fun w : Plane => heatKernel2 θ w *
            inner ℝ (planeShiftL2CLM hc w y) x) volume
    _ = inner ℝ (centeredGaussianShiftAverageCLM hc hθ y) x :=
      (inner_centeredGaussianShiftAverageCLM hc hθ y x).symm
    _ = inner ℝ x (centeredGaussianShiftAverageCLM hc hθ y) :=
      real_inner_comm _ _

/-- The actual centered B0284 heat CLM is self-adjoint for every nonnegative age. At age zero the
operator is the identity; at positive age the proof uses its literal Gaussian shift-average. -/
theorem inner_centeredHeatVecL2CLM_symm {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 ≤ θ) (x y : L2v c) :
    inner ℝ (centeredHeatVecL2CLM hc θ x) y =
      inner ℝ x (centeredHeatVecL2CLM hc θ y) := by
  by_cases hθ0 : θ ≤ 0
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc hθ0]
    simp
  · have hθ' : 0 < θ := lt_of_not_ge hθ0
    rw [centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM hc hθ' x,
      centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM hc hθ' y]
    exact inner_centeredGaussianShiftAverageCLM_symm hc hθ' x y

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.inner_centeredGaussianShiftAverageCLM_symm
#print axioms UnforcedLeray.HeatCylinder.inner_centeredHeatVecL2CLM_symm
