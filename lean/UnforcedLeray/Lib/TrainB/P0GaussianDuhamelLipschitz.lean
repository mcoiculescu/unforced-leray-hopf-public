import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelGenericBound

/-!
# Difference bounds for the actual nonlinear stress and Duhamel term

The tensor map is bilinear, so its diagonal is locally Lipschitz on bounded H³ sets. The Gaussian
Duhamel estimate then transfers this bound to the actual projected nonlinear integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.TrainB

/-- Bilinear polarization identity for the difference of the actual row-oriented stresses. -/
theorem tensorH3Bilinear_diagonal_sub {c : ℝ} (hc1 : 1 ≤ c)
    (u v : VectorH3 c) :
    tensorH3Bilinear hc1 u u - tensorH3Bilinear hc1 v v =
      tensorH3Bilinear hc1 (u - v) u + tensorH3Bilinear hc1 v (u - v) := by
  calc
    tensorH3Bilinear hc1 u u - tensorH3Bilinear hc1 v v =
        (tensorH3Bilinear hc1 u u - tensorH3Bilinear hc1 v u) +
          (tensorH3Bilinear hc1 v u - tensorH3Bilinear hc1 v v) := by abel
    _ = tensorH3Bilinear hc1 (u - v) u + tensorH3Bilinear hc1 v (u - v) := by
      have h₁ : tensorH3Bilinear hc1 (u - v) u =
          tensorH3Bilinear hc1 u u - tensorH3Bilinear hc1 v u := by
        rw [map_sub]
        rfl
      have h₂ : tensorH3Bilinear hc1 v (u - v) =
          tensorH3Bilinear hc1 v u - tensorH3Bilinear hc1 v v := by
        rw [map_sub]
      rw [h₁, h₂]

/-- Uniform bilinear Lipschitz estimate for the diagonal stress on a bounded pair. -/
theorem norm_tensorH3Bilinear_diagonal_sub_le {c : ℝ} (hc1 : 1 ≤ c)
    (u v : VectorH3 c) :
    ‖tensorH3Bilinear hc1 u u - tensorH3Bilinear hc1 v v‖ ≤
      1536 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [tensorH3Bilinear_diagonal_sub hc1 u v]
  calc
    ‖tensorH3Bilinear hc1 (u - v) u + tensorH3Bilinear hc1 v (u - v)‖ ≤
        ‖tensorH3Bilinear hc1 (u - v) u‖ +
          ‖tensorH3Bilinear hc1 v (u - v)‖ := norm_add_le _ _
    _ ≤ 1536 * ‖u - v‖ * ‖u‖ + 1536 * ‖v‖ * ‖u - v‖ :=
      add_le_add (norm_tensorH3Bilinear_apply_le hc1 _ _)
        (norm_tensorH3Bilinear_apply_le hc1 _ _)
    _ = 1536 * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- Continuous path of stress differences, for two actual velocity paths. -/
def tensorH3StressDifferencePath {c : ℝ} (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c)) : ContinuousMap ℝ (TensorH3 c) where
  toFun r := tensorH3Bilinear hc1 (u r) (u r) - tensorH3Bilinear hc1 (v r) (v r)
  continuous_toFun := by
    have hu := (tensorH3StressPath hc1 u).continuous
    have hv := (tensorH3StressPath hc1 v).continuous
    exact hu.sub hv

/-- On the time interval, the stress difference is bounded by the two trajectory radii and their
uniform distance. -/
theorem norm_tensorH3StressDifferencePath_le {c t R δ : ℝ} (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (hR : 0 ≤ R)
    (hu : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R)
    (hv : ∀ r ∈ Ioo 0 t, ‖v r‖ ≤ R)
    (hδ : ∀ r ∈ Ioo 0 t, ‖u r - v r‖ ≤ δ) :
    ∀ r ∈ Ioo 0 t,
      ‖tensorH3StressDifferencePath hc1 u v r‖ ≤ 3072 * R * δ := by
  intro r hr
  change ‖tensorH3Bilinear hc1 (u r) (u r) -
      tensorH3Bilinear hc1 (v r) (v r)‖ ≤ _
  calc
    _ ≤ 1536 * (‖u r‖ + ‖v r‖) * ‖u r - v r‖ :=
      norm_tensorH3Bilinear_diagonal_sub_le hc1 _ _
    _ ≤ 1536 * (R + R) * ‖u r - v r‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (hu r hr) (hv r hr)) (by norm_num))
        (norm_nonneg _)
    _ ≤ 1536 * (R + R) * δ :=
      mul_le_mul_of_nonneg_left (hδ r hr) (by positivity)
    _ = 3072 * R * δ := by ring


/-- The actual projected Gaussian response is linear in its tensor path at every age. -/
theorem projectedHeatDuhamelOrbit_sub {c ν s : ℝ} (hc : 0 < c)
    (F G : TensorH3 c) (r : ℝ) :
    projectedHeatDuhamelOrbit (ν := ν) (s := s) hc (fun _ => F - G) r =
      projectedHeatDuhamelOrbit (ν := ν) (s := s) hc (fun _ => F) r -
        projectedHeatDuhamelOrbit (ν := ν) (s := s) hc (fun _ => G) r := by
  by_cases hθ : 0 < ν * (s - r)
  · simp [projectedHeatDuhamelOrbit, UnforcedLeray.HeatCylinder.actualHeatDivH3Orbit,
      hθ, map_sub]
  · simp [projectedHeatDuhamelOrbit, UnforcedLeray.HeatCylinder.actualHeatDivH3Orbit,
      hθ]

/-- The set integral of the actual projected Gaussian response is linear in its continuous
TensorH3 input path. -/
theorem projectedHeatDuhamelIntegral_sub {c ν t : ℝ} (hc : 0 < c)
    (F G : ContinuousMap ℝ (TensorH3 c))
    (hF : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F)
      (volume.restrict (Ioo 0 t)))
    (hG : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc G)
      (volume.restrict (Ioo 0 t))) :
    projectedHeatDuhamelIntegral (ν := ν) hc F t -
        projectedHeatDuhamelIntegral (ν := ν) hc G t =
      projectedHeatDuhamelIntegral (ν := ν) hc (F - G) t := by
  change (∫ r in Ioo 0 t, projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r) -
      (∫ r in Ioo 0 t, projectedHeatDuhamelOrbit (ν := ν) (s := t) hc G r) = _
  calc
    _ = ∫ r in Ioo 0 t,
        (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r -
          projectedHeatDuhamelOrbit (ν := ν) (s := t) hc G r) := by
      rw [integral_sub hF hG]
    _ = ∫ r in Ioo 0 t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc (F - G) r := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (projectedHeatDuhamelOrbit_sub hc (F r) (G r) r).symm

/-- The difference of the two actual nonlinear Duhamel terms is the Duhamel integral of the
actual stress difference. -/
theorem projectedHeatNonlinearityIntegral_sub_eq {c ν t R : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht : 0 < t) (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (hu : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R)
    (hv : ∀ r ∈ Ioo 0 t, ‖v r‖ ≤ R) :
    projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t -
        projectedHeatNonlinearityIntegral (ν := ν) hc hc1 v t =
      projectedHeatDuhamelIntegral (ν := ν) hc
        (tensorH3StressDifferencePath hc1 u v) t := by
  have hIu := integrableOn_projectedHeatNonlinearity hc hν (by linarith) hc1 u hu
  have hIv := integrableOn_projectedHeatNonlinearity hc hν (by linarith) hc1 v hv
  have hpath : tensorH3StressDifferencePath hc1 u v =
      tensorH3StressPath hc1 u - tensorH3StressPath hc1 v := by
    ext r
    rfl
  change projectedHeatDuhamelIntegral (ν := ν) hc (tensorH3StressPath hc1 u) t -
      projectedHeatDuhamelIntegral (ν := ν) hc (tensorH3StressPath hc1 v) t = _
  rw [projectedHeatDuhamelIntegral_sub hc _ _ hIu hIv, hpath]

/-- The actual nonlinear Duhamel operator is Lipschitz on a bounded H³ ball, with explicit
square-root time factor. -/
theorem norm_projectedHeatNonlinearityIntegral_sub_le {c ν t R δ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht : 0 < t) (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (hR : 0 ≤ R)
    (hu : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R)
    (hv : ∀ r ∈ Ioo 0 t, ‖v r‖ ≤ R)
    (hδ : ∀ r ∈ Ioo 0 t, ‖u r - v r‖ ≤ δ) :
    ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t -
        projectedHeatNonlinearityIntegral (ν := ν) hc hc1 v t‖ ≤
      ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
  rw [projectedHeatNonlinearityIntegral_sub_eq hc hν ht hc1 u v hu hv]
  have hstress : ∀ r ∈ Ioo 0 t,
      ‖tensorH3StressDifferencePath hc1 u v r‖ ≤ 3072 * R * δ := by
    exact norm_tensorH3StressDifferencePath_le hc1 u v hR hu hv hδ
  have hbound := norm_projectedHeatDuhamelIntegral_le hc hν ht
    (tensorH3StressDifferencePath hc1 u v) hstress
  calc
    ‖projectedHeatDuhamelIntegral (ν := ν) hc
        (tensorH3StressDifferencePath hc1 u v) t‖ ≤
        ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := hbound
    _ = ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := rfl

/-- The Duhamel integral of the stress difference is bounded by the H³ trajectory distance. -/
theorem norm_projectedHeatDuhamelIntegral_stressDifference_le {c ν t R δ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht : 0 < t) (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (hR : 0 ≤ R)
    (hu : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R)
    (hv : ∀ r ∈ Ioo 0 t, ‖v r‖ ≤ R)
    (hδ : ∀ r ∈ Ioo 0 t, ‖u r - v r‖ ≤ δ) :
    ‖projectedHeatDuhamelIntegral (ν := ν) hc
      (tensorH3StressDifferencePath hc1 u v) t‖ ≤
      ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
  apply norm_projectedHeatDuhamelIntegral_le hc hν ht
  exact norm_tensorH3StressDifferencePath_le hc1 u v hR hu hv hδ

#print axioms UnforcedLeray.TrainB.tensorH3Bilinear_diagonal_sub
#print axioms UnforcedLeray.TrainB.norm_tensorH3Bilinear_diagonal_sub_le
#print axioms UnforcedLeray.TrainB.norm_projectedHeatDuhamelIntegral_stressDifference_le
#print axioms UnforcedLeray.TrainB.projectedHeatDuhamelIntegral_sub
#print axioms UnforcedLeray.TrainB.norm_projectedHeatNonlinearityIntegral_sub_le

end UnforcedLeray.TrainB
