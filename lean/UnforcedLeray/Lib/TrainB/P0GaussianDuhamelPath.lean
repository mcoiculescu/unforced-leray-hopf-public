import UnforcedLeray.Lib.TrainB.P0GaussianBilinear
import UnforcedLeray.Lib.HeatCylinder.H3RoughOrbitContinuity
import UnforcedLeray.Lib.HeatCylinder.OrbitBounds

/-!
# Continuity of the actual projected Gaussian response along a tensor path

Positive-age continuity of the actual Gaussian H³ operator and its locally uniform singular
bound imply continuity when both the age and the tensor input vary. This is the measurability gate
for the H³-valued nonlinear Duhamel integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual projected heat-divergence response along a time-varying tensor H³ path. -/
def projectedHeatDuhamelOrbit {c ν s : ℝ} (hc : 0 < c)
    (F : ℝ → TensorH3 c) (r : ℝ) : VectorH3 c :=
  P0H3CLM hc (actualHeatDivH3Orbit hc (F r) (ν * (s - r)))

/-- The actual projected H³ Gaussian response is continuous at an interior time whenever its
tensor input path is continuous there. -/
theorem continuousAt_actualHeatDuhamelOrbit {c ν s r₀ : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (hr₀ : r₀ < s) {F : ℝ → TensorH3 c}
    (hF : ContinuousAt F r₀) :
    ContinuousAt (fun r => actualHeatDivH3Orbit hc (F r) (ν * (s - r))) r₀ := by
  let θfun : ℝ → ℝ := fun r => ν * (s - r)
  let θ₀ : ℝ := ν * (s - r₀)
  have hθ₀ : 0 < θ₀ := mul_pos hν (sub_pos.mpr hr₀)
  have hθfun : ContinuousAt θfun r₀ := by
    dsimp [θfun]
    fun_prop
  let x₀ : TensorH3 c := F r₀
  have hfixed : ContinuousAt (fun θ => actualHeatDivH3Orbit hc x₀ θ) θ₀ :=
    continuousAt_actualHeatDivH3Orbit hc hθ₀ x₀
  let a : ℝ := θ₀ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let K : ℝ := ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
      ENNReal.ofReal (heatDivL2Coeff a)).toReal
  have hK : 0 ≤ K := by dsimp [K]; exact ENNReal.toReal_nonneg
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δF : ℝ := ε / (4 * (K + 1))
  have hδF : 0 < δF := by
    dsimp [δF]
    exact div_pos hε (mul_pos (by norm_num) (by linarith))
  obtain ⟨δ₁, hδ₁, hcloseF⟩ := (Metric.continuousAt_iff.mp hF) δF hδF
  obtain ⟨δ₂, hδ₂, hcloseFixed⟩ :=
    (Metric.continuousAt_iff.mp hfixed) (ε / 2) (half_pos hε)
  let δAge : ℝ := min (θ₀ / 2) δ₂
  have hδAge : 0 < δAge := by
    dsimp [δAge]
    exact lt_min (half_pos hθ₀) hδ₂
  obtain ⟨δ₃, hδ₃, hcloseAge⟩ :=
    (Metric.continuousAt_iff.mp hθfun) δAge hδAge
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_⟩
  intro r hdist
  have hr₁ : dist r r₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hr₂ : dist r r₀ < δ₂ := lt_of_lt_of_le hdist
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr₃ : dist r r₀ < δ₃ := lt_of_lt_of_le hdist
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxclose := hcloseF (x := r) hr₁
  have hAgeDist := hcloseAge (x := r) hr₃
  have hAgeAbs : |θfun r - θ₀| < θ₀ / 2 := by
    have hAgeMin : dist (θfun r) θ₀ < min (θ₀ / 2) δ₂ := by
      simpa [δAge] using hAgeDist
    have hAgeRoot := hAgeMin
    rw [Real.dist_eq] at hAgeRoot
    exact lt_of_lt_of_le hAgeRoot (min_le_left _ _)
  have hAgeDelta : dist (θfun r) θ₀ < δ₂ := by
    have hAgeMin : dist (θfun r) θ₀ < min (θ₀ / 2) δ₂ := by
      simpa [δAge] using hAgeDist
    exact lt_of_lt_of_le hAgeMin (min_le_right _ _)
  have hθr : 0 < θfun r := by
    have hleft := (abs_lt.mp hAgeAbs).1
    dsimp [a, θ₀] at hleft
    dsimp [θfun]
    linarith
  have hθrA : a ≤ θfun r := by
    have hleft := (abs_lt.mp hAgeAbs).1
    dsimp [a, θ₀] at hleft ⊢
    linarith
  have hfirst : dist (actualHeatDivH3Orbit hc (F r) (θfun r))
      (actualHeatDivH3Orbit hc x₀ (θfun r)) ≤ K * ‖F r - x₀‖ := by
    rw [dist_eq_norm, actualHeatDivH3Orbit, dif_pos hθr,
      actualHeatDivH3Orbit, dif_pos hθr, ← map_sub]
    exact norm_actualHeatDivH3CLM_le_at_left hc ha hθr hθrA (F r - x₀)
  have hmiddle : dist (actualHeatDivH3Orbit hc x₀ (θfun r))
      (actualHeatDivH3Orbit hc x₀ θ₀) < ε / 2 :=
    hcloseFixed (x := θfun r) hAgeDelta
  have hfirstSmall : K * ‖F r - x₀‖ < ε / 2 := by
    have hnorm : ‖F r - x₀‖ = dist (F r) x₀ := by rw [dist_eq_norm, norm_sub_rev]
    rw [hnorm]
    have hclose := hcloseF (x := r) hr₁
    have hden : 0 < 4 * (K + 1) := by positivity
    have hratio : 0 ≤ ε / (4 * (K + 1)) := div_nonneg hε.le hden.le
    calc
      K * dist (F r) x₀ ≤ K * δF :=
        mul_le_mul_of_nonneg_left (le_of_lt hclose) hK
      _ ≤ (K + 1) * δF :=
        mul_le_mul_of_nonneg_right (by linarith) hratio
      _ = ε / 4 := by dsimp [δF]; field_simp
      _ < ε / 2 := by linarith
  have hout : dist (actualHeatDivH3Orbit hc (F r) (θfun r))
      (actualHeatDivH3Orbit hc x₀ θ₀) < ε := by
    calc
      _ ≤ dist (actualHeatDivH3Orbit hc (F r) (θfun r))
          (actualHeatDivH3Orbit hc x₀ (θfun r)) +
          dist (actualHeatDivH3Orbit hc x₀ (θfun r))
          (actualHeatDivH3Orbit hc x₀ θ₀) := dist_triangle _ _ _
      _ < ε := by linarith [hfirst, hmiddle, hfirstSmall]
  simpa [θfun, θ₀, x₀] using hout

theorem continuousAt_projectedHeatDuhamelOrbit {c ν s r₀ : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (hr₀ : r₀ < s) {F : ℝ → TensorH3 c}
    (hF : ContinuousAt F r₀) :
    ContinuousAt (projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F) r₀ := by
  exact (P0H3CLM hc).continuous.continuousAt.comp
    (continuousAt_actualHeatDuhamelOrbit hc hν hr₀ hF)

#print axioms UnforcedLeray.TrainB.continuousAt_projectedHeatDuhamelOrbit
#print axioms UnforcedLeray.TrainB.continuousAt_actualHeatDuhamelOrbit

end UnforcedLeray.TrainB
