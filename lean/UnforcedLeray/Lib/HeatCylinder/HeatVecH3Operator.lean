import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Extension
import UnforcedLeray.Lib.HeatCylinder.H3Operator

/-!
# Contractive actual ordinary heat CLM on centered vector H³

The completed operator is characterized by its actual normalized-cell Gaussian value. Its
period-independent graph norm bound follows from the same smooth approximating sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The normalized value of the smooth Gaussian H³ limit is realized by a unique centered H³
class. -/
theorem existsUnique_actual_heatVecH3_value {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    ∃! Y : UnforcedLeray.Cyl.H ℝ Vec c 0 3,
      vectorH3NormalizedValue hc Y =
        heatVecL2CLM hc θ (vectorH3NormalizedValue hc x) := by
  obtain ⟨y, T, hT, hyrep, hyLim, Y, hYlim, hYvalue⟩ :=
    exists_tendsto_smoothHeatVecH3 hc hθ x
  refine ⟨Y, hYvalue, ?_⟩
  intro Z hZ
  exact vectorH3NormalizedValue_injective hc (hZ.trans hYvalue.symm)

/-- The actual positive-age ordinary vector heat action on the whole centered H³ graph. -/
noncomputable def actualHeatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) : UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
  Classical.choose (existsUnique_actual_heatVecH3_value hc hθ x)

theorem vectorH3NormalizedValue_actualHeatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ x) =
      heatVecL2CLM hc θ (vectorH3NormalizedValue hc x) :=
  (Classical.choose_spec (existsUnique_actual_heatVecH3_value hc hθ x)).1

/-- The actual ordinary H³ heat action is additive. -/
theorem actualHeatVecH3_add {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x y : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    actualHeatVecH3 hc hθ (x + y) = actualHeatVecH3 hc hθ x + actualHeatVecH3 hc hθ y := by
  apply vectorH3NormalizedValue_injective hc
  calc
    vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ (x + y)) =
        heatVecL2CLM hc θ (vectorH3NormalizedValue hc (x + y)) :=
      vectorH3NormalizedValue_actualHeatVecH3 hc hθ (x + y)
    _ = heatVecL2CLM hc θ
        (vectorH3NormalizedValue hc x + vectorH3NormalizedValue hc y) := by
      rw [vectorH3NormalizedValue_add hc]
    _ = heatVecL2CLM hc θ (vectorH3NormalizedValue hc x) +
        heatVecL2CLM hc θ (vectorH3NormalizedValue hc y) := map_add _ _ _
    _ = vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ x) +
        vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ y) := by
      rw [← vectorH3NormalizedValue_actualHeatVecH3 hc hθ x,
        ← vectorH3NormalizedValue_actualHeatVecH3 hc hθ y]
    _ = vectorH3NormalizedValue hc
        (actualHeatVecH3 hc hθ x + actualHeatVecH3 hc hθ y) :=
      (vectorH3NormalizedValue_add hc _ _).symm

/-- The actual ordinary H³ heat action respects real scalar multiplication. -/
theorem actualHeatVecH3_smul {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (r : ℝ) (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    actualHeatVecH3 hc hθ (r • x) = r • actualHeatVecH3 hc hθ x := by
  apply vectorH3NormalizedValue_injective hc
  calc
    vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ (r • x)) =
        heatVecL2CLM hc θ (vectorH3NormalizedValue hc (r • x)) :=
      vectorH3NormalizedValue_actualHeatVecH3 hc hθ (r • x)
    _ = heatVecL2CLM hc θ (r • vectorH3NormalizedValue hc x) := by
      rw [vectorH3NormalizedValue_smul hc]
    _ = r • heatVecL2CLM hc θ (vectorH3NormalizedValue hc x) := map_smul _ _ _
    _ = r • vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ x) := by
      rw [← vectorH3NormalizedValue_actualHeatVecH3 hc hθ x]
    _ = vectorH3NormalizedValue hc (r • actualHeatVecH3 hc hθ x) :=
      (vectorH3NormalizedValue_smul hc r _).symm

/-- The actual ordinary H³ Gaussian heat is a contraction, with no period-dependent factor. -/
theorem norm_actualHeatVecH3_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    ‖actualHeatVecH3 hc hθ x‖ ≤ ‖x‖ := by
  obtain ⟨y, T, hT, hyrep, hyLim, Y, hYlim, hYvalue⟩ :=
    exists_tendsto_smoothHeatVecH3 hc hθ x
  have hYeq : Y = actualHeatVecH3 hc hθ x :=
    vectorH3NormalizedValue_injective hc
      (hYvalue.trans (vectorH3NormalizedValue_actualHeatVecH3 hc hθ x).symm)
  have hOutLim : Tendsto (fun n => heatVecH3 (c := c) (θ := θ) hc hθ (hT n))
      atTop (𝓝 (actualHeatVecH3 hc hθ x)) := by
    change Tendsto (fun n => heatVecH3 (c := c) (θ := θ) hc hθ (hT n))
      atTop (𝓝 Y) at hYlim
    simpa only [hYeq] using hYlim
  have hnormOut : Tendsto
      (fun n => ‖heatVecH3 (c := c) (θ := θ) hc hθ (hT n)‖)
      atTop (𝓝 ‖actualHeatVecH3 hc hθ x‖) :=
    (continuous_norm.tendsto (actualHeatVecH3 hc hθ x)).comp hOutLim
  have hnormIn : Tendsto (fun n => ‖y n‖) atTop (𝓝 ‖x‖) :=
    (continuous_norm.tendsto x).comp hyLim
  have hbound (n : ℕ) :
      ‖heatVecH3 (c := c) (θ := θ) hc hθ (hT n)‖ ≤ ‖y n‖ := by
    rw [hyrep n]
    exact norm_heatVecH3_le_ofCylSmooth hc hθ (hT n)
  exact le_of_tendsto_of_tendsto hnormOut hnormIn (Eventually.of_forall hbound)

/-- Continuous linear operator for the actual ordinary Gaussian heat semigroup at positive age. -/
noncomputable def actualHeatVecH3CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ] UnforcedLeray.Cyl.H ℝ Vec c 0 3 := by
  let L : UnforcedLeray.Cyl.H ℝ Vec c 0 3 →ₗ[ℝ]
      UnforcedLeray.Cyl.H ℝ Vec c 0 3 := {
    toFun := actualHeatVecH3 hc hθ
    map_add' := actualHeatVecH3_add hc hθ
    map_smul' := actualHeatVecH3_smul hc hθ }
  exact L.mkContinuous 1 (fun x => by
    change ‖actualHeatVecH3 hc hθ x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_actualHeatVecH3_le hc hθ x)

@[simp] theorem actualHeatVecH3CLM_apply {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    actualHeatVecH3CLM hc hθ x = actualHeatVecH3 hc hθ x := rfl

theorem norm_actualHeatVecH3CLM_le_one {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ‖actualHeatVecH3CLM hc hθ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  calc
    ‖actualHeatVecH3CLM hc hθ x‖ = ‖actualHeatVecH3 hc hθ x‖ := by
      rw [actualHeatVecH3CLM_apply]
    _ ≤ ‖x‖ := norm_actualHeatVecH3_le hc hθ x
    _ = 1 * ‖x‖ := (one_mul _).symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.existsUnique_actual_heatVecH3_value
#print axioms UnforcedLeray.HeatCylinder.actualHeatVecH3CLM
#print axioms UnforcedLeray.HeatCylinder.norm_actualHeatVecH3CLM_le_one
