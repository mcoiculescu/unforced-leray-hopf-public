import UnforcedLeray.Lib.HeatCylinder.HeatL2ZeroAge
import UnforcedLeray.Lib.HeatCylinder.HeatL2OrbitContinuity

/-!
# Strong continuity and the actual semigroup at all heat ages

At age zero, positive-side Gaussian convergence combines with the exact identity convention at
nonpositive ages. Negative ages are locally constant, while positive ages use the actual kernel
L¹ continuity estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

/-- Full-filter strong continuity at age zero for the actual Plane quotient heat. -/
theorem tendsto_heatL2CLM_apply_zero_full {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => heatL2CLM hc θ x) (𝓝 0) (𝓝 x) := by
  have hleft : Tendsto (fun θ : ℝ => heatL2CLM hc θ x) (𝓝[≤] 0) (𝓝 x) := by
    have hEq : (fun θ : ℝ => heatL2CLM hc θ x) =ᶠ[𝓝[≤] 0] fun _ => x := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : θ ≤ 0 := by simpa using hθ
      rw [heatL2CLM_eq_id_of_nonpos hc hθ']
      rfl
    exact tendsto_const_nhds.congr' hEq.symm
  have hright := tendsto_heatL2CLM_apply_zero hc x
  rw [← nhdsLE_sup_nhdsGT]
  exact hleft.sup hright

/-- Full-filter strong continuity at age zero for the actual Euclidean-vector quotient heat. -/
theorem tendsto_heatVecL2CLM_apply_zero_full {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => heatVecL2CLM hc θ x) (𝓝 0) (𝓝 x) := by
  have hleft : Tendsto (fun θ : ℝ => heatVecL2CLM hc θ x) (𝓝[≤] 0) (𝓝 x) := by
    have hEq : (fun θ : ℝ => heatVecL2CLM hc θ x) =ᶠ[𝓝[≤] 0] fun _ => x := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : θ ≤ 0 := by simpa using hθ
      rw [heatVecL2CLM_eq_id_of_nonpos hc hθ']
      rfl
    exact tendsto_const_nhds.congr' hEq.symm
  have hright := tendsto_heatVecL2CLM_apply_zero hc x
  rw [← nhdsLE_sup_nhdsGT]
  exact hleft.sup hright

/-- Strong continuity of the actual normalized-cell Plane heat orbit at every real age. -/
theorem continuousAt_heatL2CLM_apply {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    ContinuousAt (fun s : ℝ => heatL2CLM hc s x) θ := by
  by_cases hpos : 0 < θ
  · exact continuousAt_heatL2_of_pos hc hpos x
  · by_cases hzero : θ = 0
    · subst θ
      have hAt : heatL2CLM hc 0 x = x := by
        rw [heatL2CLM_eq_id_of_nonpos hc le_rfl]
        rfl
      simpa only [ContinuousAt, hAt] using tendsto_heatL2CLM_apply_zero_full hc x
    · have hneg : θ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
      have hAt : heatL2CLM hc θ x = x := by
        rw [heatL2CLM_eq_id_of_nonpos hc (le_of_lt hneg)]
        rfl
      have hEq : (fun s : ℝ => heatL2CLM hc s x) =ᶠ[𝓝 θ] fun _ => x := by
        filter_upwards [Iio_mem_nhds hneg] with s hs
        rw [heatL2CLM_eq_id_of_nonpos hc (le_of_lt hs)]
        rfl
      have hconst : Tendsto (fun _ : ℝ => x) (𝓝 θ)
          (𝓝 (heatL2CLM hc θ x)) := by rw [hAt]; exact tendsto_const_nhds
      exact hconst.congr' hEq.symm

/-- The actual normalized-cell Plane heat orbit is continuous as a function of its age. -/
theorem continuous_heatL2CLM_apply {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    Continuous (fun θ : ℝ => heatL2CLM hc θ x) :=
  continuous_iff_continuousAt.mpr (fun θ => continuousAt_heatL2CLM_apply hc x)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatL2CLM_apply_zero_full
#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecL2CLM_apply_zero_full
#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatL2CLM_apply
#print axioms UnforcedLeray.HeatCylinder.continuous_heatL2CLM_apply
