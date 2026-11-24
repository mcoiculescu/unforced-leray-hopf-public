import UnforcedLeray.Lib.TrainB.P0CompactDuhamelCausal

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The natural inclusion of one nonnegative compact evolution interval into a longer one. -/
def compactIntervalInclusion {T S : ℝ} (hTS : T ≤ S) :
    ContinuousMap (Icc (0 : ℝ) T) (Icc (0 : ℝ) S) where
  toFun t := ⟨(t : ℝ), ⟨t.2.1, le_trans t.2.2 hTS⟩⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val (by
    intro t
    exact ⟨t.2.1, le_trans t.2.2 hTS⟩)

/-- Restriction of a compact-time path to a shorter nonnegative interval. -/
def restrictCompactEvolutionPath {T S : ℝ} (hTS : T ≤ S)
    {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) S) E) :
    ContinuousMap (Icc (0 : ℝ) T) E := u.comp (compactIntervalInclusion hTS)

@[simp] theorem restrictCompactEvolutionPath_apply {T S : ℝ} (hTS : T ≤ S)
    {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) S) E) (t : Icc (0 : ℝ) T) :
    restrictCompactEvolutionPath hTS u t =
      u ⟨(t : ℝ), ⟨t.2.1, le_trans t.2.2 hTS⟩⟩ := rfl

/-- The constant-clamped extensions of a path and its restriction agree on the shorter interval.
-/
theorem extend_restrictCompactEvolutionPath_eq {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hTS : T ≤ S) {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) S) E) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    extendCompactPath hT (restrictCompactEvolutionPath hTS u) r =
      extendCompactPath hS u r := by
  rw [extendCompactPath_apply_of_mem hT _ hr,
    extendCompactPath_apply_of_mem hS u ⟨hr.1, le_trans hr.2 hTS⟩]
  rfl

/-- Restricting a compact-time path does not change its actual projected Gaussian Duhamel term
at any time in the shorter interval. The proof uses causal dependence on `(0,t)`. -/
theorem projectedNonlinearDuhamelCompactMap_restrict {c ν T S : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hTS : T ≤ S)
    (u : ContinuousMap (Icc (0 : ℝ) S) (VectorH3 c))
    (t : Icc (0 : ℝ) T) :
    projectedNonlinearDuhamelCompactMap hc hc1 hν (le_trans t.2.1 t.2.2)
        (restrictCompactEvolutionPath hTS u) t =
      projectedNonlinearDuhamelCompactMap hc hc1 hν
        (le_trans (le_trans t.2.1 t.2.2) hTS)
        u ⟨(t : ℝ), ⟨t.2.1, le_trans t.2.2 hTS⟩⟩ := by
  have hT0 : 0 ≤ T := le_trans t.2.1 t.2.2
  have hS0 : 0 ≤ S := le_trans hT0 hTS
  apply projectedNonlinearDuhamelCompactMap_eq_of_clamped_paths_eq_causal hc hc1 hν
    hT0 hS0 (restrictCompactEvolutionPath hTS u) u t.2
    ⟨t.2.1, le_trans t.2.2 hTS⟩
  intro r hr
  exact extend_restrictCompactEvolutionPath_eq hT0 hS0 hTS u
    ⟨le_of_lt hr.1, le_trans (le_of_lt hr.2) t.2.2⟩

#print axioms UnforcedLeray.TrainB.compactIntervalInclusion
#print axioms UnforcedLeray.TrainB.projectedNonlinearDuhamelCompactMap_restrict

end UnforcedLeray.TrainB
