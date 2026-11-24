import UnforcedLeray.Short.PartI.Sub.T04.Defs
import UnforcedLeray.Lib.TrainB.P0CompactDuhamelCausal
import UnforcedLeray.Lib.TrainB.P0CompactMildFixedPoint
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupP0

/-!
# Part I, task `PartI:T04/1` (`MildConcat`): decomposition

Source: `the November 2 reference manuscript` lines 270-277 (global mild solution by
restart).  The concatenated path `concatPath` is `u₁` on `[0,T₁]` and `u₂(· - T₁)` on `[T₁,T₁+T₂]`.
Proved here: its values, and the fixed-point equation for `t ≤ T₁` (causal lemma), and the algebra of
the equation for `t ≥ T₁` from two leaves:

* `ConcatSeedRestart`: the projected heat seed of `x` restarts from its value at `T₁` by the heat
  semigroup;
* `ConcatDuhamelSplit`: the Duhamel integral of the concatenated path splits at `T₁`.

`mildConcat_of` assembles `MildConcat` from them.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- The concatenation of two compact paths, `u₁(t)` for `t ≤ T₁` and `u₂(t - T₁)` for `t ≥ T₁`
(written with the constant-at-the-ends extensions, so continuity is automatic; the paths match at
`T₁` when `u₂ 0 = u₁ T₁`). -/
def concatPath {c T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c)) :
    ContinuousMap (Icc (0 : ℝ) (T₁ + T₂)) (VectorH3 c) where
  toFun t := extendCompactPath hT₁ u₁ t.1 +
    (extendCompactPath hT₂ u₂ (t.1 - T₁) - u₁ ⟨T₁, hT₁, le_rfl⟩)
  continuous_toFun := by
    have h1 := (extendCompactPath hT₁ u₁).continuous
    have h2 := (extendCompactPath hT₂ u₂).continuous
    fun_prop

theorem extendCompactPath_of_ge {T : ℝ} (hT : 0 ≤ T) {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) T) E) {t : ℝ} (h : T ≤ t) :
    extendCompactPath hT u t = u ⟨T, hT, le_rfl⟩ := by
  unfold extendCompactPath
  change u _ = _
  congr 1
  apply Subtype.ext
  simp [clampTimeMap, min_eq_left h, max_eq_right hT]

theorem extendCompactPath_of_le {T : ℝ} (hT : 0 ≤ T) {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) T) E) {t : ℝ} (h : t ≤ 0) :
    extendCompactPath hT u t = u ⟨0, le_rfl, hT⟩ := by
  unfold extendCompactPath
  change u _ = _
  congr 1
  apply Subtype.ext
  simp [clampTimeMap, min_eq_right (h.trans hT), max_eq_left h]

theorem concatPath_early {c T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c))
    (h0 : u₂ ⟨0, le_rfl, hT₂⟩ = u₁ ⟨T₁, hT₁, le_rfl⟩)
    (t : Icc (0 : ℝ) (T₁ + T₂)) (ht : t.1 ≤ T₁) :
    concatPath hT₁ hT₂ u₁ u₂ t = u₁ ⟨t.1, t.2.1, ht⟩ := by
  change extendCompactPath hT₁ u₁ t.1 +
    (extendCompactPath hT₂ u₂ (t.1 - T₁) - u₁ ⟨T₁, hT₁, le_rfl⟩) = _
  rw [extendCompactPath_of_le hT₂ u₂ (by linarith), h0, sub_self, add_zero,
    extendCompactPath_apply_of_mem hT₁ u₁ ⟨t.2.1, ht⟩]

theorem concatPath_late {c T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c))
    (t : Icc (0 : ℝ) (T₁ + T₂)) (ht : T₁ ≤ t.1) :
    concatPath hT₁ hT₂ u₁ u₂ t = u₂ ⟨t.1 - T₁, by linarith, by linarith [t.2.2]⟩ := by
  change extendCompactPath hT₁ u₁ t.1 +
    (extendCompactPath hT₂ u₂ (t.1 - T₁) - u₁ ⟨T₁, hT₁, le_rfl⟩) = _
  rw [extendCompactPath_of_ge hT₁ u₁ ht,
    extendCompactPath_apply_of_mem hT₂ u₂ ⟨by linarith, by linarith [t.2.2]⟩]
  abel

/-- **Seed restart** (line 276, "restart"): for `0 ≤ T₁ ≤ t`,
`projectedHeatSeedPath x t = e^{ν(t-T₁)Δ}(projectedHeatSeedPath x T₁)`.  Route: unfold
`projectedHeatSeedPath` (`P₀ e^{ν t Δ} x`, ages `max 0 (ν t)`), `heatVecH3Semigroup_comp_of_nonneg`
and `heatVecH3Semigroup_P0H3CLM_comm`. -/
def ConcatSeedRestart : Prop :=
  ∀ (c ν T₁ t : ℝ) (hc : 0 < c) (hν : 0 < ν) (x : VectorH3 c), 0 ≤ T₁ → T₁ ≤ t →
    projectedHeatSeedPath hc hν x t =
      heatVecH3Semigroup (c := c) (θ := ν * (t - T₁)) hc (projectedHeatSeedPath hc hν x T₁)

/-- **Duhamel split at `T₁`** (lines 276-277; `TrainB.compact_mild_restart_equation` read forwards).
For `u₁` on `[0,T₁]`, `u₂` on `[0,T₂]` with `u₂ 0 = u₁ T₁` and `T₁ ≤ t ≤ T₁ + T₂`: the actual
projected Duhamel term of the concatenated path at `t` is the heat evolution over `ν(t-T₁)` of the
term of `u₁` at `T₁`, plus the term of `u₂` at `t - T₁`.  Route: split `Ioo 0 t` at `T₁`, apply
`heatVecH3Semigroup_integral_projectedDuhamelLag` to `(0,T₁)` (as in
`compact_mild_restart_equation`), translate `r ↦ r - T₁` on `(T₁,t)` where the stress path of the
concatenation at `r` is that of `extendCompactPath u₂` at `r - T₁`; the case `t = T₁` is trivial. -/
def ConcatDuhamelSplit : Prop :=
  ∀ (c ν T₁ T₂ : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c)),
    u₂ ⟨0, le_rfl, hT₂⟩ = u₁ ⟨T₁, hT₁, le_rfl⟩ → ∀ t : ℝ, T₁ ≤ t → t ≤ T₁ + T₂ →
      projectedHeatNonlinearityIntegral (ν := ν) hc hc1
        (extendCompactPath (add_nonneg hT₁ hT₂) (concatPath hT₁ hT₂ u₁ u₂)) t =
      heatVecH3Semigroup (c := c) (θ := ν * (t - T₁)) hc
        (projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₁ u₁) T₁) +
      projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₂ u₂) (t - T₁)

set_option maxHeartbeats 1600000 in
theorem mildConcat_of (hS : ConcatSeedRestart) (hD : ConcatDuhamelSplit) : MildConcat := by
  intro ν c T₁ T₂ hν hc hc1 hT₁ hT₂ x u₁ u₂ hx hfix1 hP1 htr1 hfix2 hP2 htr2
  have hT : 0 < T₁ + T₂ := add_pos hT₁ hT₂
  have h0 : u₂ ⟨0, le_rfl, hT₂.le⟩ = u₁ ⟨T₁, hT₁.le, le_rfl⟩ := htr2
  set u := concatPath hT₁.le hT₂.le u₁ u₂ with hu
  have pt1 : ∀ t : Icc (0 : ℝ) T₁, u₁ t = projectedHeatSeedPath hc hν x t -
      projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₁.le u₁) t := by
    intro t
    exact compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel hc hc1 hν hT₁.le _ u₁ hfix1 t
  have pt2 : ∀ t : Icc (0 : ℝ) T₂, u₂ t = projectedHeatSeedPath hc hν (u₁ ⟨T₁, hT₁.le, le_rfl⟩) t -
      projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₂.le u₂) t := by
    intro t
    exact compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel hc hc1 hν hT₂.le _ u₂ hfix2 t
  refine ⟨u, ?_, ?_, ?_⟩
  · refine ContinuousMap.ext fun t => ?_
    change u t = projectedHeatSeedPath hc hν x t +
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t
    rw [projectedNonlinearDuhamelCompactMap_apply, ← sub_eq_add_neg]
    rcases le_total t.1 T₁ with ht | ht
    · -- early: causal comparison with `u₁`
      have hn := projectedNonlinearDuhamelCompactMap_eq_of_clamped_paths_eq_causal hc hc1 hν
        hT.le hT₁.le u u₁ t.2 ⟨t.2.1, ht⟩ (t := t.1) (by
          intro r hr
          have hr1 : r ∈ Icc (0 : ℝ) (T₁ + T₂) := ⟨hr.1.le, by linarith [hr.2, t.2.2]⟩
          have hr2 : r ∈ Icc (0 : ℝ) T₁ := ⟨hr.1.le, by linarith [hr.2]⟩
          rw [hu, extendCompactPath_apply_of_mem _ _ hr1,
            extendCompactPath_apply_of_mem _ _ hr2, concatPath_early _ _ _ _ h0 ⟨r, hr1⟩ hr2.2])
      rw [projectedNonlinearDuhamelCompactMap_apply, projectedNonlinearDuhamelCompactMap_apply] at hn
      rw [hu, concatPath_early hT₁.le hT₂.le u₁ u₂ h0 t ht]
      have := pt1 ⟨t.1, t.2.1, ht⟩
      rw [this]
      have hn' := neg_inj.1 hn
      exact congrArg₂ _ rfl hn'.symm
    · -- late
      have hsplit := hD c ν T₁ T₂ hc hc1 hν hT₁.le hT₂.le u₁ u₂ h0 t.1 ht t.2.2
      have hseed := hS c ν T₁ t.1 hc hν x hT₁.le ht
      have hyP : P0H3CLM hc (u₁ ⟨T₁, hT₁.le, le_rfl⟩) = u₁ ⟨T₁, hT₁.le, le_rfl⟩ := hP1 _
      have hs2 := pt2 ⟨t.1 - T₁, by linarith, by linarith [t.2.2]⟩
      have e3 : u₁ ⟨T₁, hT₁.le, le_rfl⟩ = projectedHeatSeedPath hc hν x T₁ -
          projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₁.le u₁) T₁ :=
        pt1 ⟨T₁, hT₁.le, le_rfl⟩
      have hseed2 : projectedHeatSeedPath hc hν (u₁ ⟨T₁, hT₁.le, le_rfl⟩) (t.1 - T₁) =
          heatVecH3Semigroup (c := c) (θ := ν * (t.1 - T₁)) hc (u₁ ⟨T₁, hT₁.le, le_rfl⟩) := by
        change P0H3CLM hc (heatVecH3Semigroup (c := c) (θ := max 0 (ν * (t.1 - T₁))) hc _) = _
        rw [max_eq_right (by have := hν; nlinarith), heatVecH3Semigroup_P0H3CLM_comm, hyP]
      have e1 : u₂ ⟨t.1 - T₁, by linarith, by linarith [t.2.2]⟩ =
          heatVecH3Semigroup (c := c) (θ := ν * (t.1 - T₁)) hc (u₁ ⟨T₁, hT₁.le, le_rfl⟩) -
          projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT₂.le u₂)
            (t.1 - T₁) := by
        rw [← hseed2]; exact hs2
      rw [hu, concatPath_late hT₁.le hT₂.le u₁ u₂ t ht, e1, hsplit, hseed]
      rw [e3]
      simp only [map_sub]
      abel
  · intro t
    by_cases ht : t.1 ≤ T₁
    · have e : u t = u₁ ⟨t.1, t.2.1, ht⟩ := concatPath_early hT₁.le hT₂.le u₁ u₂ h0 t ht
      exact (congrArg (P0H3CLM hc) e).trans ((hP1 ⟨t.1, t.2.1, ht⟩).trans e.symm)
    · have hge : T₁ ≤ t.1 := le_of_not_ge ht
      have hlt : t.1 - T₁ ≤ T₂ := by
        have h : t.1 ≤ T₁ + T₂ := t.2.2
        exact sub_le_iff_le_add.2 (by linarith)
      have e : u t = u₂ ⟨t.1 - T₁, sub_nonneg.2 hge, hlt⟩ :=
        concatPath_late hT₁.le hT₂.le u₁ u₂ t hge
      exact (congrArg (P0H3CLM hc) e).trans ((hP2 ⟨t.1 - T₁, sub_nonneg.2 hge, hlt⟩).trans e.symm)
  · have e : u ⟨0, le_rfl, hT.le⟩ = u₁ ⟨0, le_rfl, hT₁.le⟩ :=
      concatPath_early hT₁.le hT₂.le u₁ u₂ h0 _ hT₁.le
    exact e.trans htr1

end UnforcedLeray.Short.PartI
