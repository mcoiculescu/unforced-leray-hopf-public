import UnforcedLeray.Short.PartI.Sub.PartI_T04_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ProjectedHeatDivOrbitIntegral
import UnforcedLeray.Lib.TrainB.TensorBridge
import UnforcedLeray.Lib.TrainB.P0GaussianVelocityPath
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelPath
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelIntegrable
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelEstimate
import UnforcedLeray.Lib.TrainB.P0CompactPathExtension

/-!
# Part I, task `PartI:T04/1/2`: the Duhamel integral of the concatenated path splits at `T₁`

Source: `the November 2 reference manuscript` lines 270-277.

For `u₁` on `[0,T₁]`, `u₂` on `[0,T₂]` with `u₂ 0 = u₁ T₁` and `T₁ ≤ t ≤ T₁ + T₂`, the projected
Duhamel term of the concatenation splits at `T₁`: the piece on `(0,T₁)` is the heat evolution over
`ν(t-T₁)` of the Duhamel term of `u₁` at `T₁` (the lag lemma
`heatVecH3Semigroup_integral_projectedDuhamelLag`), and the piece on `(T₁,t)` is the Duhamel term of
`u₂` at `t - T₁` after the translation `r ↦ r - T₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem concatDS_stress_apply {c : ℝ} (hc1 : 1 ≤ c) (u : ContinuousMap ℝ (VectorH3 c)) (r : ℝ) :
    tensorH3StressPath hc1 u r = tensorH3Bilinear hc1 (u r) (u r) := rfl

/-- Integrability of the projected Duhamel orbit on `(0,T)` for a bounded stress path. -/
theorem concatDS_integrableOn {c ν T M : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : ContinuousMap ℝ (VectorH3 c)) (hM : ∀ r, ‖tensorH3StressPath hc1 u r‖ ≤ M) :
    IntegrableOn (projectedHeatDuhamelOrbit (ν := ν) (s := T) hc (tensorH3StressPath hc1 u))
      (Ioo 0 T) := by
  rcases hT.eq_or_lt with h | h
  · rw [← h, Set.Ioo_self]
    exact integrableOn_empty
  · exact integrableOn_projectedHeatDuhamelOrbit hc hν h (tensorH3StressPath hc1 u)
      (fun r _ => hM r)

set_option maxHeartbeats 1000000 in
theorem concatDS_early {c T₁ T₂ : ℝ} (hc1 : 1 ≤ c) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c))
    (h0 : u₂ ⟨0, le_rfl, hT₂⟩ = u₁ ⟨T₁, hT₁, le_rfl⟩) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T₁) :
    tensorH3StressPath hc1
        (extendCompactPath (add_nonneg hT₁ hT₂) (concatPath hT₁ hT₂ u₁ u₂)) r =
      tensorH3StressPath hc1 (extendCompactPath hT₁ u₁) r := by
  have hr1 : r ∈ Icc (0 : ℝ) (T₁ + T₂) := ⟨hr.1, by linarith [hr.2]⟩
  rw [concatDS_stress_apply, concatDS_stress_apply,
    extendCompactPath_apply_of_mem _ _ hr1, extendCompactPath_apply_of_mem _ _ hr,
    concatPath_early hT₁ hT₂ u₁ u₂ h0 ⟨r, hr1⟩ hr.2]

set_option maxHeartbeats 1000000 in
theorem concatDS_late {c T₁ T₂ : ℝ} (hc1 : 1 ≤ c) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c)) (r : ℝ) (hr : r ∈ Icc T₁ (T₁ + T₂)) :
    tensorH3StressPath hc1
        (extendCompactPath (add_nonneg hT₁ hT₂) (concatPath hT₁ hT₂ u₁ u₂)) r =
      tensorH3StressPath hc1 (extendCompactPath hT₂ u₂) (r - T₁) := by
  have hr1 : r ∈ Icc (0 : ℝ) (T₁ + T₂) := ⟨by linarith [hr.1], hr.2⟩
  have hr2 : r - T₁ ∈ Icc (0 : ℝ) T₂ := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  rw [concatDS_stress_apply, concatDS_stress_apply,
    extendCompactPath_apply_of_mem _ _ hr1, extendCompactPath_apply_of_mem _ _ hr2,
    concatPath_late hT₁ hT₂ u₁ u₂ ⟨r, hr1⟩ hr.1]

theorem concatDS_pdo_early {c ν T₁ T₂ t : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hT₁ : 0 ≤ T₁)
    (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c))
    (h0 : u₂ ⟨0, le_rfl, hT₂⟩ = u₁ ⟨T₁, hT₁, le_rfl⟩) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T₁) :
    projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1
          (extendCompactPath (add_nonneg hT₁ hT₂) (concatPath hT₁ hT₂ u₁ u₂))) r =
      projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁)) r := by
  unfold projectedHeatDuhamelOrbit
  rw [concatDS_early hc1 hT₁ hT₂ u₁ u₂ h0 r hr]

theorem concatDS_pdo_late {c ν T₁ T₂ t : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hT₁ : 0 ≤ T₁)
    (hT₂ : 0 ≤ T₂)
    (u₁ : ContinuousMap (Icc (0 : ℝ) T₁) (VectorH3 c))
    (u₂ : ContinuousMap (Icc (0 : ℝ) T₂) (VectorH3 c)) (r : ℝ) (hr : r ∈ Icc T₁ (T₁ + T₂)) :
    projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1
          (extendCompactPath (add_nonneg hT₁ hT₂) (concatPath hT₁ hT₂ u₁ u₂))) r =
      projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
        (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) (r - T₁) := by
  unfold projectedHeatDuhamelOrbit
  rw [concatDS_late hc1 hT₁ hT₂ u₁ u₂ r hr, show ν * (t - r) = ν * ((t - T₁) - (r - T₁)) by ring]

/-- **Duhamel split at `T₁`** (`ConcatDuhamelSplit`, lines 276-277). -/
theorem concatDuhamelSplit : ConcatDuhamelSplit := by
  intro c ν T₁ T₂ hc hc1 hν hT₁ hT₂ u₁ u₂ h0 t ht1 ht2
  have hT : 0 ≤ T₁ + T₂ := add_nonneg hT₁ hT₂
  -- integrability of the Duhamel orbit of the concatenation on `(0,t)`
  have hIoo : IntegrableOn
      (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂)))) (Ioo 0 t) :=
    concatDS_integrableOn hc hc1 hν (by linarith) _
      (fun r => norm_tensorH3StressPath_extendCompactPath_le hc1 hT (concatPath hT₁ hT₂ u₁ u₂) r)
  have eIocIoo : Ioc (0 : ℝ) t =ᵐ[volume] Ioo (0 : ℝ) t := Ioo_ae_eq_Ioc.symm
  have hIoc : IntegrableOn
      (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂)))) (Ioc 0 t) :=
    hIoo.congr_set_ae eIocIoo
  have hI1 : IntegrableOn
      (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂)))) (Ioc 0 T₁) :=
    hIoc.mono_set (Ioc_subset_Ioc le_rfl ht1)
  have hI2 : IntegrableOn
      (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂)))) (Ioc T₁ t) :=
    hIoc.mono_set (Ioc_subset_Ioc hT₁ le_rfl)
  -- the split of `(0,t]` at `T₁`
  have hsplit : ∫ r in Ioc 0 t,
      projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
        (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r =
      (∫ r in Ioc 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) +
      ∫ r in Ioc T₁ t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r := by
    rw [← Ioc_union_Ioc_eq_Ioc hT₁ ht1]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI1 hI2
  -- early piece: equal to the early Duhamel integral of `u₁`, then the lag lemma
  have eIocIooEarly : Ioc (0 : ℝ) T₁ =ᵐ[volume] Ioo (0 : ℝ) T₁ := Ioo_ae_eq_Ioc.symm
  have hA : (∫ r in Ioc 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) =
      ∫ r in Ioo 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁)) r := by
    rw [setIntegral_congr_set eIocIooEarly]
    exact setIntegral_congr_fun measurableSet_Ioo (fun r hr =>
      concatDS_pdo_early hc hc1 hT₁ hT₂ u₁ u₂ h0 r ⟨hr.1.le, hr.2.le⟩)
  have hlag : heatVecH3Semigroup (c := c) (θ := ν * (t - T₁)) hc
      (∫ r in Ioo 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := T₁) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁)) r) =
      ∫ r in Ioo 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁)) r :=
    heatVecH3Semigroup_integral_projectedDuhamelLag (a := 0) hc hν ht1
      (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁))
      (concatDS_integrableOn hc hc1 hν hT₁ (extendCompactPath hT₁ u₁)
        (fun r => norm_tensorH3StressPath_extendCompactPath_le hc1 hT₁ u₁ r))
  -- late piece: translate `r ↦ r - T₁`
  have hB : (∫ r in Ioc T₁ t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) =
      ∫ r in Ioo 0 (t - T₁),
        projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) r := by
    have e1 : (∫ r in Ioc T₁ t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) =
        ∫ r in Ioc T₁ t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) (r - T₁) :=
      setIntegral_congr_fun measurableSet_Ioc (fun r hr =>
        concatDS_pdo_late hc hc1 hT₁ hT₂ u₁ u₂ r ⟨hr.1.le, hr.2.trans ht2⟩)
    have e2 : (∫ r in Ioc T₁ t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) (r - T₁)) =
        ∫ x in T₁..t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) (x - T₁) :=
      (intervalIntegral.integral_of_le ht1).symm
    have e3 : (∫ x in T₁..t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) (x - T₁)) =
        ∫ x in (T₁ - T₁)..(t - T₁),
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) x :=
      intervalIntegral.integral_comp_sub_right
        (f := fun x => projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) x) T₁
    rw [sub_self] at e3
    have e4 : (∫ x in (0 : ℝ)..(t - T₁),
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) x) =
        ∫ x in Ioc 0 (t - T₁),
          projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
            (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) x :=
      intervalIntegral.integral_of_le (sub_nonneg.2 ht1)
    have e5 : Ioc (0 : ℝ) (t - T₁) =ᵐ[volume] Ioo (0 : ℝ) (t - T₁) := Ioo_ae_eq_Ioc.symm
    rw [e1, e2, e3, e4, setIntegral_congr_set e5]
  -- the full identity
  have hfin : (∫ r in Ioo 0 t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) =
      (∫ r in Ioo 0 T₁,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₁ u₁)) r) +
      ∫ r in Ioo 0 (t - T₁),
        projectedHeatDuhamelOrbit (ν := ν) (s := t - T₁) hc
          (tensorH3StressPath hc1 (extendCompactPath hT₂ u₂)) r := by
    have e0 : (∫ r in Ioo 0 t,
        projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r) =
        ∫ r in Ioc 0 t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
            (tensorH3StressPath hc1 (extendCompactPath hT (concatPath hT₁ hT₂ u₁ u₂))) r :=
      setIntegral_congr_set Ioo_ae_eq_Ioc
    rw [e0, hsplit, hA, hB]
  unfold projectedHeatNonlinearityIntegral
  rw [hlag, hfin]

end UnforcedLeray.Short.PartI
