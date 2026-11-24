import UnforcedLeray.Short.PartI.Sub.T02_1_2_4

/-!
# Part I, task `PartI:T02/1/2/4/2`: additivity of the polarised Duhamel map (leaf A)

Target `bilDuhamelAdditive : BilDuhamelAdditive` (`Short/PartI/Sub/T02_1_2_4.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288.

`bilDuhamel a b` is `-(P ∘ ι)` where `P` is the actual projected Gaussian Duhamel path of the
tensor stress `r ↦ a(r) ⊗ b(r)` on the full line (with `a, b` extended by clamping,
`extendCompactPath`) and `ι` is the compact time inclusion.  Its value at time `t` is
`-∫_{(0,t)} P₀ e^{ν(t-r)Δ} div (a(r) ⊗ b(r)) dr`, which does not depend on the bound parameter `M`
of `projectedHeatDuhamelContinuousMap`.

The proof is pointwise:

1. `extendCompactPath` is additive (it is a composition with a fixed map).
2. `tensorH3Bilinear` is bilinear, so `bilStressPath` is additive in each argument.
3. `actualHeatDivH3Orbit` is additive in its tensor input, so the orbit is additive, and the
   Bochner integral splits by `integral_add`, the summands being integrable on `Ioo 0 s` by
   `integrableOn_projectedHeatDuhamelOrbit` (and the trivial case `s ≤ 0`, where the interval is
   empty).

The target is `bilDuhamelAdditive`, which gives both conjuncts.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### Additivity of the actual orbit in the tensor input -/

/-- The actual H³ heat-divergence orbit is additive in its tensor input. -/
theorem actualHeatDivH3Orbit_add_tensor {c : ℝ} (hc : 0 < c) (x y : TensorH3 c) (θ : ℝ) :
    actualHeatDivH3Orbit hc (x + y) θ =
      actualHeatDivH3Orbit hc x θ + actualHeatDivH3Orbit hc y θ := by
  unfold actualHeatDivH3Orbit
  split_ifs with h
  · rw [map_add]
  · rw [add_zero]

/-- The projected Duhamel orbit is additive along tensor paths which add pointwise. -/
theorem projectedHeatDuhamelOrbit_add_pointwise {c ν s : ℝ} (hc : 0 < c)
    (F G H : ℝ → TensorH3 c) (hH : ∀ r, H r = F r + G r) :
    ∀ r, projectedHeatDuhamelOrbit (ν := ν) (s := s) hc H r =
      projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F r +
        projectedHeatDuhamelOrbit (ν := ν) (s := s) hc G r := by
  intro r
  unfold projectedHeatDuhamelOrbit
  rw [hH r, actualHeatDivH3Orbit_add_tensor, map_add]

/-! ### Integrability and additivity of the projected Duhamel integral -/

/-- The projected Duhamel orbit of a bounded continuous tensor path is integrable on `Ioo 0 s`,
for every real `s` (the interval is empty when `s ≤ 0`). -/
theorem integrable_projectedHeatDuhamelOrbit_zero {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (s : ℝ)
    (F : ContinuousMap ℝ (TensorH3 c)) (M : ℝ) (hF : ∀ r, ‖F r‖ ≤ M) :
    Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F)
      (volume.restrict (Ioo 0 s)) := by
  rcases lt_or_ge 0 s with hs | hs
  · exact integrableOn_projectedHeatDuhamelOrbit hc hν hs F (fun r _ => hF r)
  · rw [Ioo_eq_empty (not_lt.mpr hs), Measure.restrict_empty]
    exact integrable_zero_measure

/-- The actual projected Duhamel integral is additive in the tensor path, when the tensor path of
the sum is the pointwise sum of the two tensor paths. -/
theorem projectedHeatDuhamelIntegral_add_pointwise {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (s : ℝ)
    (F G H : ContinuousMap ℝ (TensorH3 c)) (M N : ℝ)
    (hF : ∀ r, ‖F r‖ ≤ M) (hG : ∀ r, ‖G r‖ ≤ N)
    (hH : ∀ r, H r = F r + G r) :
    projectedHeatDuhamelIntegral (ν := ν) hc H s =
      projectedHeatDuhamelIntegral (ν := ν) hc F s +
        projectedHeatDuhamelIntegral (ν := ν) hc G s := by
  unfold projectedHeatDuhamelIntegral
  simp only [projectedHeatDuhamelOrbit_add_pointwise (ν := ν) (s := s) hc
    (⇑F) (⇑G) (⇑H) hH]
  rw [integral_add (integrable_projectedHeatDuhamelOrbit_zero hc hν s F M hF)
    (integrable_projectedHeatDuhamelOrbit_zero hc hν s G N hG)]

/-! ### The polarised stress path and the extended paths -/

/-- Clamped extension is additive. -/
theorem extendCompactPath_add_path {c T : ℝ} (hT : 0 ≤ T) (a a' : MPath c T) :
    extendCompactPath hT (a + a') = extendCompactPath hT a + extendCompactPath hT a' :=
  ContinuousMap.ext fun _ => rfl

/-- A continuous bilinear map is additive in its first argument (generic form). -/
theorem clmBilinear_add_left {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E →L[ℝ] F →L[ℝ] G) (x x' : E) (y : F) :
    T (x + x') y = T x y + T x' y := by
  rw [map_add, add_apply]

/-- A continuous bilinear map is additive in its second argument (generic form). -/
theorem clmBilinear_add_right {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E →L[ℝ] F →L[ℝ] G) (x : E) (y y' : F) :
    T x (y + y') = T x y + T x y' := by
  rw [map_add]

/-- The stress path of a sum in the first argument splits pointwise. -/
theorem bilStressPath_add_left_pointwise {c : ℝ} (hc1 : 1 ≤ c)
    (a a' b : ContinuousMap ℝ (VectorH3 c)) (r : ℝ) :
    bilStressPath hc1 (a + a') b r = bilStressPath hc1 a b r + bilStressPath hc1 a' b r := by
  change tensorH3Bilinear hc1 ((a + a') r) (b r) =
    tensorH3Bilinear hc1 (a r) (b r) + tensorH3Bilinear hc1 (a' r) (b r)
  rw [ContinuousMap.add_apply]
  exact clmBilinear_add_left (tensorH3Bilinear hc1) (a r) (a' r) (b r)

/-- The stress path of a sum in the second argument splits pointwise. -/
theorem bilStressPath_add_right_pointwise {c : ℝ} (hc1 : 1 ≤ c)
    (a b b' : ContinuousMap ℝ (VectorH3 c)) (r : ℝ) :
    bilStressPath hc1 a (b + b') r = bilStressPath hc1 a b r + bilStressPath hc1 a b' r := by
  change tensorH3Bilinear hc1 (a r) ((b + b') r) =
    tensorH3Bilinear hc1 (a r) (b r) + tensorH3Bilinear hc1 (a r) (b' r)
  rw [ContinuousMap.add_apply]
  exact clmBilinear_add_right (tensorH3Bilinear hc1) (a r) (b r) (b' r)

/-- The uniform bound of the extended stress path, as used in the definition of `bilDuhamel`. -/
theorem norm_bilStressPath_extend_le {c T : ℝ} (hc1 : 1 ≤ c) (hT : 0 ≤ T)
    (a b : MPath c T) (r : ℝ) :
    ‖bilStressPath hc1 (extendCompactPath hT a) (extendCompactPath hT b) r‖ ≤
      1536 * ‖a‖ * ‖b‖ := by
  change ‖tensorH3Bilinear hc1 (extendCompactPath hT a r) (extendCompactPath hT b r)‖ ≤ _
  calc _ ≤ 1536 * ‖extendCompactPath hT a r‖ * ‖extendCompactPath hT b r‖ :=
        norm_tensorH3Bilinear_apply_le hc1 _ _
    _ ≤ 1536 * ‖a‖ * ‖b‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_extendCompactPath_le hT a r)
          (by norm_num)) (norm_extendCompactPath_le hT b r) (norm_nonneg _)
          (mul_nonneg (by norm_num) (norm_nonneg _))

/-- The value of `bilDuhamel` at a time is the negative of the projected Duhamel integral of the
extended stress path. -/
theorem bilDuhamel_apply_eq_integral {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν)
    (hT : 0 ≤ T) (a b : MPath c T) (t : Icc (0 : ℝ) T) :
    bilDuhamel hc hc1 hν hT a b t =
      -(projectedHeatDuhamelIntegral (ν := ν) hc
        (bilStressPath hc1 (extendCompactPath hT a) (extendCompactPath hT b)) (t : ℝ)) :=
  rfl

/-! ### The target -/

/-- **Leaf A** (`PartI:T02/1/2/4/2`): the polarised Duhamel map `bilDuhamel` is additive in each
argument (source lines 261-288). -/
theorem bilDuhamelAdditive : BilDuhamelAdditive := by
  intro ν c T hν hc hc1 hT a a' b b'
  have hT0 : 0 ≤ T := hT.le
  constructor
  · -- additivity in the first argument
    have key : ∀ s : ℝ,
        projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 (a + a')) (extendCompactPath hT0 b)) s =
          projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b)) s +
          projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 a') (extendCompactPath hT0 b)) s := by
      intro s
      rw [extendCompactPath_add_path hT0 a a']
      exact projectedHeatDuhamelIntegral_add_pointwise (ν := ν) hc hν s
        (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b))
        (bilStressPath hc1 (extendCompactPath hT0 a') (extendCompactPath hT0 b))
        (bilStressPath hc1 (extendCompactPath hT0 a + extendCompactPath hT0 a')
          (extendCompactPath hT0 b))
        (1536 * ‖a‖ * ‖b‖) (1536 * ‖a'‖ * ‖b‖)
        (fun r => norm_bilStressPath_extend_le hc1 hT0 a b r)
        (fun r => norm_bilStressPath_extend_le hc1 hT0 a' b r)
        (fun r => bilStressPath_add_left_pointwise hc1
          (extendCompactPath hT0 a) (extendCompactPath hT0 a') (extendCompactPath hT0 b) r)
    refine ContinuousMap.ext fun t => ?_
    simp only [bilDuhamel_apply_eq_integral, ContinuousMap.add_apply]
    rw [key, neg_add]
  · -- additivity in the second argument
    have key : ∀ s : ℝ,
        projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 (b + b'))) s =
          projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b)) s +
          projectedHeatDuhamelIntegral (ν := ν) hc
            (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b')) s := by
      intro s
      rw [extendCompactPath_add_path hT0 b b']
      exact projectedHeatDuhamelIntegral_add_pointwise (ν := ν) hc hν s
        (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b))
        (bilStressPath hc1 (extendCompactPath hT0 a) (extendCompactPath hT0 b'))
        (bilStressPath hc1 (extendCompactPath hT0 a)
          (extendCompactPath hT0 b + extendCompactPath hT0 b'))
        (1536 * ‖a‖ * ‖b‖) (1536 * ‖a‖ * ‖b'‖)
        (fun r => norm_bilStressPath_extend_le hc1 hT0 a b r)
        (fun r => norm_bilStressPath_extend_le hc1 hT0 a b' r)
        (fun r => bilStressPath_add_right_pointwise hc1
          (extendCompactPath hT0 a) (extendCompactPath hT0 b) (extendCompactPath hT0 b') r)
    refine ContinuousMap.ext fun t => ?_
    simp only [bilDuhamel_apply_eq_integral, ContinuousMap.add_apply]
    rw [key, neg_add]

end UnforcedLeray.Short.PartI
