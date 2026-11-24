import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelContinuous
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Extending a compact-time Picard path to a bounded full-line path

The Gaussian Duhamel continuity and estimate APIs use continuous paths on all real times. A
trajectory on a compact interval has a canonical constant-at-the-ends extension, obtained by
clamping time to the interval. This leaf records its bound and the corresponding actual stress bound.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- Clamp a real time to the compact interval `[0,T]`. -/
def clampTimeMap (T : ℝ) (hT : 0 ≤ T) : ContinuousMap ℝ (Icc (0 : ℝ) T) where
  toFun t := ⟨max 0 (min T t), ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_const.max (continuous_const.min continuous_id)) _

/-- Constant-at-the-ends extension of a continuous path on `[0,T]`. -/
def extendCompactPath {T : ℝ} (hT : 0 ≤ T) {E : Type*} [TopologicalSpace E]
    (u : ContinuousMap (Icc (0 : ℝ) T) E) : ContinuousMap ℝ E :=
  u.comp (clampTimeMap T hT)

@[simp]
theorem extendCompactPath_apply_of_mem {T : ℝ} (hT : 0 ≤ T) {E : Type*}
    [TopologicalSpace E] (u : ContinuousMap (Icc (0 : ℝ) T) E)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    extendCompactPath hT u t = u ⟨t, ht⟩ := by
  simp [extendCompactPath, clampTimeMap, max_eq_right ht.1, min_eq_right ht.2]

/-- The extension stays within the compact-time uniform norm on the whole line. -/
theorem norm_extendCompactPath_le {T : ℝ} (hT : 0 ≤ T) {E : Type*}
    [NormedAddCommGroup E] [CompactSpace (Icc (0 : ℝ) T)]
    (u : ContinuousMap (Icc (0 : ℝ) T) E) (t : ℝ) :
    ‖extendCompactPath hT u t‖ ≤ ‖u‖ := by
  exact u.norm_coe_le_norm (clampTimeMap T hT t)

/-- The actual row-oriented H³ stress of the constant-at-the-ends path is globally bounded by its
compact-time trajectory radius. -/
theorem norm_tensorH3StressPath_extendCompactPath_le {c T : ℝ}
    (hc1 : 1 ≤ c) (hT : 0 ≤ T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (t : ℝ) :
    ‖tensorH3StressPath hc1 (extendCompactPath hT u) t‖ ≤ 1536 * ‖u‖ ^ 2 := by
  change ‖tensorH3Bilinear hc1 (extendCompactPath hT u t)
    (extendCompactPath hT u t)‖ ≤ _
  calc
    _ ≤ 1536 * ‖extendCompactPath hT u t‖ * ‖extendCompactPath hT u t‖ :=
      norm_tensorH3Bilinear_apply_le hc1 _ _
    _ ≤ 1536 * ‖u‖ ^ 2 := by
      have hu : ‖extendCompactPath hT u t‖ ≤ ‖u‖ := norm_extendCompactPath_le hT u t
      have hsq : ‖extendCompactPath hT u t‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hu
      calc
        1536 * ‖extendCompactPath hT u t‖ * ‖extendCompactPath hT u t‖ =
            1536 * ‖extendCompactPath hT u t‖ ^ 2 := by ring
        _ ≤ 1536 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)

#print axioms UnforcedLeray.TrainB.clampTimeMap
#print axioms UnforcedLeray.TrainB.extendCompactPath
#print axioms UnforcedLeray.TrainB.norm_tensorH3StressPath_extendCompactPath_le

end UnforcedLeray.TrainB
