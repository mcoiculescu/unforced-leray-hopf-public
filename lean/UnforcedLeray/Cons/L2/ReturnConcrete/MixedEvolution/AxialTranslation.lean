import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedKernel
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeat

/-!
# Axial weight control under translations

The axial weight is periodic in the cylinder coordinate. These pointwise estimates bound the
conjugating multiplier for axial translations uniformly for shifts in a bounded set; they are
the domination input for weighted translation continuity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)

/-- The Peetre bound for the axial weight at a translated point. -/
theorem axialWeight_translate_le {m : ℝ} (hm : 0 ≤ m) (x w : Plane) :
    axialWeight m x ≤ 2 ^ (m / 2) * axialWeight m (x - w) * axialWeight m w := by
  simpa [axialWeight, axialBracket] using axialBracket_rpow_le_peetre hm x w

/-- If the translation length is at most one, the axial weight ratio is uniformly bounded by
`2^m`. This bound is independent of the point being translated. -/
theorem axialWeight_translate_ratio_le {m : ℝ} (hm : 0 ≤ m) {x w : Plane}
    (hw : ‖w‖ ≤ 1) :
    axialWeight m x ≤ (2 : ℝ) ^ m * axialWeight m (x - w) := by
  have hpeetre := axialWeight_translate_le hm x w
  have hweight : axialWeight m w ≤ (2 : ℝ) ^ (m / 2) := by
    rw [axialWeight, axialBracket_rpow]
    have hwη : |w.2| ≤ 1 := by
      have h := (norm_snd_le w).trans hw
      simpa only [Real.norm_eq_abs] using h
    have hwSq : w.2 ^ 2 ≤ 1 := by
      have hsq := (sq_le_sq₀ (abs_nonneg w.2)
        (by norm_num : 0 ≤ (1 : ℝ))).2 hwη
      simpa only [sq_abs, one_pow] using hsq
    have hbase : 1 + w.2 ^ 2 ≤ 2 := by linarith
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hconst : 0 ≤ (2 : ℝ) ^ (m / 2) := Real.rpow_nonneg (by norm_num) _
  calc
    axialWeight m x ≤ (2 : ℝ) ^ (m / 2) * axialWeight m (x - w) * axialWeight m w := hpeetre
    _ ≤ (2 : ℝ) ^ (m / 2) * axialWeight m (x - w) * (2 : ℝ) ^ (m / 2) := by
      have hAx : 0 ≤ axialWeight m (x - w) := by
        dsimp [axialWeight, axialBracket]
        positivity
      exact mul_le_mul_of_nonneg_left hweight
        (mul_nonneg hconst hAx)
    _ = ((2 : ℝ) ^ (m / 2) * (2 : ℝ) ^ (m / 2)) * axialWeight m (x - w) := by ring
    _ = (2 : ℝ) ^ m * axialWeight m (x - w) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- The pointwise multiplier ratio is continuous at zero for each fixed cylinder point. -/
theorem continuousAt_axialWeight_translate_ratio {m : ℝ} (hm : 0 ≤ m) (x : Plane) :
    ContinuousAt (fun w : Plane => axialWeight m x / axialWeight m (x - w)) 0 := by
  have hsub : ContinuousAt (fun w : Plane => x - w) 0 :=
    continuousAt_const.sub continuousAt_id
  have hden : ContinuousAt (fun w : Plane => axialWeight m (x - w)) 0 :=
    (continuous_axialWeight m).continuousAt.comp hsub
  have hpos : axialWeight m (x - (0 : Plane)) ≠ 0 := by
    dsimp [axialWeight, axialBracket]
    positivity
  exact continuousAt_const.div hden hpos
end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_translate_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_translate_ratio_le
