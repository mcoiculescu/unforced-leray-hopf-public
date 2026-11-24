import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.WeightInt
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Pointwise
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: the derivative passes under the centred integral

Source: `the November 2 reference manuscript` (SP) lines 2081-2084, 3052-3057.
Statement `BsrKcHasFDeriv` in `BSRep/Defs.lean`.

`bsrKcHasFDeriv_of : BsrWeightInt → BsrKcHasFDeriv`: `K_cω(z) = ∫_cell ω(z - y) K_c(y) dy`
(`Cyl.K_eq_reflect`), and `hasFDerivAt_integral_of_dominated_of_fderiv_le` on `Metric.ball x 1`
with the dominator `A 3^{β/2}(1 + (x₂ - y₂)²)^{-β/2}‖K_c(y)‖` (`1 + (x₂ - y₂)² ≤ 3(1 + (z₂ - y₂)²)`
for `|z₂ - x₂| < 1`), integrable by `BsrWeightInt` at `a = x₂`.

`tjTrainBSRep_of_train`: `TjTrainBSRep m` from the train leaves `TjTrainVort`, `TjVortDecay m`,
`TjLadGrad m`, `TjKcBound` alone.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem bsrKcHasFDeriv_of (hWI : BsrWeightInt) : BsrKcHasFDeriv := by
  intro c β A hc hβ g hg1 hper hA hA' x
  have hc0 : 0 < c := by linarith
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hKm : Measurable (UnforcedLeray.Cyl.bsKernel c) := UnforcedLeray.Cyl.measurable_bsKernel c
  have hK : UnforcedLeray.Cyl.K c g = fun z =>
      ∫ y in UnforcedLeray.Cyl.cell c, g (z - y) • UnforcedLeray.Cyl.bsKernel c y :=
    funext fun z => UnforcedLeray.Cyl.K_eq_reflect hc0 hper z
  rw [hK]
  -- the weighted bounds as upper bounds
  have hwpos : ∀ z : ℝ × ℝ, 0 < (1 + z.2 ^ 2) ^ (β / 2) := fun z =>
    Real.rpow_pos_of_pos (by positivity) _
  have hgb : ∀ z : ℝ × ℝ, |g z| ≤ A * (1 + z.2 ^ 2) ^ (-(β / 2)) := by
    intro z
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (hwpos z), mul_comm]
    exact hA z
  have hgb' : ∀ z : ℝ × ℝ, ‖fderiv ℝ g z‖ ≤ A * (1 + z.2 ^ 2) ^ (-(β / 2)) := by
    intro z
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (hwpos z), mul_comm]
    exact hA' z
  have hA0 : 0 ≤ A := (mul_nonneg (hwpos 0).le (abs_nonneg _)).trans (hA 0)
  -- comparison of the weights on the unit ball around `x`
  have hcmp : ∀ z y : ℝ × ℝ, z ∈ Metric.ball x 1 →
      (1 + (z - y).2 ^ 2) ^ (-(β / 2)) ≤ 3 ^ (β / 2) * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) := by
    intro z y hz
    have hz2 : |z.2 - x.2| < 1 := by
      have h := Metric.mem_ball.1 hz
      rw [Prod.dist_eq, Real.dist_eq] at h
      exact lt_of_le_of_lt (le_max_right _ _) h
    obtain ⟨hz2a, hz2b⟩ := abs_lt.1 hz2
    have hle : (1 + (x.2 - y.2) ^ 2) / 3 ≤ 1 + (z - y).2 ^ 2 := by
      rw [Prod.snd_sub, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      have hb : 0 < (1 - (z.2 - x.2)) * (1 + (z.2 - x.2)) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [sq_nonneg ((z.2 - y.2) - (x.2 - z.2)), sq_nonneg (z.2 - y.2), hb]
    calc (1 + (z - y).2 ^ 2) ^ (-(β / 2)) ≤ ((1 + (x.2 - y.2) ^ 2) / 3) ^ (-(β / 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = 3 ^ (β / 2) * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
            div_inv_eq_mul, mul_comm]
  have hbint : Integrable (fun y : ℝ × ℝ => A * 3 ^ (β / 2) *
      ((1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := (hWI c β hc hβ x.2).const_mul _
  have hL : Continuous (fun y : ℝ × ℝ => fderiv ℝ g (x - y)) :=
    (hg1.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z y => (fderiv ℝ g (z - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y))
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ hbint ?_
  · refine Eventually.of_forall (fun z => ?_)
    exact (hg1.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul
      hKm.aestronglyMeasurable
  · refine Integrable.mono' ((hWI c β hc hβ x.2).const_mul A)
      ((hg1.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul
        hKm.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have h := hgb (x - y)
    rw [Prod.snd_sub] at h
    calc |g (x - y)| * ‖UnforcedLeray.Cyl.bsKernel c y‖
        ≤ (A * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2))) * ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = A * ((1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖) := by ring
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) UnforcedLeray.Cyl.Vec2).continuous₂.comp_aestronglyMeasurable₂
      hL.aestronglyMeasurable hKm.aestronglyMeasurable
  · refine Eventually.of_forall (fun y z hz => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc ‖fderiv ℝ g (z - y)‖ * ‖UnforcedLeray.Cyl.bsKernel c y‖
        ≤ (A * (1 + (z - y).2 ^ 2) ^ (-(β / 2))) * ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
          mul_le_mul_of_nonneg_right (hgb' (z - y)) (norm_nonneg _)
      _ ≤ (A * (3 ^ (β / 2) * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)))) *
            ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcmp z y hz) hA0) (norm_nonneg _)
      _ = A * 3 ^ (β / 2) *
            ((1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖) := by ring
  · refine Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasFDerivAt (fun z : ℝ × ℝ => g (z - y)) (fderiv ℝ g (z - y)) z := by
      have h := (hgd (z - y)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    exact h1.smul_const (UnforcedLeray.Cyl.bsKernel c y)

/-- **`TjTrainBSRep m` from the train leaves alone** (all the kernel and calculus leaves of
`BSRep/Defs.lean` are proved in `BSRep/`). -/
theorem tjTrainBSRep_of_train (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hDec : TjVortDecay m)
    (hG : TjLadGrad m) (hKb : TjKcBound) : TjTrainBSRep m :=
  tjTrainBSRep_of_two m hm hV hDec hG hKb bsrWeightInt (bsrKcHasFDeriv_of bsrWeightInt)

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrKcHasFDeriv_of
#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of_train
