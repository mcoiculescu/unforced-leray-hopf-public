import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Defs
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: the kernel against a transverse weight is integrable

Source: `the November 2 reference manuscript` (SP) lines 2117-2121, 3052-3057
(integrable near part, bounded far part). Statement `BsrWeightInt` in `BSRep/Defs.lean`.

`bsrWeightInt : BsrWeightInt`: on the cell `K_c = k_near + k_far` (`Cyl.bsKernel_split`); the
weight is `≤ 1` against `‖k_near‖` (integrable), and `‖k_far‖ ≤ 2` against the weight, whose cell
integral is `c ∫_ℝ (1 + s²)^{-β/2} ds < ∞` (`integrable_rpow_neg_one_add_norm_sq`,
`Integrable.mul_prod`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem bsrWeightInt : BsrWeightInt := by
  intro c β hc hβ a
  obtain ⟨C₀, -, hsplit⟩ := UnforcedLeray.Cyl.bsKernel_split
  obtain ⟨hnear, hfar, hsum⟩ := hsplit c hc
  have hwnn : ∀ t : ℝ, 0 ≤ (1 + t ^ 2) ^ (-(β / 2)) := fun t => Real.rpow_nonneg (by positivity) _
  have hw1 : ∀ t : ℝ, (1 + t ^ 2) ^ (-(β / 2)) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by linarith)
  -- the near part is integrable on the cell
  have hkNm : Measurable (UnforcedLeray.Cyl.kNear c) :=
    (UnforcedLeray.Cyl.measurable_bsKernel c).indicator
      ((UnforcedLeray.Cyl.measurableSet_cell c).inter Metric.isOpen_ball.measurableSet)
  have hg1 : IntegrableOn (fun y : ℝ × ℝ => ‖UnforcedLeray.Cyl.kNear c y‖)
      (UnforcedLeray.Cyl.cell c) := by
    refine ⟨hkNm.norm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [enorm_norm]
    exact lt_of_le_of_lt hnear ENNReal.ofReal_lt_top
  -- the weight is integrable on the cell
  have hg2 : IntegrableOn (fun y : ℝ × ℝ => (1 + (a - y.2) ^ 2) ^ (-(β / 2)))
      (UnforcedLeray.Cyl.cell c) := by
    have h2 : Integrable (fun t : ℝ => (1 + (a - t) ^ 2) ^ (-(β / 2))) := by
      have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := β)
        (by simpa using hβ)
      refine (h0.comp_sub_right a).congr (Eventually.of_forall fun t => ?_)
      simp only [Real.norm_eq_abs, sq_abs, neg_div]
      ring_nf
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (-c / 2) (c / 2))) :=
      integrable_const 1
    have hcell : UnforcedLeray.Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := rfl
    rw [IntegrableOn, hcell, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ]
    simpa using h1.mul_prod h2
  -- domination on the cell
  have hwc : Continuous (fun y : ℝ × ℝ => (1 + (a - y.2) ^ 2) ^ (-(β / 2))) :=
    (continuous_const.add ((continuous_const.sub continuous_snd).pow 2)).rpow_const
      (fun y => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
  refine Integrable.mono' (hg1.add (hg2.const_mul 2)) ?_ ?_
  · exact (hwc.measurable.mul (UnforcedLeray.Cyl.measurable_bsKernel c).norm).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwnn _) (norm_nonneg _)), hsum y hy]
    calc (1 + (a - y.2) ^ 2) ^ (-(β / 2)) *
          ‖UnforcedLeray.Cyl.kNear c y + UnforcedLeray.Cyl.kFar c y‖
        ≤ (1 + (a - y.2) ^ 2) ^ (-(β / 2)) *
          (‖UnforcedLeray.Cyl.kNear c y‖ + ‖UnforcedLeray.Cyl.kFar c y‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hwnn _)
      _ ≤ 1 * ‖UnforcedLeray.Cyl.kNear c y‖ + (1 + (a - y.2) ^ 2) ^ (-(β / 2)) * 2 := by
          rw [mul_add]
          exact add_le_add (mul_le_mul_of_nonneg_right (hw1 _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hfar y) (hwnn _))
      _ = ‖UnforcedLeray.Cyl.kNear c y‖ + 2 * (1 + (a - y.2) ^ 2) ^ (-(β / 2)) := by ring

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrWeightInt
