import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# `L⁴` bound from inverse-distance decay on `ℝ³` (helper for `PartIII-b:C/ward/13/7/1`)

A field `G` on `ℝ³` with `‖G y‖ ≤ C (1+|y|)⁻¹` lies in `L⁴` with norm `≤ C·K`, `K` universal
(`(1+|y|)^{-4}` is integrable since `3 < 4`, `integrable_one_add_norm`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The model decay profile `(1+|y|)⁻¹` on `ℝ³`. -/
def decay1 : UnforcedLeray.Space → ℝ := fun y => (1 + ‖y‖)⁻¹

theorem memLp_decay1 : MemLp decay1 4 (volume : Measure UnforcedLeray.Space) := by
  have hm : AEStronglyMeasurable decay1 (volume : Measure UnforcedLeray.Space) :=
    (Measurable.aestronglyMeasurable (by unfold decay1; fun_prop))
  have hint : Integrable (fun y : UnforcedLeray.Space => (1 + ‖y‖) ^ (-(4 : ℝ)))
      (volume : Measure UnforcedLeray.Space) := by
    apply integrable_one_add_norm
    simp [finrank_euclideanSpace]
    norm_num
  have h1 : MemLp (fun x : UnforcedLeray.Space => ‖decay1 x‖ ^ (4 : ℝ≥0∞).toReal) (4 / 4)
      (volume : Measure UnforcedLeray.Space) := by
    rw [ENNReal.div_self (by norm_num) (by norm_num), memLp_one_iff_integrable]
    refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
    have hp : 0 < 1 + ‖y‖ := by positivity
    simp only [decay1, norm_inv, Real.norm_eq_abs, abs_of_pos hp, ENNReal.toReal_ofNat]
    rw [Real.rpow_neg hp.le, Real.inv_rpow hp.le]
  exact (memLp_norm_rpow_iff hm (by norm_num) (by norm_num)).mp h1

/-- Universal constant. -/
def decayK : ℝ := (eLpNorm decay1 4 (volume : Measure UnforcedLeray.Space)).toReal

/-- A field with `‖G y‖ ≤ C (1+|y|)⁻¹` has `L⁴` norm at most `C · decayK`. -/
theorem eLpNorm_le_of_decay {V : Type*} [NormedAddCommGroup V] (G : UnforcedLeray.Space → V)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, ‖G y‖ ≤ C * (1 + ‖y‖)⁻¹) :
    eLpNorm G 4 (volume : Measure UnforcedLeray.Space) ≤ ENNReal.ofReal (C * decayK) := by
  have hle : eLpNorm G 4 volume ≤ eLpNorm (C • decay1) 4 volume := by
    apply eLpNorm_mono
    intro y
    simp only [Pi.smul_apply, smul_eq_mul, decay1, norm_mul, Real.norm_eq_abs, norm_inv]
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [abs_of_pos hp, abs_of_nonneg hC]
    exact h y
  refine hle.trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC, decayK,
    ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal memLp_decay1.eLpNorm_lt_top.ne]

end UnforcedLeray.Short.PartIIIb.Concrete
