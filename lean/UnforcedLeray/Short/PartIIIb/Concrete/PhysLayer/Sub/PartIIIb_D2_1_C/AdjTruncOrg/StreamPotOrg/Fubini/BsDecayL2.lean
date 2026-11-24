import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsDecayL2 : BSDecayL2 := by
  have hdim : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  have hint : Integrable (fun x : Space => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq hdim
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact (Continuous.inv₀ (by fun_prop) fun z => by positivity).aestronglyMeasurable
  · refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    have ha : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (inv_nonneg.mpr ha), show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num,
      Real.rpow_neg ha, Real.rpow_two, inv_pow]

end UnforcedLeray.Short.PartIIIb.Concrete
