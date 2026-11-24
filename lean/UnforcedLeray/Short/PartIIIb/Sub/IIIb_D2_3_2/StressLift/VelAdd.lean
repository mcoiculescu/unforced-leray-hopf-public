import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs

/-!
# Additivity of the body velocity coercion a.e. for `ageμ c (-1/2)` (source 2666-2700)

The coercion `VelG c γ ν → (Chart → Merid)` is additive `ageμ c (-1/2)`-a.e.: the body measure
`bodyMeasure c γ ν = ageμ c (-3/2).withDensity (π g⁻²)` has a.e. nonzero density, so
`ageμ c (-3/2) ≪ bodyMeasure`, and `ageμ c (-1/2) ≪ ageμ c (-3/2)` by `ageμ_absCont`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageμ_neg_half_absCont_body (c γ ν : ℝ) :
    ageμ c (-1 / 2) ≪ bodyMeasure c γ ν := by
  refine (NearInst.ageμ_absCont c (-1 / 2) (-3 / 2)).trans ?_
  unfold bodyMeasure
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp
      ((measurable_const.mul ((NearInst.ginv_measurable' γ ν).pow_const 2)))).aemeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    have hg := NearInst.ginv_pos' γ ν p
    positivity

theorem velAddAE_proved (c γ ν : ℝ) : VelAddAE c γ ν := by
  intro u v
  exact (ageμ_neg_half_absCont_body c γ ν).ae_le (Lp.coeFn_add u v)

end UnforcedLeray.Short.PartIIIb.Concrete
