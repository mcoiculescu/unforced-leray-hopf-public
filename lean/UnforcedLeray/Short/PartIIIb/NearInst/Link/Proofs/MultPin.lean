import UnforcedLeray.Short.PartIIIb.NearInst.Link.Clauses

/-!
# The multiplier pin from the link (source 2706, 3876-3878, 5779-5782)

Proof of `MultPinOfLink` (`NearInst/Link/Clauses.lean`), the converse of `MultLinkOf`: if the split
multiplier `M_U` of the near layer is `IsSplitMult` and the return base multiplier is `o.MG`, then
the return base satisfies the exact-multiplier pin `IsExactMultiplier`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

theorem multPinOfLink : MultPinOfLink := by
  intro c mZ ρb γ ν hν Aff _ _ _ B o R V rb hS hM
  unfold IsExactMultiplier
  intro w
  rw [hM]
  have hacZ : gainZ1Measure c mZ γ ν ≪ ageμ c (-3 / 2) :=
    (root_gainZ1 c mZ γ ν).absCont'.trans
      ((root_z1 c mZ).absCont'.trans (ageμ_absCont c (-1 / 2) (-3 / 2)))
  have hR : htRhoMeasure c ρb ≪ ageμ c (-1 / 2) := by
    unfold htRhoMeasure
    exact Measure.smul_absolutelyContinuous
  have hacH : gainHTMeasure c ρb γ ν ≪ ageμ c (-3 / 2) :=
    (root_gainHT c ρb γ ν).absCont'.trans (hR.trans (ageμ_absCont c (-1 / 2) (-3 / 2)))
  constructor
  · filter_upwards [coeFn_MG_fst o γ hν w,
      (root_gainZ1 c mZ γ ν).absCont'.ae_le
        (hS ((Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν w))).1,
      hacZ.ae_le (coeFn_hOfVel γ hν w)] with p h1 h2 h3
    rw [h1, h2, h3]
  · filter_upwards [coeFn_MG_snd o γ hν w,
      (root_gainHT c ρb γ ν).absCont'.ae_le
        (hS ((Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν w))).2,
      hacH.ae_le (coeFn_hOfVel γ hν w)] with p h1 h2 h3
    rw [h1, h2, h3]

end UnforcedLeray.Short.PartIIIb.NearInst
