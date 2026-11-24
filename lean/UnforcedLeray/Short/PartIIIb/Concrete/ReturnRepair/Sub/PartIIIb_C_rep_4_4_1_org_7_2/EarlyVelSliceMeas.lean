import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.VelPairAE
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A1

/-!
# Proof of the leaf `EarlyVelSliceMeas` (`PartIII-b:C/rep/4/4/1/org/7/2/2`, source 2683)

As `velSliceMeas` (`PartIII-b:C/rep/1/3`) with `w` replaced by `earlyTrunc ν w`. The truncated
field agrees a.e. with the measurable function `G'' p = if νs ≤ 3/2 then G' p else 0`, where `G'`
is a measurable representative of `w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf `EarlyVelSliceMeas`** (source 2683): the phase slices of the early-truncated `𝒩_v w`
are a.e.-strongly measurable for a.e. phase in the cell. -/
theorem earlyVelSliceMeas : EarlyVelSliceMeas := by
  intro Pl L w
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by
    rw [div_inv_eq_mul]; ring
  -- a measurable representative of the body field
  have hw : AEStronglyMeasurable (w : Chart → Merid)
      (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) := Lp.aestronglyMeasurable w
  obtain ⟨G', hG'm, hG'eq⟩ : ∃ G' : Chart → Merid, Measurable G' ∧
      (w : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν] G' :=
    ⟨AEStronglyMeasurable.mk (w : Chart → Merid) hw, hw.measurable_mk, hw.ae_eq_mk⟩
  -- the early-truncated measurable representative
  set G'' : Chart → Merid := fun p => if L.ν * p.1 ≤ 3 / 2 then G' p else 0 with hG''def
  have hG''m : Measurable G'' :=
    Measurable.ite (measurableSet_le (measurable_const.mul measurable_fst) measurable_const)
      hG'm measurable_const
  have hB' : earlyTrunc L.ν (w : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν] G'' := by
    filter_upwards [hG'eq] with p hp
    simp only [earlyTrunc, hG''def, hp]
  have h1 : earlyTrunc L.ν (w : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)] G'' := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
    exact hB'
  have hB : ageμ (cOf L.ν) (-3 / 2) {p : Chart | ¬ (earlyTrunc L.ν (w : Chart → Merid) p = G'' p)}
      = 0 :=
    ae_iff.1 h1
  set N := toMeasurable (ageμ (cOf L.ν) (-3 / 2))
    {p : Chart | ¬ (earlyTrunc L.ν (w : Chart → Merid) p = G'' p)} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : ageμ (cOf L.ν) (-3 / 2) N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact hB
  have hN5 : ageμ (cOf L.ν) (-5 / 2) N = 0 := NearInst.ageμ_absCont (cOf L.ν) (-5 / 2) (-3 / 2) hN0
  -- transfer to the cell in `(τ, y)`
  have hpt := NearInst.stressPairAE_null L.ε⁻¹ (cOf L.ν) (2 * L.ε * cOf L.ν) hR hc hP N hNm hN5
  have h5 : ∀ᵐ x ∂((volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))).prod (volume : Measure Space)),
      velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν (w : Chart → Merid)) x =
        velPhys L.ε⁻¹ (cOf L.ν) G'' x := by
    filter_upwards [hpt] with x hx
    apply NearInst.velPhys_congr_chart hR hc _ _ x
    by_contra hne
    exact hx (subset_toMeasurable _ _ hne)
  have h6 := Measure.ae_ae_of_ae_prod h5
  filter_upwards [h6] with τ hτ
  have hτ' : (fun y : Space => velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν (w : Chart → Merid)) (τ, y))
      =ᵐ[volume] (fun y : Space => velPhys L.ε⁻¹ (cOf L.ν) G'' (τ, y)) := hτ
  have hm : Measurable (velPhys L.ε⁻¹ (cOf L.ν) G'') :=
    fwuA1_measurable_velPhys L.ε⁻¹ (cOf L.ν) hG''m
  exact ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).congr hτ'.symm

end UnforcedLeray.Short.PartIIIb.Concrete
