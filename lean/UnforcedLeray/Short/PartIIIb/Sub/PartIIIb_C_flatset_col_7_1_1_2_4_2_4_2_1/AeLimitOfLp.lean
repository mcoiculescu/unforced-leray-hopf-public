import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# Part III-b, task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/19` (`aeLimitOfLp`)

Source of record `the November 2 reference manuscript`, lines 1744-1747 (density
argument): an `L²` limit agrees almost everywhere with a pointwise limit of representatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem aeLimitOfLp : AeLimitOfLp := by
  intro c X Y S T hX hXS hS
  have hTIM : TendstoInMeasure (measureH c) (fun N => ⇑(X N)) atTop ⇑Y :=
    tendstoInMeasure_of_tendsto_Lp hX
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  have hall : ∀ᵐ p ∂(measureH c), ∀ N, (X N : Profile → MeridC) p = S N p :=
    ae_all_iff.2 (fun N => hXS N)
  filter_upwards [hae, hall] with p hp1 hp2
  have h2 : Tendsto (fun k => S (ns k) p) atTop (𝓝 (T p)) :=
    (hS p).comp hns.tendsto_atTop
  have hfun : (fun k => S (ns k) p) = fun k => (X (ns k) : Profile → MeridC) p :=
    funext fun k => (hp2 (ns k)).symm
  have h3 : Tendsto (fun k => S (ns k) p) atTop (𝓝 (Y p)) := by
    rw [hfun]
    exact hp1
  exact tendsto_nhds_unique h3 h2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
