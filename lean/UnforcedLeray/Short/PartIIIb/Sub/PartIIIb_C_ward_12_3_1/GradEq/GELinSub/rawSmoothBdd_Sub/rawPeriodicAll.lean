import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas

/-!
# `rawPeriodicAll` (task `PartIII-b:C/ward/12/3/1/2/6/1/2`)

Source `the November 2 reference manuscript`
lines 1215-1217.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete (Params)

private theorem raw_periodic_off {p : Params} (τ : ℝ) {y : UnforcedLeray.Space}
    (hy : y ∉ UnforcedLeray.Axi.axis) :
    p.raw (τ + p.period) y = p.raw τ y := by
  rw [p.raw_eq_off_axis _ y hy, p.raw_eq_off_axis _ y hy]
  refine UnforcedLeray.Cons.C03.Nv_add_period_of_not_mem_axis (c := p.c) p.R_pos.ne' ?_ ?_ τ hy
  · show 2 * p.ε * p.c = 2 * p.c / p.ε⁻¹
    field_simp
  · intro s hs ξ η
    exact UnforcedLeray.Cons.C03.rawProfile_periodic p.train hs ξ η

theorem rawPeriodicAll : RawPeriodicAll := by
  intro dm dp _
  refine ⟨1, one_pos, fun p d _ _ τ y => ?_⟩
  by_cases hy : y ∈ UnforcedLeray.Axi.axis
  · have hev : (UnforcedLeray.Axi.Nv p.R
        (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (τ + p.period)) =ᶠ[𝓝[UnforcedLeray.Axi.axisᶜ] y]
        (UnforcedLeray.Axi.Nv p.R
          (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 := raw_periodic_off (p := p) τ hz
      rwa [p.raw_eq_off_axis _ z hz, p.raw_eq_off_axis _ z hz] at h1
    show UnforcedLeray.Cons.C03.Concrete.axisExt _ y = UnforcedLeray.Cons.C03.Concrete.axisExt _ y
    unfold UnforcedLeray.Cons.C03.Concrete.axisExt
    simp only [hy, ↓reduceIte]
    simp only [limUnder]
    rw [Filter.map_congr hev]
  · exact raw_periodic_off τ hy

#print axioms rawPeriodicAll

end UnforcedLeray.Short.PartIIIb.Concrete
