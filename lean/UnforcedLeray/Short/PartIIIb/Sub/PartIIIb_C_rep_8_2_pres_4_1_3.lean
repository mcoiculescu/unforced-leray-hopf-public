import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_2
import UnforcedLeray.Cons.L2.BackgroundConcrete.Fields

/-!
# Smoothness of the raw lift off the axis (task `PartIII-b:C/rep/8/2/pres/4/1/3`)

Source `the November 2 reference manuscript`
5200-5201. Off the axis the raw lift `U_raw` is the ring lift `Nv ε⁻¹` of the raw profile
`rawProfile ε v ψ` of the actual train (`Params.raw_eq_off_axis`), which is `C²` on
`Ioi 0 ×ˢ univ` (`rawProfile_contDiffOn`), so `Nv` of it is `C²` off the axis
(`nv_contDiffOn_offAxis`).
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/3`.** The raw lift `U_raw` of the actual train is `C²`
jointly in `(τ, y)` off the axis, given that the stream is `C³` on `Ioi 0 ×ˢ univ`. -/
theorem rawU_contDiffOn_offAxis_of (p : Params) (hε : 0 < p.ε) (hψ : ContDiffOn ℝ 3 (fun x : ℝ × Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis := by
  have hR : 0 < p.ε⁻¹ := inv_pos.2 hε
  have hb : ContDiffOn ℝ 2 (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      (Ioi 0 ×ˢ univ) :=
    rawProfile_contDiffOn p.train.isTrain hψ
  have hN := nv_contDiffOn_offAxis hR hb
  exact hN.congr fun x hx => p.raw_eq_off_axis x.1 x.2 hx

end UnforcedLeray.Short.PartIIIb.Concrete
