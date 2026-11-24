import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Nv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Profile
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Off-axis smoothness of the raw coefficient (task `PartIII-b:C/rep/8/2/pres/6/2/4`)

Source `the November 2 reference manuscript`
lines 1205-1225 (the lift is smooth through the axis for positive time).

Off the axis `U_raw = Params.raw = Nv ε⁻¹ (rawProfile ε v ψ)` (`Params.raw_eq_off_axis`), and the
profile `rawProfile` is `C^∞` on `Ioi 0 ×ˢ univ` for a BUC train (`rawProfile_contDiffOn_of`,
with the stream smooth by `PartI.trainStreamSmooth`), so the ring lift is `C^∞` off the axis
(`nv_contDiffOn`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **The raw coefficient is `C^∞` off the axis** (source 1205-1225). -/
theorem rawOffAxisSmooth_of (Pl : PlanarData) (L : ReturnLevel)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain L.train) : RawOffAxisSmooth Pl L := by
  have hR : L.ε⁻¹ ≠ 0 := (inv_pos.2 L.ε_pos).ne'
  have hS : UnforcedLeray.Short.PartI.TrainStreamSmooth :=
    UnforcedLeray.Short.PartI.trainStreamSmooth
  have hP := UnforcedLeray.Short.PartIIIb.rawProfile_contDiffOn_of hS L.ν_pos
    (cOf_pos L.ν_pos) L.train hb L.ε
  have hN := nv_contDiffOn L.ε⁻¹ hR _ hP
  refine hN.congr fun x hx => ?_
  have hy : x.2 ∉ axis := hx
  exact (L.params Pl).raw_eq_off_axis x.1 x.2 hy

end UnforcedLeray.Short.PartIIIb.Concrete
