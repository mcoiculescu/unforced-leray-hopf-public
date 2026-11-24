import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld.Dense
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld.Box

/-!
# `PartIII-b:C/rep/4/1/org/6`: `χ_yS_Nχ_o = 0` (the full statement)

Source `the November 2 reference manuscript` 5303-5306, 3902-3920, 4163-4166.
The density of box stresses (`strBoxDenseAt_standing`, in `NearYoungOld.Dense`) and the box case
(`nearYoungOldBox`, in `NearYoungOld.Box`) give `NearYoungOldZero` by `nearYoungOldZero_of_box`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem nearYoungOldZero (dm dp : ℝ) : NearYoungOldZero dm dp :=
  nearYoungOldZero_of_box (nearYoungOldBox dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
