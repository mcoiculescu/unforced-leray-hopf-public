import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldYq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinIBP

/-!
# `GELin` (assembly, source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6`. Source of record
`the November 2 reference manuscript`
lines 2525-2533.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gELin : GELin := by
  unfold GELin GERegime
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, hok⟩ := rawSmoothBdd_ok (dp := dp) rawSmoothBdd hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hmode z g hd ⟨h, hh⟩ j
  have hU := hok p d hreg hν
  obtain ⟨F, hF⟩ := gELinFieldYq p z g h j hU
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [hF Φ hΦ.1]
  exact gELinIBP p z g h j hU.1 hd.2 (fun m => hh j m) Φ hΦ.1

end UnforcedLeray.Short.PartIIIb.Concrete
