import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQWeakU
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQWeakDu
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem

/-!
# `GEQIbp`: weak integration by parts for the quadratic term (source 2525-2533)

Assembly of `gEQIbp_core` (`GEQIbp/Core.lean`) from the accepted regime facts `gEQWeakU`,
`gEQWeakDu`, `gEQMem`.  The regime bounds are combined by taking the minimum.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQIbp : GEQIbp := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := gEQWeakU lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := gEQWeakDu lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := gEQMem lam q hq dm dp hdm
  refine ⟨min n1 (min n2 n3), lt_min hn1 (lt_min hn2 hn3), ?_⟩
  intro p d hreg hν hmode z g hd
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ n3 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  intro h hyp j Φ hΦ
  have hU := H1 p d hreg e1 hmode z g hd h hyp
  have hD := H2 p d hreg e2 hmode z g hd h hyp
  obtain ⟨hMu, hMd, hMdd⟩ := H3 p d hreg e3 hmode z g hd h hyp
  exact gEQIbp_core (P := p.period) (U := fun i x => p.uOf z x i)
    (D := fun a b x => GEQDu p z g a x b) (DD := fun a b c x => GEQDdu p z g h a b x c)
    hMu hMd hMdd (fun a b => hU a b) (fun a b c => hD a b c) Φ hΦ j

end UnforcedLeray.Short.PartIIIb.Concrete
