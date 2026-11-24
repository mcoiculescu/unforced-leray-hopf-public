import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2

/-!
# Decomposition of `gEQWeakDu` (source 2525-2531)

Same three leaves as `gEQWeakU` (`GEQInletWeak`, `GEQRepWeak`, `GEQWeakSum`): the second-order
inlet identity is the last conjunct of `GEQInletWeak`, the `w` part is `GEQHyp.1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params rep)

theorem gEQWeakDu_of (h1 : GEQInletWeak) (h2 : GEQRepWeak) (h3 : GEQWeakSum) : GEQWeakDu := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h1 lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hmode z g hd h hyp j k i
  obtain ⟨-, he, he', -, hw⟩ := H p d hreg hν hmode z g hd j k i
  obtain ⟨hr, hm, hm'⟩ := h2 p.period k (g j) (h j k) (hyp.1 j k) i
  have := h3 p.period k _ _ _ _ he he' hm hm' hw hr
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
