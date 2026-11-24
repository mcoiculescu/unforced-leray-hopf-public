import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F10
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique

/-!
# Part II-b, `PartII-b:G2/1/org/B2`: `PhysKOutUnique`

Two outputs `g, g'` of the same `b` have equal phase pairings of their ring lifts
(`IsKOut`, SP 2007-2010); `profileUnique` (density of phase tests, SP 1902-1906, 2370-2382) gives
`toProf g =ᵐ toProf g'`, and `toProf_eq_of_ae_eq` gives `g = g'`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

theorem physKOutUnique : PhysKOutUnique := by
  intro p _ hc _ b g g' _ hg hg'
  have h := profileUnique p.c p.ε hc ‹0 < p.ε› (toProf p.c g) (toProf p.c g')
    (RespOp.inHr_toProf hc g) (RespOp.inHr_toProf hc g') (fun Φ hΦ => by
      have e1 := hg Φ hΦ
      have e2 := hg' Φ hΦ
      exact e1.symm.trans e2)
  exact toProf_eq_of_ae_eq hc h

end UnforcedLeray.Short.IIb
