import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.Meas
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.Bound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.FlowNormBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.PairBound

/-!


Source: `the November 2 reference manuscript`
(SP 2074-2105). The three hypotheses of `cylTdRhsCont_of` are supplied by the
measurability, pointwise and uniform-bound lemmas in `N1/Approx/RhsCont/`.
-/

open UnforcedLeray.Short.IIb in
theorem cylTdRhsCont : UnforcedLeray.Short.IIb.CylTdRhsCont :=
  cylTdRhsCont_of cylTdRhsMeas cylTdRhsPointwise cylTdRhsBound
