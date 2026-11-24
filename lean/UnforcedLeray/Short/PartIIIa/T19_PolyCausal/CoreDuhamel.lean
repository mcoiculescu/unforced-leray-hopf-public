import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.CurlDuality
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.BiotSavartH1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation

/-!
# `PartIII-a:T19/2`: `CoreDuhamelBiotSavart`

Source of record: `the November 2 reference manuscript` lines 3456-3515.
Assembles `coreDuhamelBiotSavart` from `coreDuhamelBiotSavart_of`, `coreCurlDuality`,
`coreBiotSavartH1Uniform`, and `coreDuhamelPropagation`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem coreDuhamelBiotSavart : UnforcedLeray.Short.IIIa.CoreDuhamelBiotSavart :=
  coreDuhamelBiotSavart_of coreCurlDuality coreBiotSavartH1Uniform coreDuhamelPropagation

end UnforcedLeray.Short.IIIa
