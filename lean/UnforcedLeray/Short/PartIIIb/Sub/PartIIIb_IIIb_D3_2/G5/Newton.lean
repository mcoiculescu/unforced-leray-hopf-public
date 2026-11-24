import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonSigmaSymm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonSigmaPolar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonSigmaMom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonD3tDiff

/-!
# Assembly for `newtonTaylor` (`PartIII-b:IIIb-D3/2/G5/2`)

Source: `the November 2 reference manuscript` lines 4859–4901.
Assembles `newtonTaylor` from `newtonTaylor_of` (`NewtonOrg.lean`) and the four leaf files
`NewtonSigmaSymm`, `NewtonSigmaPolar`, `NewtonSigmaMom`, `NewtonD3tDiff`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

theorem newtonTaylor (as : ℝ) (K : Set ℝ) (chio chiy : ℝ → ℝ) :
    FlatUnif.G5.NewtonTaylor as K chio chiy :=
  newtonTaylor_of as K chio chiy (sigmaIntSymm chio) (sigmaIntPolar chio)
    (sigmaMFirstMoment chio) d3tDiffBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
