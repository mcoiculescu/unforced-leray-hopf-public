import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecay

/-!
# Sub-lemma for `PartIII-a:T21/c5/3/1/1`

The sharp decay `SeedLamPDSharpDecay κ` follows from `SeedLamPJet2Decay κ` (the `C²` regularity and
weighted first/second-jet decay `O((1+|z₁|+|z₂|)⁻²)` of the Part I seed dual kernels `κ.lamP j`;
source `the November 2 reference manuscript` lines
2891-2897 and 593-610, the seed functional `eq:short-seed-functional` and the Green representation
`eq:short-seed-green`).  The only missing input is the leaf `SeedLamPJet2Decay κ` for every `κ`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- Assembly of `SeedLamPDSharpDecay κ` from the Part I leaf `SeedLamPJet2Decay`. -/
theorem seedLamPDSharpDecay_from_jet (hJet : ∀ κ : PlanarFrameKernels, SeedLamPJet2Decay κ)
    (κ : PlanarFrameKernels) : SeedLamPDSharpDecay κ :=
  seedLamPDSharpDecay_of κ (hJet κ)

end UnforcedLeray.Short.IIIa
