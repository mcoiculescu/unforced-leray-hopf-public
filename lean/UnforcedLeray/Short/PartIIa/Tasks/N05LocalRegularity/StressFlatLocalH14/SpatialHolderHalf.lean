import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.Final

/-!


Source of record: `the November 2 reference manuscript`, lines 1757-1758, 1785-1788.
The two 1D leaves (weak derivative in `L²` implies translation bound) are proved in
`SpatialHolderHalf/Final.lean` by the duality argument: for a smooth periodic test `φ`,
`∫⟨u(·+h e) - u, φ⟩ = ∫⟨∫_0^h dq(·+t e) dt, φ⟩`, and the fundamental lemma of the calculus of
variations on the open cell gives the pointwise identity a.e.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem flatStressSpatialHolderHalf : UnforcedLeray.Short.PartIIa.FlatStressSpatialHolderHalf :=
  flatStressSpatialHolderHalf_of cellWeakQDiffQuotient cellWeakEtaDiffQuotient

end UnforcedLeray.Short.PartIIa
