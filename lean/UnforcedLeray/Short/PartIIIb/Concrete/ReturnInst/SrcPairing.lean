import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.SrcPairing.Lift

/-!
# Body forces are determined by their phase pairings: `srcPairingNondeg`

Source of record: `the November 2 reference manuscript` (73 pages), lines
2666-2689 (cylinder chart, `H = L²(s^{-3/2} dς)`, the lift identity
`‖𝒩_v b‖²_{Y_2} = πR²‖b‖²_H`) and 5001-5008 (Lemma `ret:physical-affine`: the physical identity
against all phase tests determines `𝔯_A`).

`srcPairingNondeg : SrcPairingNondeg` (`Concrete/ReturnInst.lean`, consumed by `isRAOp_unique`
and `concreteReturnSeq_rA_le`) is `SrcPairing.sp_nondeg` of `ReturnInst/SrcPairing/Lift.lean`:
the lifts `𝒩_v f` of body forces lie in `Y_2` with `R⁻¹‖𝒩_v f‖_{Y_2} = √π‖f‖_H` (2683-2689),
phase tests separate points of `Y_2` (`IIb.phaseFundamental`), and the norm identity for `f - g`
gives `f = g` in `SrcG c`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`SrcPairingNondeg`** (source 2666-2689, 5001-5008): body forces `f, g ∈ SrcG c` whose lifts
`velPhys ε⁻¹ c f`, `velPhys ε⁻¹ c g` have the same pairing `pairF (2εc) Φ` with every phase test
`Φ` are equal. -/
theorem srcPairingNondeg : SrcPairingNondeg :=
  fun c ε hc hε f g hpair => SrcPairing.sp_nondeg c ε hc hε f g hpair

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.srcPairingNondeg
