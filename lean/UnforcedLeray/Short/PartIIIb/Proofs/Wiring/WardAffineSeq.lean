import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_3
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse

/-!
# `WardAffineSeq`: Ward stress normal form, physical affine identity and nilpotency along the sequence

Task `PartIII-b:IIIb-D5/3` (source `the November 2 reference manuscript` lines
4300-4303, 5001-5008, 5796-5814).

Assembles `wardAffineSeq` from `wardAffineSeq_of` and `UnforcedLeray.Short.IIIa.ctKineticImpulse`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardAffineSeq : UnforcedLeray.Short.PartIIIb.Concrete.Wiring.WardAffineSeq :=
  wardAffineSeq_of UnforcedLeray.Short.IIIa.ctKineticImpulse

end UnforcedLeray.Short.PartIIIb.Concrete
