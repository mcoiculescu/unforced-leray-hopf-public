import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatLerayRep
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem

/-!


Source of record: `the November 2 reference manuscript`, lines 1800-1836.

Assembles `adjointPolynomialBound` from `adjointPolynomialBound_of`, `flatLeraySmoothRep`,
and `flatAdjointElementaryBound`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem adjointPolynomialBound : AdjointPolynomialBound :=
  adjointPolynomialBound_of flatLeraySmoothRep flatAdjointElementaryBound

end UnforcedLeray.Short.PartIIa
