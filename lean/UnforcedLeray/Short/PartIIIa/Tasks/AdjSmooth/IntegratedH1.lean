import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.SupL2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutLimit

/-!
# `PartIII-a:T21/2/7/2/2/1`: integrated `H¹` bound for the adjoint

Assembly of `adjointIntegratedH1_of` (`Sub/PartIII-a_T21_2_7_2_2_1.lean`) from the three
leaves `adjSupL2`, `adjCutRate`, `adjCutLimit` in `Sub/T21_2_7/IntH1/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjointIntegratedH1 (m : ℝ) (hm : 8 < m) : AdjointIntegratedH1 m :=
  adjointIntegratedH1_of m (adjSupL2 m hm) (adjCutRate m hm) (adjCutLimit m)

end UnforcedLeray.Short.IIIa
