import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Deriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Cont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Real
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Convert

/-!
# `PartIII-a:T21/2/7/2/2/1/2/6`: `AdjCutRate` from the five leaves (a)-(e)

Composes `adjCutRate_of` (in `PartIII-a_T21_2_7_2_2_1_2`) with the leaf proofs
`adjCutE0Deriv` (a), `adjCutE0Cont` (b), `adjCutE0Lower` (c), `adjCutRateReal` (d),
`adjCutConvert` (e). Source: SP lines 3060-3067.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T21/2/7/2/2/1/2/6`**: `AdjCutRate` for `m > 8`, from leaves (a)-(e). -/
theorem adjCutRate (m : ℝ) (hm : 8 < m) : AdjCutRate m :=
  adjCutRate_of m hm (adjCutE0Deriv m) (adjCutE0Cont m) (adjCutE0Lower m)
    (adjCutRateReal m) (adjCutConvert m)

end UnforcedLeray.Short.IIIa
