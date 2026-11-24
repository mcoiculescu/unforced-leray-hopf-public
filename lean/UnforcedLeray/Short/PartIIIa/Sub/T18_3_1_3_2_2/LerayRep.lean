import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.LerayRepH1

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/2`: `LMDerivRepAE`, unconditional

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
`IsLMMollifier` now carries `gradL2` and `divFreeWeak`, which are the two fields of `LMMollH1`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **`LMDerivRepAE`** (SP 3427-3440, 3541-3552). -/
theorem lmDerivRepAE : LMDerivRepAE :=
  fun c ν μ F b G hS J hJ hE k =>
    lmDerivRepAEH1 c ν μ F b G hS J hJ ⟨hJ.gradL2, hJ.divFreeWeak⟩ hE k

end UnforcedLeray.Short.IIIa
