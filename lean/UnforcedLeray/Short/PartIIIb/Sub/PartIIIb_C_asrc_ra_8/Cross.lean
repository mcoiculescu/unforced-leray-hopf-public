import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.All

/-!
# `PartIII-b:C/asrc/ra/8/2` : the cross-center bound `RCrossBound`

Source `the November 2 reference manuscript`
5026-5031 (distinct-center products, cross-center cell norms `≤ C δ_base M(A) s^{5/2}`), 4371
(`δ_base`).  The statement is `RCrossBound` of the parent file; the proof is the assembled bound
`rcCrossBound_assembled` of `Cross/All.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rCrossBound (as : ℝ) (χf : ℝ → ℝ) : RCrossBound as χf :=
  rcCrossBound_assembled as χf

end UnforcedLeray.Short.PartIIIb.Concrete
