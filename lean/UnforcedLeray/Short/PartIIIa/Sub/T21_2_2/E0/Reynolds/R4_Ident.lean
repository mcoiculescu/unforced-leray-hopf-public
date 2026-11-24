import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R4_Pointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R4_IntegrableRe
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R4_IntegrableA

/-!
# `PartIII-a:T21/2/2/2/2/4`: `ReyIdent` from its three leaves (SP 2860, 2945-2946, 3060-3062)

Assembly only: `reyIdent_of` applied to `reyPointwise`, `reyIntegrableRe`, `reyIntegrableA`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.E0

/-- **R4/R6: integrability and identification with `rate0`** (SP 2860, 2945-2946, 3060-3062),
assembled from the three leaves. -/
theorem reyIdent (m : ℝ) (hm : 8 < m) (hc : UnforcedLeray.Short.IIIa.E0.ReyChain) :
    UnforcedLeray.Short.IIIa.E0.ReyIdent m :=
  reyIdent_of m hm (reyPointwise m hm hc) (reyIntegrableRe m hm) (reyIntegrableA m hm)

end UnforcedLeray.Short.IIIa.E0
