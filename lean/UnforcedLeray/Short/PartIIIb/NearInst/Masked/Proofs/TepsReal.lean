import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.SolenoidalConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.LiftVecConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.OuterSConj

/-!
# `T_ε` maps real fields to real fields (source 1675-1677)

Source of record: `the November 2 reference manuscript`.  `T_ε = R_ε^{vec}(μ) P_ε`
commutes with componentwise conjugation for real `μ > -1/4`: `P_ε` because the solenoidal subspace
is conjugation invariant (`solenoidalConj`), `R_ε^{vec}` because the lift and the outer
Ornstein-Uhlenbeck semigroup are real (`liftVecConj`, `outerSConj`).  Assembled in
`Body.tepsReal_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- `T_ε` preserves real fields (source 1675-1677). -/
theorem tepsReal : TepsReal :=
  Body.tepsReal_of Body.solenoidalConj Body.liftVecConj Body.outerSConj

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
