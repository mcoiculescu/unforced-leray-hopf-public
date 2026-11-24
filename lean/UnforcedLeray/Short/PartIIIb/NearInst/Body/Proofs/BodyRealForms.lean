import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.SolenoidalConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.LiftVecConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.OuterSConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.T0Conj
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.ChartTransport

/-!
# Real forms of the body inverses (task `PartIII-b:C/near/body-real/5`)

Source `the November 2 reference manuscript` 1675-1677.  The leaves
`solenoidalConj`, `liftVecConj`, `outerSConj`, `t0Conj` and the recentring identities are
assembled by `bodyRealForms_of` and `tepsReal_of` (Body/Defs.lean).

The inverse recentring identity is taken from `ct_cellPtInvH` (ChartTransport.lean), because the
proof files `Masked/Proofs/CellPtH.lean` and `Masked/Proofs/CellPtInvH.lean` declare the same
names and cannot be imported together.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile cell)

/-- **Real forms of the body inverses** (source 1675-1677): `BodyRealForms`. -/
theorem bodyRealForms : UnforcedLeray.Short.PartIIIb.NearInst.BodyRealForms :=
  bodyRealForms_of solenoidalConj liftVecConj outerSConj t0Conj
    (fun c hc => UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc)
    (fun c hc => UnforcedLeray.Short.PartIIIb.NearInst.ct_cellPtInvH c hc)

/-- `T_ε` preserves real fields (`Masked.TepsReal`, source 1675-1677), from the leaves. -/
theorem tepsReal' : UnforcedLeray.Short.PartIIIb.NearInst.Masked.TepsReal :=
  tepsReal_of solenoidalConj liftVecConj outerSConj

end UnforcedLeray.Short.PartIIIb.NearInst.Body
