import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF2.Kf2a
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF2.Kf2b1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF2.Kf2b2

/-!
# `kf2 : KF2pos` (source 3613, "In its Laplace integral")

Assembly of the three leaves `kf2a`, `kf2b1`, `kf2b2` and `kf1 : KF1` (`KF1` of `Sub1` has the
body of `KF1pos`, with the hypothesis `0 < ν * ε ^ 2`) through `kf2pos_of` of `Sub2`.
Source of record: `the November 2 reference manuscript`
(line 3613).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- **KF2pos** (3613): `physRes` is the pointwise a.e. Laplace integral of the explicit outer
semigroup, for `ν > 0`, `ε > 0`. -/
theorem kf2 : KF2pos :=
  kf2pos_of kf1 kf2a kf2b1 kf2b2

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
