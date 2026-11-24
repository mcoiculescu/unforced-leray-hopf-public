import UnforcedLeray.Short.PartI.Sub.T02_1_4_5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSobolevRep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.AePeriodicEq
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.JointSmoothOfHk.EvalHasFDerivAt

/-!
# Part I, task `PartI:T02/1/4/5`: assembly of `JointSmoothOfHk`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `JointSmoothOfHk` (`Short/PartI/Sub/T02_1_4.lean`, line 118), proved unconditionally by
composing the proved conditional theorem `jointSmoothOfHk_of` (`Short/PartI/Sub/T02_1_4_5.lean`)
with the three leaves:

* `cylSobolevRep : CylSobolevRep` (Sobolev embedding on the cell with derivative bounds);
* `aePeriodicEq : AePeriodicEq` (uniqueness of continuous periodic representatives);
* `evalFamilySmooth_of evalHasFDerivAt : EvalFamilySmooth` (`EvalHasFDerivAt` gives joint
  smoothness of evaluation families).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open Set Filter MeasureTheory

theorem jointSmoothOfHk : JointSmoothOfHk :=
  jointSmoothOfHk_of cylSobolevRep aePeriodicEq (evalFamilySmooth_of evalHasFDerivAt)

end UnforcedLeray.Short.PartI
