import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_3
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.Inj
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.MultFun
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.Surj

/-!
# `nearFlatBoundC_of` (source 3560-3581, 3881-3887): the flat bound `NearFlatBoundC`

Assembles the two leaves of `Sub/PartIII-b_C_near_3.lean`:

* `nearD0Inj_of` (injectivity of `D₀`, `NearFlat/Inj.lean`);
* `nearD0Surj_of` (gained right inverse of `D₀`, `NearFlat/Surj.lean`), fed the function-level
  train multiplier bound `flatMultFunBound_of` (`NearFlat/MultFun.lean`).

`nearFlatBoundC_of_leaves` then gives `NearFlatBoundC`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **`nearFlatBoundC_of`**: the flat near bound `NearFlatBoundC` from the causal and stress
inputs of `IIIa` and the actual train multiplier bound `FlatTrainMultBound`. -/
theorem nearFlatBoundC_of (hPC : UnforcedLeray.Short.IIIa.PolyCausal)
    (hPS : UnforcedLeray.Short.IIIa.PolyStressCorollary)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) (hT : FlatTrainMultBound) :
    NearFlatBoundC :=
  nearFlatBoundC_of_leaves (nearD0Inj_of hPC) (nearD0Surj_of hPS hU (flatMultFunBound_of hT))

#print axioms nearFlatBoundC_of

end UnforcedLeray.Short.PartIIIb.NearInst
