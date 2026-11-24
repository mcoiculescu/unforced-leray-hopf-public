import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.BiotSavartSlice
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity

/-!
# Part III-a, task `PartIII-a:T19/2/3`: forward Duhamel propagation and core velocity equation

Source of record: `the November 2 reference manuscript` (SP), lines 3489-3515
(Steps P3-Duhamel and P4: forward Duhamel vorticity propagation and core velocity equation).

The submodule `UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T19_2_3»` proves
`coreDuhamelPropagation_of`, the assembly of `CoreDuhamelPropagation` from the leaf propositions
`CoreBiotSavartSliceBound` (`PartIII-a:T19/2/3/1`) and `CoreDuhamelVorticityBound`
(`PartIII-a:T19/2/3/2`), using the train causal solution of `trainCausalExistence` and the
null-set modification `isCoreCausalSolution_of_nullKeep`.

The helper `Propagation/BiotSavartSlice.lean` proves the first leaf,
`coreBiotSavartSliceBound : CoreBiotSavartSliceBound` (SP 3497-3515: the velocity is the
Biot-Savart velocity of its curl by `CTE.isBiotSavart_unique`, its gradient is unique by
`weakCellAeUnique`).

What remains is the second leaf, the forward Duhamel vorticity bound (SP 3489-3496):
`theorem coreDuhamelVorticityBound : UnforcedLeray.Short.IIIa.CoreDuhamelVorticityBound`.
Given it, `coreDuhamelPropagation_of_vorticityBound coreDuhamelVorticityBound` is the target
`coreDuhamelPropagation : UnforcedLeray.Short.IIIa.CoreDuhamelPropagation`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **`CoreDuhamelPropagation` from the forward Duhamel vorticity bound** (`PartIII-a:T19/2/3`,
SP 3489-3515): the Biot-Savart slice leaf is proved (`coreBiotSavartSliceBound`), so the only
remaining input is `CoreDuhamelVorticityBound` (leaf `PartIII-a:T19/2/3/2`, SP 3489-3496). -/
theorem coreDuhamelPropagation_of_vorticityBound (hVort : CoreDuhamelVorticityBound) :
    CoreDuhamelPropagation :=
  coreDuhamelPropagation_of coreBiotSavartSliceBound hVort

theorem coreDuhamelPropagation : UnforcedLeray.Short.IIIa.CoreDuhamelPropagation :=
  coreDuhamelPropagation_of_vorticityBound coreDuhamelVorticityBound

end UnforcedLeray.Short.IIIa
