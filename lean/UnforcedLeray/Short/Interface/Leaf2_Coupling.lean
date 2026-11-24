import UnforcedLeray.Short.Interface.Sub.I09
import UnforcedLeray.Short.Interface.Leaf2_Coupling.SymColumns
import UnforcedLeray.Short.Interface.Leaf2_Coupling.FiberIdentity
import UnforcedLeray.Short.Interface.Leaf2_Coupling.PartialPhaseTest

/-!
# Interface:I09 (helper 2b-4): the unconditional periodic transfer of the Leray coupling

Final assembly. Source of record: `the November 2 reference manuscript`, lines
173-180 (the mode equation `loc:eq:mode` with the term `𝔓 div(U_* ⊗ b_* + b_* ⊗ U_*)`, whose
pairing with the Leray projection gives the periodic transfer of the coupling to one period).

The three sub-lemmas are proved in their own files:
* `symColumnsIsY2` (task `Interface:I09/1`, `Leaf2_Coupling/SymColumns.lean`);
* `lerayFiberIdentity` (task `Interface:I09/2`, `Leaf2_Coupling/FiberIdentity.lean`);
* `similarityPartialPhaseTest` (task `Interface:I09/3`, `Leaf2_Coupling/PartialPhaseTest.lean`).

They feed the conditional assembly `periodicCouplingTransfer_of` (`Sub/I09.lean`), which yields
`PeriodicCouplingTransfer` with no extra hypothesis.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Interface

/-- **Interface:I09 (helper 2b-4), unconditional.** `PeriodicCouplingTransfer` holds: the
integrability of the line coupling and the transfer to one period follow from the three proved
sub-lemmas. -/
theorem periodicCouplingTransfer : PeriodicCouplingTransfer :=
  periodicCouplingTransfer_of symColumnsIsY2 lerayFiberIdentity similarityPartialPhaseTest

end UnforcedLeray.Short.Interface
