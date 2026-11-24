import UnforcedLeray.Short.Interface.Leaf2.Assemble
import UnforcedLeray.Short.Interface.Leaf2_PeriodizeTest
import UnforcedLeray.Short.Interface.Leaf2_Commutes
import UnforcedLeray.Short.Interface.Leaf2_LineToSlab
import UnforcedLeray.Short.Interface.Leaf2_Coupling
import UnforcedLeray.Short.Interface.Leaf2_Integrability

/-!
# Interface leaf 2 (`PeriodicModeEquationToLine`): the unconditional theorem

Source of record: `the November 2 reference manuscript`, line 180.

The conditional assembly `periodicModeEquationToLine_of` (`Leaf2/Assemble.lean`, verified) takes
the five helper Props. This file applies it to the five proved helpers:

* `periodizeIsPeriodicTest` (task `Interface:I06`, `Leaf2_PeriodizeTest.lean`);
* `periodizeCommutes` (task `Interface:I07`, `Leaf2_Commutes.lean`);
* `periodicLineToSlab` (task `Interface:I08`, `Leaf2_LineToSlab.lean`);
* `periodicCouplingTransfer` (task `Interface:I09`, `Leaf2_Coupling.lean`);
* `modeSolutionIntegrability` (task `Interface:I10`, `Leaf2_Integrability.lean`).
-/

namespace UnforcedLeray.Short.Interface

/-- **Leaf 2** (task `Interface:I11`): the mode equation on `𝒟'(ℝ³ × ℝ/𝒯ℤ)` gives the
line equation `IsWeakModeSolution`. -/
theorem periodicModeEquationToLine : PeriodicModeEquationToLine :=
  Leaf2.periodicModeEquationToLine_of periodizeIsPeriodicTest periodizeCommutes
    periodicLineToSlab periodicCouplingTransfer modeSolutionIntegrability

end UnforcedLeray.Short.Interface
