import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Volterra
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Flow
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.BiotSavart
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.FluxRefl
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowAppend
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowCongrAE
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowGlobal
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.LinFlowComb
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# `TrainEvolutionExists` with the proved leaves plugged in (source 2819-2836, 4349-4352)

Source of record: `the November 2 reference manuscript` (73 pages).

`trainEvolutionExists_of'` is `trainEvolutionExists_of` (`Evolution/Assembly.lean`) with the leaves
proved in this folder (`volterraReflect`, `volterraJointCont_of volterraDiagCont`,
`flowOfRealFamily_of`, `fluxBOnRefl_of (stripVelRefl_of ...)`) and the accepted Part III-a lemmas
(`biotSavartFieldAll`, `flowCongrAE`, `flowAppend`, `flowGlobal`, `linFlowComb`,
`IIIa.CTE.isBiotSavart_unique`).  The hypotheses left are the existence chain of the Volterra
evolution of Part III-a (tasks `PartIII-a:T21/3/1`, `/1/2`, `/5`, `/6`, `/7`, `/9/5`) and the
reflection-compatible heat family `ReflHeatSupplierExists` (task

`heatS0Refl_of`, `heatResponseRefl_of`, `periodicRepRefl` of `Evolution/Heat.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Short.IIIa.Exist

/-- **`TrainEvolutionExists`** from the existence chain of the Volterra evolution and the
reflection-compatible heat family. -/
theorem trainEvolutionExists_of' (hTB : TrainBoundsSmall) (hFP : FluxPathExistsAll)
    (hHeat : ReflHeatSupplierExists) (hFI : FluxIdentityOnAll) (hMI : MildIntegratedOnAll)
    (hSC : StripContinuityOnAll) (hLoc : HorizonLocality) : TrainEvolutionExists :=
  trainEvolutionExists_of hTB hFP hHeat biotSavartFieldAll hFI hMI hSC hLoc flowCongrAE
    (flowOfRealFamily_of linFlowComb flowCongrAE flowAppend flowGlobal) volterraReflect
    (volterraJointCont_of volterraDiagCont)
    (fluxBOnRefl_of (stripVelRefl_of biotSavartFieldAll IIIa.CTE.isBiotSavart_unique))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
