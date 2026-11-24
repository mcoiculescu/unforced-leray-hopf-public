import UnforcedLeray.Loc.L01Coefficient
import UnforcedLeray.Loc.L02FreeEvolution
import UnforcedLeray.Loc.L03Evolution
import UnforcedLeray.Loc.L04ModeRegularity
import UnforcedLeray.Loc.L05EssentialRadius
import UnforcedLeray.Loc.L06SpectralSplitting
import UnforcedLeray.Loc.L07Projection
import UnforcedLeray.Loc.L08Green
import UnforcedLeray.Loc.L09CompactDatum
import UnforcedLeray.Loc.L10Nonlinear
import UnforcedLeray.Loc.L11AffineBound
import UnforcedLeray.Loc.L12Equivariance
import UnforcedLeray.Loc.L13PhysicalRemainder
import UnforcedLeray.Loc.L14Realization
import UnforcedLeray.Blueprint.Localization.Compose
import UnforcedLeray.Blueprint.Top

/-!
# Assembly of the localization half

`thm:localization` (`paper/main.tex` statement lines 232–260, proof lines 262–593; blueprint
B1035) from the fourteen step theorems of `Loc/`, composed by the compiled
`Blueprint.localizationClaim_of_steps` (`Blueprint/Localization/Compose.lean`). Ten steps are
proved outright:

* L2 `Loc.L02.freeEvolutionStep`, L3 `Loc.L03Evolution.evolutionStep`,
  L5 `Loc.L05.essentialRadiusStep`, L6 `Loc.L06.spectralSplittingStep`,
  L7 `Loc.L07.projectionStep`, L8 `Blueprint.L08Green.greenStep`,
  L9 `L09.compactDatumStep`, L11 `Loc.L11.affineBoundStep`,
  L12 `Blueprint.L12.equivarianceStep`, L14 `Blueprint.realizationStep`.

Four steps are proved from eight named hypotheses, each a `Prop` with its own docstring:

* L1 `Blueprint.coefficientStep_of` from `H2EmbedsC0`, `HeatProfileRegularity`
  (lines 279–290; B0709–B0711);
* L4 `Blueprint.L04.modeRegularityStep_of` from `L04.ModeIdentificationHyp`
  (lines 307–329; B1009–B1011), which is equivalent to the step
  (`L04.modeRegularityStep_iff`);
* L10 `Blueprint.L10.nonlinearStep_of` from `L10.H2ProductBound`, `L10.HeatTailW2Continuous`,
  `L10.ResidualForce` (lines 462–491; B0721, B0722);
* L13 `Blueprint.L13.physicalRemainderStep_of` from `L13.BackgroundStrongForm`,
  `L13.EvolutionWeakForm` (lines 501–503, 525–547).

No step theorem takes a hypothesis beyond these eight. Theorem A (lines 74–105) then follows
from `prop:unstable-background` (`ConstructionClaim`, lines 150–191; B1034) and the viscosity
transport (lines 597–617; B1036), as in lines 614–617 and 13740–13749 (B1037, B1038), by the
compiled `Blueprint.mainClaim_of_localization_construction` (`Blueprint/Top.lean`).

Status: the eight hypotheses and `ConstructionClaim` are OPEN, so neither `LocalizationClaim`
nor `MainClaim` is proved here.
-/

set_option autoImplicit false

namespace UnforcedLeray.Loc.Assembly

open UnforcedLeray.Blueprint

/-- **`thm:localization` from the eight named hypotheses** (`paper/main.tex` lines 232–260,
proof lines 262–593; blueprint B1035). The fourteen steps L1–L14 are the compiled step
theorems of `Loc/`; L1, L4, L10 and L13 use the hypotheses, the other ten are proved. -/
theorem localizationClaim_of_hyps (h1 : H2EmbedsC0) (h2 : HeatProfileRegularity)
    (h3 : L04.ModeIdentificationHyp) (h4 : L10.H2ProductBound)
    (h5 : L10.HeatTailW2Continuous) (h6 : L10.ResidualForce)
    (h7 : L13.BackgroundStrongForm) (h8 : L13.EvolutionWeakForm) : LocalizationClaim :=
  localizationClaim_of_steps
    (coefficientStep_of h1 h2)
    UnforcedLeray.Loc.L02.freeEvolutionStep
    UnforcedLeray.Loc.L03Evolution.evolutionStep
    (L04.modeRegularityStep_of h3)
    UnforcedLeray.Loc.L05.essentialRadiusStep
    UnforcedLeray.Loc.L06.spectralSplittingStep
    UnforcedLeray.Loc.L07.projectionStep
    L08Green.greenStep
    UnforcedLeray.L09.compactDatumStep
    (L10.nonlinearStep_of h4 h5 h6)
    UnforcedLeray.Loc.L11.affineBoundStep
    L12.equivarianceStep
    (L13.physicalRemainderStep_of h7 h8)
    realizationStep

/-- **Theorem A from the eight localization hypotheses and the construction**
(`paper/main.tex` lines 74–105, assembled in lines 614–617 and 13740–13749; blueprint B1037,
B1038): `thm:localization` (`localizationClaim_of_hyps`, B1035) applied to the package of
`prop:unstable-background` (`ConstructionClaim`, lines 150–191, B1034), followed by the
compiled viscosity transport (lines 597–617, B1036). -/
theorem mainClaim_of_localizationHyps (h1 : H2EmbedsC0) (h2 : HeatProfileRegularity)
    (h3 : L04.ModeIdentificationHyp) (h4 : L10.H2ProductBound)
    (h5 : L10.HeatTailW2Continuous) (h6 : L10.ResidualForce)
    (h7 : L13.BackgroundStrongForm) (h8 : L13.EvolutionWeakForm)
    (hC : ConstructionClaim) : MainClaim :=
  mainClaim_of_localization_construction
    (localizationClaim_of_hyps h1 h2 h3 h4 h5 h6 h7 h8) hC

end UnforcedLeray.Loc.Assembly

#print axioms UnforcedLeray.Loc.Assembly.localizationClaim_of_hyps
#print axioms UnforcedLeray.Loc.Assembly.mainClaim_of_localizationHyps
