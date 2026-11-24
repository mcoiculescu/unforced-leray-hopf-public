import UnforcedLeray.Loc.Assembly
import UnforcedLeray.Loc.Hyp.H2EmbedsC0
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity
import UnforcedLeray.Loc.Hyp.H2ProductBound
import UnforcedLeray.Loc.Hyp.HeatTailW2Continuous
import UnforcedLeray.Loc.Hyp.ResidualForce
import UnforcedLeray.Loc.Hyp.BackgroundStrongForm
import UnforcedLeray.Loc.Hyp.EvolutionWeakForm
import UnforcedLeray.Loc.Hyp.ModeIdentification

/-!
# Localization half from the mode identification

`Loc/Assembly.lean` proves `LocalizationClaim` from eight named analytic hypotheses. Seven of
them are proved in `Loc/Hyp/`; this file discharges them, so the localization half
(Theorem `thm:localization`, `paper/main.tex` lines 232–621) depends only on
`L04.ModeIdentificationHyp` (lines 308–318, blueprint units B1009 and B1010).
-/

set_option autoImplicit false

namespace UnforcedLeray.Loc.Assembly

open UnforcedLeray.Blueprint

theorem localizationClaim_of_modeIdentification (h3 : L04.ModeIdentificationHyp) :
    LocalizationClaim :=
  localizationClaim_of_hyps h2EmbedsC0 heatProfileRegularity h3 L10.h2ProductBound
    UnforcedLeray.Hyp.HeatTail.heatTailW2Continuous L10.residualForce
    HypBg.backgroundStrongForm L13.evolutionWeakForm

theorem mainClaim_of_modeIdentification (h3 : L04.ModeIdentificationHyp)
    (hC : ConstructionClaim) : MainClaim :=
  mainClaim_of_localization_construction (localizationClaim_of_modeIdentification h3) hC

/-- The localization half, `thm:localization` (`paper/main.tex` lines 232–621): every background
with the properties of `prop:unstable-background` yields `ViscosityMainClaim`. -/
theorem localizationClaim : LocalizationClaim :=
  localizationClaim_of_modeIdentification ModeId.modeIdentificationHyp

/-- `MainClaim` from the construction half alone. -/
theorem mainClaim_of_constructionClaim (hC : ConstructionClaim) : MainClaim :=
  mainClaim_of_localization_construction localizationClaim hC

end UnforcedLeray.Loc.Assembly

#print axioms UnforcedLeray.Loc.Assembly.localizationClaim_of_modeIdentification
#print axioms UnforcedLeray.Loc.Assembly.mainClaim_of_modeIdentification
#print axioms UnforcedLeray.Loc.Assembly.localizationClaim
#print axioms UnforcedLeray.Loc.Assembly.mainClaim_of_constructionClaim
