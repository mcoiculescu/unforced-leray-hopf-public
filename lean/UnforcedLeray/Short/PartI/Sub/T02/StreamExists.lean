import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.TendstoZero
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.EnergyProfile
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.EtaDeriv
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.PrimitiveQ
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.FluxZero
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.GammaDeriv
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.GammaOdd
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.GammaTendsto
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.CurlMeanMoment
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.GammaIntegrableIoi
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.MeanPrimDeriv
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.PsiBarExists
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.PsiGradient
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists.PsiDecay

/-!
# Part I, task `PartI:T02/5`: `StreamExists` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

The unconditional target `streamExists : StreamExists` is assembled from the conditional theorem
`streamExists_of_leaves` (`Short/PartI/Sub/T02_5.lean`) and the proved leaf statements, each a
separate module under `Short/PartI/Sub/T02/StreamExists/`:

* `hB` `TendstoZeroOfLipschitzIntegrable`, `hC` `SliceEnergyProfile`, `hD`
  `HasDerivAtEtaIntervalIntegral` (real analysis and differentiation under the integral);
* `hE` `ContDiffPrimitiveQ` (from `hD`), `hF` `SliceFluxZero` (from `hB`, `hC`, `hD`);
* `h6` `GammaDeriv` (from `hD`), `h7` `GammaOdd`, `h8` `GammaTendsto` (from `hB`, `hC`),
  `h9` `CurlMeanMoment`, `h10` `GammaIntegrableIoi` (from `h6`, `h8`, `h9`);
* `h11` `MeanPrimDeriv` (from `hD`, `hE`).

The three leaves of `streamExists_of_leaves` are then `PsiBarExists` (from `h6`, `h7`, `h10`),
`PsiGradient` (from `hD`, `hE`, `h11`) and `PsiDecay` (from `hB`, `hC`, `hF`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T02/5`, unconditional**: `StreamExists` (source lines 261-288). -/
theorem streamExists : StreamExists := by
  have hB := tendstoZeroOfLipschitzIntegrable
  have hC := sliceEnergyProfile
  have hD := hasDerivAtEtaIntervalIntegral
  have hE := contDiffPrimitiveQ hD
  have hF := sliceFluxZero hB hC hD
  have h6 := gammaDeriv hD
  have h7 := gammaOdd
  have h8 := gammaTendsto hB hC
  have h9 := curlMeanMoment
  have h10 := gammaIntegrableIoi h6 h8 h9
  have h11 := meanPrimDeriv hD hE
  exact streamExists_of_leaves (psiBarExists h6 h7 h10) (psiGradient hD hE h11) (psiDecay hB hC hF)

end UnforcedLeray.Short.PartI

end
