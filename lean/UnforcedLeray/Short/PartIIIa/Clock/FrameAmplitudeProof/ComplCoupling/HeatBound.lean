import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecayFinal
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.GramInvSplit

/-!
# Part III-a, task `PartIII-a:T21/c5/3/1`: moving heat/dilation dual bound (`MovLamDualHeatBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2896-2912 and
2990-2997 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

All proved infrastructure (`eLpNorm_cellMeasure_neg_le_of_cell_bdd`, `memLp_and_xNorm_perSum_of_inv_sq_decay`,
`memLp_and_xNorm_perLam0_neg`, `physFrameLam0_eq_perSum_physAdj`, `physFrameLam_eq_sum_perGram_inv`,
`perGram_inv_entry_bound`, `movPlanarLap_physAdj_eq`, and the conditional assembly
`movLamDualHeatBound_of`) has been promoted to
`UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T21_c5_3_1»`.

Once child tasks `PartIII-a:T21/c5/3/1/1` (`seedLamPDSharpDecay`) and
`PartIII-a:T21/c5/3/1/2` (`perGramInvHeatSplit`) are complete (or via `DirectHeatSub.movLamDualHeatBound_of`
from `PartIII-a:T21/c5/2/1/1` `movLam0HeatDecomp`), this file will assemble `movLamDualHeatBound`.
-/

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T21/c5/3/1`**: assembly of `MovLamDualHeatBound` from the two leaves. -/
theorem movLamDualHeatBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLamDualHeatBound κ :=
  movLamDualHeatBound_of κ (seedLamPDSharpDecay κ) (perGramInvHeatSplit κ)

end UnforcedLeray.Short.IIIa
