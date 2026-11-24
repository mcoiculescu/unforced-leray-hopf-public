import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.L2Sq

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/6` (`MollLimit`): pointwise limit of `E_k`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. On a good slice `s > 0`, `E_k(s) = ∫_cell |J_k b(s)|² → E(s) = ∫_cell |b(s)|²`.

Proof: `LMMollE c J b k s` is by definition `∫_cell vnorm2 (J k (b s))^2`, and `energyE c b s` is
`∫_cell vnorm2 (b (s, ·))^2`. Apply `lm_tendsto_vsq` with `a k = J k (b s)` and `a₀ = b s`; its
hypotheses are `IsLMMollifier.memL2` and `IsLMMollifier.tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Pointwise limit of `E_k`** (SP 3541-3552): on a good slice `s > 0`,
`E_k(s) → E(s)`. -/
theorem lmMollPointwiseE : LMMollPointwiseE := by
  intro c ν μ F b G hD J hJ s hs hg
  have hb : LMCellL2 c (fun y => b (s, y)) := hg.1
  exact lm_tendsto_vsq (a := fun k => J k (fun y => b (s, y))) (a₀ := fun y => b (s, y))
    (fun k => hJ.memL2 k _ hb) hb (hJ.tendsto _ hb)

end UnforcedLeray.Short.IIIa
