import UnforcedLeray.Short.PartIIa.Sub.R02_3
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-a, task `PartII-a:R02/3/1`: joint smoothness of the mean remainder

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`)
and 447-449 (`sct:expansion`, first display).

`meanRemainder tr N s η = meanStream tr s η - ∑_{j ≤ N} meanCoeff tr j * ∂_η^{2j} G_{νs}(η)`.
The first term is smooth on `(0,∞) × ℝ` by `TrainMeanEquations` (its first conjunct); each summand of
the finite sum is a constant times a joint heat-kernel derivative, smooth by `HeatKernelIterSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)

theorem meanRemainderSmooth_of (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hH : UnforcedLeray.Short.PartIIa.HeatKernelIterSmooth) :
    UnforcedLeray.Short.PartIIa.MeanRemainderSmooth := by
  unfold UnforcedLeray.Short.PartIIa.MeanRemainderSmooth
  intro ν c hν hc tr hb N
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (hE ν c hν hc tr hb).1
  have hsum : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1),
        meanCoeff tr j * iteratedDeriv (2 * j) (fun e => heatKernel1 (ν * x.1) e) x.2)
      (Ioi 0 ×ˢ univ) := by
    apply ContDiffOn.sum
    intro j _
    exact ContDiffOn.mul contDiffOn_const (hH ν hν (2 * j))
  refine (hS.sub hsum).congr ?_
  intro x _
  rfl

end UnforcedLeray.Short.PartIIa
