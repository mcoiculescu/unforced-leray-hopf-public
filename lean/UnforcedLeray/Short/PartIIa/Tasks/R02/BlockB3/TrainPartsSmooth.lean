import UnforcedLeray.Short.PartIIa.Calc.BlockB3
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.FluctProfileSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth

/-!
# Part II-a, block `B₃`: the leaf `TrainPartsSmooth` (task `PartII-a:R02/11/7`)

Target: `trainPartsSmooth_of (hS : LateProfileSmooth) : TrainPartsSmooth`: for a BUC train,
the mean `S = meanP`, the fluctuation `fluctP`, the remainder `remP tr 1` and the heat profile
`heatProfile ν` are `C^∞` on `{s > 0}`.

Source of record: `the November 2 reference manuscript` lines 397-404 (mean stream)
and 447-449 (mean remainder `R_N`).

Route: the fluctuation is `fluctProfileSmooth_of`; the mean and the remainder reuse the stream
`(s, η) ↦ meanStream tr s η`, smooth by `hmeanContDiff` (applied to the train stream, via the
same change of variables as in `fluctProfileSmooth_of`); the heat profile is the `k = 0` case of
`heatKernelIterSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)
open UnforcedLeray.B0184 UnforcedLeray.B0190

/-- **Leaf `TrainPartsSmooth`** (source lines 397-404, 447-449). -/
theorem trainPartsSmooth_of (hS : UnforcedLeray.Short.PartIIa.LateProfileSmooth) :
    TrainPartsSmooth := by
  unfold TrainPartsSmooth
  intro ν c hν hc tr hb
  -- common input: the stream on train variables, and the smoothness of the mean stream
  have hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (x.2.1, (x.2.2, x.1))) := by
    fun_prop
  have hmap : Set.MapsTo (fun x : ℝ × (ℝ × ℝ) => (x.2.1, (x.2.2, x.1)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) {x : ProfilePoint | 0 < x.2.2} := by
    intro x hx
    exact hx.1
  have hψS : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    ((hS ν c hν hc tr hb).1).comp hg.contDiffOn hmap
  have hmeanS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    UnforcedLeray.Short.PartI.hmeanContDiff c hc tr.ψ hψS
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the mean stream `S = meanP`
    exact contDiffOn_trainProfile_of_eta (G := meanStream tr) hmeanS
  · -- (2) the fluctuation `ψ̃ = fluctP`
    exact UnforcedLeray.Short.PartIIa.fluctProfileSmooth_of hS UnforcedLeray.Short.PartI.hmeanContDiff ν c hν hc tr hb
  · -- (3) the mean remainder `R₁ = remP tr 1`
    have hsum : ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => ∑ j ∈ Finset.range (1 + 1),
          meanCoeff tr j * iteratedDeriv (2 * j) (fun e => heatKernel1 (ν * x.1) e) x.2)
        (Ioi 0 ×ˢ univ) := by
      apply ContDiffOn.sum
      intro j _
      exact ContDiffOn.mul contDiffOn_const
        (UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν hν (2 * j))
    have hR : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr 1 x.1 x.2)
        (Ioi 0 ×ˢ univ) := by
      refine (hmeanS.sub hsum).congr ?_
      intro x _
      rfl
    exact contDiffOn_trainProfile_of_eta (G := fun s e => meanRemainder tr 1 s e) hR
  · -- (4) the heat profile `heatProfile ν`
    have h := UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν hν 0
    simp only [iteratedDeriv_zero] at h
    exact contDiffOn_trainProfile_of_eta (G := fun s e => heatKernel1 (ν * s) e) h

end UnforcedLeray.Short.PartIIa.BlockB3
