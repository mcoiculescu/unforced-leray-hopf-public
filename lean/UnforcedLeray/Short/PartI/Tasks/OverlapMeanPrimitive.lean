import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive.MeanStreamDiffDuhamelL1
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive.MeanStressPreOverlapL1Integral

/-!
# Part I, task `PartI:T14`: the overlap-rescaled mean stream primitive `𝖲` (unconditional assembly)

Source of record: `the November 2 reference manuscript`, lines 395-425.
Assembles `overlap_mean_primitive` from `overlap_mean_primitive_of` (`Sub/PartI_T14.lean`),
`meanStreamDiffDuhamelL1_proof` (`PartI:T14/1`), and `meanStressPreOverlapL1Integral_proof`
(`PartI:T14/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T14` (`overlap_mean_primitive`)** (source lines 395-425):
properties and initial `L¹_Y` bound of the overlap-rescaled mean stream primitive
`𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)`. -/
theorem overlap_mean_primitive (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (UnforcedLeray.Short.PartI.trainPeriod ρ ν),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          let c := UnforcedLeray.Short.PartI.trainPeriod ρ ν
          let U := UnforcedLeray.Short.PartI.overlapField ν c tr.v
          let W := fun T => UnforcedLeray.Short.PartI.hfluct 1 (U T)
          let b := fun T Y => (UnforcedLeray.Short.PartI.hmean 1 (U T) Y) 0
          ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.overlapMeanStream tr x.1 x.2) (Set.Ici 0 ×ˢ Set.univ) ∧
          (∀ T : ℝ, 0 ≤ T → ∀ Y : ℝ,
            deriv (fun T' => UnforcedLeray.Short.PartI.overlapMeanStream tr T' Y) T -
                deriv (deriv (fun Y' => UnforcedLeray.Short.PartI.overlapMeanStream tr T Y')) Y =
              UnforcedLeray.Short.PartI.eC ν c * UnforcedLeray.Short.PartI.hmean 1 (fun y : UnforcedLeray.Cyl.Plane => W T y 0 * W T y 1) Y ∧
            b T Y = -deriv (fun Y' => UnforcedLeray.Short.PartI.overlapMeanStream tr T Y') Y ∧
            (UnforcedLeray.Short.PartI.hmean 1 (U T) Y) 1 = 0) ∧
          MeasureTheory.eLpNorm (UnforcedLeray.Short.PartI.overlapMeanStream tr 0) 1 MeasureTheory.volume ≤ ENNReal.ofReal C :=
  overlap_mean_primitive_of meanStreamDiffDuhamelL1_proof meanStressPreOverlapL1Integral_proof ρ hρ

end UnforcedLeray.Short.PartI
