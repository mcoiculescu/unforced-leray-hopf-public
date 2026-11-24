import UnforcedLeray.Short.Spine.Sub.SP_EST
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm

/-!
# Spine: the post-overlap train bound (task `Spine:SP-EST/3`)

Source of record: `the November 2 reference manuscript`, lines 304-313, 379-389
(`sct:overlap`, uniform post-overlap derivative bound). The statement is `Spine.TrainPostBound`;
the proof reads off the `supNormD` bound of `PartI.overlap_highnorm_uniform` (`PartI:T12`) at
`ρ = 2` (so `Train.per ν = trainPeriod 2 ν`) and derivative budget `N = 3`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.Short.PartI
open UnforcedLeray.Cyl (Plane)

theorem trainPostBound_proof : UnforcedLeray.Short.Spine.TrainPostBound := by
  obtain ⟨C, ν₀, hC, hν₀, h⟩ :=
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform 2 (by norm_num) 3
  refine ⟨fun _ => C, ν₀, hν₀, ?_⟩
  intro ν hν T hT t ht j hj y
  have hν0 : 0 < ν := hν.1
  have hνle : ν ≤ ν₀ := hν.2
  have gen : ∀ c : ℝ, c = trainPeriod 2 ν → ∀ T : B0140.TrainSol ν c, IsBUCTrain T →
      ∀ y : Plane, ‖iteratedFDeriv ℝ j (overlapField ν c T.v t) y‖ ≤ C := by
    intro c hc T hT y
    subst hc
    have hsup := (h ν hν0 hνle T hT t ht j hj).2
    have h1 : ‖iteratedFDeriv ℝ j (overlapField ν (trainPeriod 2 ν) T.v t) y‖ₑ ≤
        B0277.supNormD j (overlapField ν (trainPeriod 2 ν) T.v t) :=
      le_iSup (fun z => ‖iteratedFDeriv ℝ j (overlapField ν (trainPeriod 2 ν) T.v t) z‖ₑ) y
    have h2 := h1.trans hsup
    rw [← ofReal_norm] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).1 h2
  exact gen (Train.per ν) (Train.per_eq_rpow hν0) T hT y

end UnforcedLeray.Short.Spine
