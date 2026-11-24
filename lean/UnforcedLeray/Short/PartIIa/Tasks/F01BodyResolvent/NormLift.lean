import UnforcedLeray.Short.PartIIa.Sub.F01

/-!
# Part II-a, task `PartII-a:F01/1`: the norm lift

Proves `NormLiftExists` (defined in `Sub/F01.lean`): for `F ∈ L^p(ℝ³; ℂ³)` the real field
`G x = (‖F x‖, 0, 0)` lies in `L^p(ℝ³; ℝ³)` and has the same `L^p` norm as `F`.

Source of record: `the November 2 reference manuscript`, lines 1363-1368.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace (CVec3)

/-- **Norm lift** (task `PartII-a:F01/1`): `NormLiftExists` holds. -/
theorem normLiftExists_proof : UnforcedLeray.Short.PartIIa.NormLiftExists := by
  intro p hpF hp F
  have hFm : AEStronglyMeasurable (fun x : Space => ‖F x‖) (volume : Measure Space) :=
    (Lp.aestronglyMeasurable F).norm
  have hc : Continuous (fun r : ℝ => EuclideanSpace.single (0 : Fin 3) r) := by
    have hiso : Isometry (fun r : ℝ => EuclideanSpace.single (0 : Fin 3) r) := by
      apply Isometry.of_dist_eq
      intro a b
      simp [PiLp.dist_single_same]
    exact hiso.continuous
  have hgm : AEStronglyMeasurable (fun x : Space => EuclideanSpace.single (0 : Fin 3) ‖F x‖)
      (volume : Measure Space) :=
    hc.comp_aestronglyMeasurable hFm
  have hgn : ∀ x : Space, ‖(EuclideanSpace.single (0 : Fin 3) ‖F x‖ : Space)‖ = ‖F x‖ := by
    intro x
    simp
  have hmem : MemLp (fun x : Space => EuclideanSpace.single (0 : Fin 3) ‖F x‖) p
      (volume : Measure Space) :=
    (Lp.memLp F).congr_norm hgm (ae_of_all _ fun x => (hgn x).symm)
  refine ⟨hmem.toLp (fun x : Space => EuclideanSpace.single (0 : Fin 3) ‖F x‖), ?_, ?_⟩
  · exact MemLp.coeFn_toLp hmem
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (ae_of_all _ fun x => hgn x))

end UnforcedLeray.Short.PartIIa
