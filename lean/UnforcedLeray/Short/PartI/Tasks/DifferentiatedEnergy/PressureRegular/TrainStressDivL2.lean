import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.StressBound

/-!
# Part I, task `PartI:T08/3/6` (`trainStressDivL2_proof`): the stress divergence

Source: `the November 2 reference manuscript` lines 326-329.

Component `l` of `div Q_c` is `∂_q Q_{0l} + ∂_η Q_{1l}`. Smoothness follows from `qcSmooth_proof`.
Word derivatives in `L²(cell)` come from the first conjunct of `vcStressJetBound_proof` (every word
derivative of every entry of `Q_c` is in `L²(cell)`), via `ForcingIBP.matDiv_word_L2`, which
moves the word derivative through `∂_q` and `∂_η` (commutation, `ForcingIBP.derivWord_comm`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

theorem trainStressDivL2_proof : UnforcedLeray.Short.PartI.TrainStressDivL2 := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  have hQs : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Qc ν c s z k l) :=
    fun k l => qcSmooth_proof ν c s hν hc0 hs.le k l
  obtain ⟨B, b, -, -, h⟩ := vcStressJetBound_proof 0
  have hL : ∀ (w : List Bool) (k l : Fin 2),
      MemLp (B0151.derivWord w (fun z => Qc ν c s z k l)) 2 (Cyl.cellμ c) :=
    (h ν c s hν hc hs hac).1
  refine ⟨?_, ?_⟩
  · refine (contDiff_piLp _).2 fun l => ?_
    rw [ForcingIBP.matDiv_comp (Qc ν c s) l]
    exact (ForcingIBP.cd_partialQ (hQs 0 l)).add (ForcingIBP.cd_partialEta (hQs 1 l))
  · intro w k
    exact ForcingIBP.matDiv_word_L2 (c := c) (Qc ν c s) hQs hL w k

end UnforcedLeray.Short.PartI
