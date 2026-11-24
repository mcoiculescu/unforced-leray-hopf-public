import UnforcedLeray.Short.PartI.Sub.T02_1_4

/-!
# Part I, task `PartI:T02/1/4/1`: finite energy of the spatial representative

Source of record: `the November 2 reference manuscript`, lines 261-288
(the mild solution is the finite-energy solution, so `u(s)` lies in `L²` of the cell).

Target: `repFiniteEnergy : RepFiniteEnergy` (leaf 1 of `Sub/T02_1_4.lean`).

Route.
* `IsSpatialRepOn.represents` at `s` and the zero word `α = Idx.zero` says that
  `vecH3CellDerivCLM Idx.zero (u s)` equals `Sob.iterD [] (w s) = w s` almost everywhere on the cell.
* The left side is an element of `L²(cellμ c)`, so `‖·‖²` is integrable on `cellμ c`.
* Transfer along the a.e. equality; `IntegrableOn _ (cell c)` is `Integrable _ (cellμ c)` by definition.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **Leaf 1** (finite energy), `RepFiniteEnergy`: the spatial representative has `‖w s‖²`
integrable on the cell for every `s ∈ [0,T]`. -/
theorem repFiniteEnergy : RepFiniteEnergy := by
  intro ν c T hν hc hc1 hT u _ w hw s hs
  have hrep := hw.represents ⟨s, hs⟩ Sob.Idx.zero
  simp only [Sob.TestDomain.word_zero, Sob.iterD_nil] at hrep
  have hmem : MemLp
      (vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) : Plane → Vec) 2 (Cyl.cellμ c) :=
    Lp.memLp _
  have hmem2 : MemLp
      (vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) : Plane → Vec)
      ((2 : ℕ) : ENNReal) (Cyl.cellμ c) := by
    exact_mod_cast hmem
  have hint : Integrable
      (fun z => ‖(vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) : Plane → Vec) z‖ ^ 2)
      (Cyl.cellμ c) :=
    hmem2.integrable_norm_pow (by norm_num)
  have hae : (fun z => ‖(vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) : Plane → Vec) z‖ ^ 2)
      =ᵐ[Cyl.cellμ c] (fun z => ‖w s z‖ ^ 2) := by
    filter_upwards [hrep] with z hz
    rw [hz]
  exact hint.congr hae
