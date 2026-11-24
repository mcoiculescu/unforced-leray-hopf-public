import UnforcedLeray.Short.PartI.Sub.PartI_T08_4
import UnforcedLeray.Short.PartI.Sub.T08_3

/-!
# Part I, task `PartI:T08/4/1` (`TrainJetEnergyTimeDeriv`): decomposition

Source `the November 2 reference manuscript` lines 341-348 (differentiated energy
`d/ds ‖D^j e‖₂²`), 326-329 (error equation) and 261-288 (the train and its regularity).

`d/dr ∫_cell (∂_w e_k)²` is a derivative under the integral over the uncut cell, which has no
compact box. Two leaves:

* `TrainTimeDerivLocalL2`: a time-local `L²(cell)` majorant of `∂_r D^w e(r)` for `r` near `s`
  (the pointwise-in-`s` version is `TrainTimeDerivL2`);
* `TrainJetEnergyTimeDerivOfLocal`: the dominated-convergence reduction
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, bound `sup |∂_w e| · |∂_r ∂_w e|` and
  Cauchy-Schwarz, commutation of `wordComp` with `deriv` in time by `swtc_main` of
  `ErrJetL2/VelocityJetL2/EnergyIneq/SliceWordTimeComm.lean`, `HasDerivAt.sum` over words).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf 1 (time-local `L²` majorant of `∂_r D^w e`)** (lines 261-288, 326-329). For every age
`s > 0` with `a(s) ≤ c²`, every word `w` and component `k`, there are `ε, K` such that for all
`r ∈ (0, ∞)` with `|r - s| < ε` the word derivative of `∂_r e(r)` is in `L²(cell)` with squared
norm at most `K`. (`∂_r e = νΔe - A - ∇π - div Q_c` with `e(r) ∈ H^∞` uniformly for `r` in a
neighbourhood of `s`; the existence of the train on a neighbourhood of `s` is part of the
`TrainSol` data. Pointwise in `s` this is `TrainTimeDerivL2`.) -/
def TrainTimeDerivLocalL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 → ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
      ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp w (fun z => deriv (fun t => trainErr tr t z) r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (fun z => deriv (fun t => trainErr tr t z) r) k z) ^ 2 ≤ K

/-- **Leaf 2 (differentiation under the integral over the uncut cell)** (lines 341-348): the
time-local majorant implies the differentiated cell energy. -/
def TrainJetEnergyTimeDerivOfLocal : Prop :=
  TrainTimeDerivLocalL2 → TrainJetEnergyTimeDeriv

theorem trainJetEnergyTimeDeriv_proof_of (h1 : TrainTimeDerivLocalL2)
    (h2 : TrainJetEnergyTimeDerivOfLocal) : TrainJetEnergyTimeDeriv :=
  h2 h1

end UnforcedLeray.Short.PartI
