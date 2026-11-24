import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1

/-!
# `PartI:T09/5/org/1/org`: the finite-energy class of the train

Source: `the November 2 reference manuscript`,
lines 270-288 (the BUC solution is the finite-energy solution: the mild `L^2` bound continues
`L^2` membership, approximation and cutoffs give the energy identities, so the jets of `v` are
continuous in age with values in `L^2` of the cell), 294 (`V_c^p`), 341-344.

`CellL2ContAt0 c F` says that every word derivative of every component of `F s` converges to that
of `F 0` in `L^2(cell c)` as `s -> 0+`.  `IsFiniteEnergyTrain tr` is this for `F = tr.v`
(continuity at age `0` of `s -> v(s)` in `H^k(cell)` for all `k`); `VcCellL2Cont` is the same
statement for the explicit Gaussian train `V_c^p` (`Train.Vc`).  Both are written with `lintegral`
so that no junk Bochner value can satisfy them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc)

/-- Every word derivative of every component of `F s` tends to that of `F 0` in `L^2(cell c)`
as the age tends to `0` from the right. -/
def CellL2ContAt0 (c : ℝ) (F : ℝ → Plane → Vec) : Prop :=
  ∀ (w : List Bool) (k : Fin 2),
    Tendsto (fun s : ℝ => ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal ((wordComp w (F s) k z - wordComp w (F 0) k z) ^ 2))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0)

/-- **The finite-energy train (lines 281-288):** the velocity is continuous at age `0` into every
`H^k(cell)`. -/
structure IsFiniteEnergyTrain {ν c : ℝ} (tr : B0140.TrainSol ν c) : Prop where
  cont : CellL2ContAt0 c tr.v

/-- The explicit Gaussian train `V_c^p` (line 294) is `H^k(cell)`-continuous at age `0`. -/
def VcCellL2Cont : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → CellL2ContAt0 c (Vc ν c)

/-- **Source fact (lines 270-288):** a BUC train is the finite-energy solution. -/
def TrainFiniteEnergyClass : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → IsFiniteEnergyTrain tr

/-- Reduction target (for the Haiku task): the jet energies of the error tend to `0` once the
velocity and `V_c^p` are `H^k(cell)`-continuous at age `0`. -/
def TrainJetEnergyToZero_reduction : Prop :=
  VcCellL2Cont → TrainFiniteEnergyClass → TrainJetEnergyToZero

end UnforcedLeray.Short.PartI
