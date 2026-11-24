import UnforcedLeray.Short.PartI.Sub.T08Statement

/-!
# Part I, task `PartI:T08/4` (`TrainJetEnergyBalance`): decomposition

Source `the November 2 reference manuscript` lines 341-348 and the error equation
326-329. Two leaves: time differentiation of the cell energy (derivative under the integral over
the uncut cell), and the algebraic splitting of `⟨D^j e, D^j ∂_s e⟩` by the error equation.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf A: differentiated cell energy** (line 346). At every age `s > 0` with `a(s) ≤ c²`,
`r ↦ ‖D^j e(r)‖₂²` is differentiable at `s` with derivative `2⟨D^j e(s), D^j ∂_s e(s)⟩`
(differentiate under the integral over the cell; `∂_r D^w e` is in `L²(cell)` locally uniformly in
`r`, `TrainTimeDerivL2` and `TrainErrJetL2`, time and space derivatives commute by joint
smoothness of `v` and `V_c`). -/
def TrainJetEnergyTimeDeriv : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ j : ℕ,
      HasDerivAt (fun r => jetEnergy c j (trainErr tr r))
        (2 * jetPair c j (trainErr tr s) (fun y => deriv (fun t => trainErr tr t y) s)) s

/-- **Leaf B: the error equation inside the pairing** (lines 326-329, 346). Substituting
`∂_s e = νΔe - A - ∇π - div Q_c` (`train_error_equation`) and splitting the pairing, which is
linear in its second argument on fields with `L²` word derivatives
(`TrainErrLaplacianL2`, `TrainAdvDiffL2`, `TrainPressureRegular`, `TrainStressDivL2`). -/
def TrainJetPairSplit : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ j : ℕ,
      jetPair c j (trainErr tr s) (fun y => deriv (fun t => trainErr tr t y) s)
        = ν * jetPair c j (trainErr tr s) (Train.vecLaplacian (trainErr tr s))
          - jetPair c j (trainErr tr s) (advDiff tr s)
          - jetPair c j (trainErr tr s) (Train.gradS (errPressure tr s))
          - jetPair c j (trainErr tr s) (Train.matDiv (Qc ν c s))

theorem trainJetEnergyBalance_of (hA : TrainJetEnergyTimeDeriv) (hB : TrainJetPairSplit) :
    TrainJetEnergyBalance := by
  intro ν c hν hc tr htr s hs hac j
  have := hA ν c hν hc tr htr s hs hac j
  have h2 := hB ν c hν hc tr htr s hs hac j
  rw [h2] at this
  exact this

end UnforcedLeray.Short.PartI
