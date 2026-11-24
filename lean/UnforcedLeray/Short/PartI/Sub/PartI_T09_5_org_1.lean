import UnforcedLeray.Short.PartI.Sub.PartI_T09_5

/-!
# `PartI:T09/5/org/1`: right-continuity of the jet energies of the train error

Source: `the November 2 reference manuscript`,
lines 270-288, 294, 341-344.  `IsBUCTrain` (bounded derivatives on `[0,S] x R^2`) carries no
`L^2` information in time, so the right-continuity at age `0` of the jet energies of
`e = v - V_c^p` is isolated as `TrainJetEnergyToZero` (the finite-energy continuation of lines
281-288: mild `L^2` bound plus the energy identities).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- **Source lemma (lines 281-288, 294):** for a BUC train every jet energy of the comparison error
tends to `0` as the age tends to `0` from the right. -/
def TrainJetEnergyToZero : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ j : ℕ,
    Tendsto (fun s => jetEnergy c j (trainErr tr s)) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0)

theorem trainJetEnergyRightCont_proof_of (h : TrainJetEnergyToZero) : TrainJetEnergyRightCont := by
  intro ν c hν hc tr htr j
  have h0 : jetEnergy c j (trainErr tr 0) = 0 := by
    rw [trainErr_zero_local tr]; exact jetEnergy_zero_local c j
  unfold ContinuousWithinAt
  show Tendsto _ _ (𝓝 (jetEnergy c j (trainErr tr 0)))
  rw [h0]
  exact h ν c hν hc tr htr j

end UnforcedLeray.Short.PartI
