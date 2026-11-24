import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Needed
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Regular.SourceMemLp

/-!
# Design for `ComplWeakEq` (`PartIII-a:T21/c3/3/1/1/2/2/3`), SP 2898-2958

`ComplWeakEq` (DuhamelSplit.lean) now carries `LadTrainBdd`, finiteness of the mode forcings
(the body of `ForceFinite`) and the amplitude FTC `α(s') - α(r) = ∫ a⁻² H₀(movingW)` as
hypotheses.  The leaf Props below discharge them / supply the pairings:
(a) `Leaf2WeakEqNeeded.LinFreeAdjPairing`, (b) `AmplFTCUnnorm` (here), (d) `H0ModeIdentity`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqDesign

/-- **Leaf (b)** (SP 2898-2918): the un-normalised amplitude FTC along a linearised flow, for
`b ≥ b₀`, `ν ≤ ν₀`. -/
def AmplFTCUnnorm (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ b₀ : ℝ, 1 ≤ b₀ ∧
    ∀ b : ℝ, b₀ ≤ b →
      ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ ν : ℝ, (hν : ν ∈ Ioc 0 ν₀) → ∀ (hF : PerFrameFacts κ ν m b K),
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ r ∈ Icc t₁ t₂, ∀ s' ∈ Icc r t₂, ∀ i : Fin 2,
            ampl (periodizedFrame κ ν m b K hν.1 hF) w s' i -
                ampl (periodizedFrame κ ν m b K hν.1 hF) w r i =
              ∫ q in Ioc r s', (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
                movH0 κ tr q i (movingW ν w q)

end Leaf2WeakEqDesign

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
