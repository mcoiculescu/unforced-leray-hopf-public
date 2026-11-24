import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.DuhamelSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Helper for `ComplWeakEq` (`PartIII-a:T21/c3/3/1/1/2/2/3`): the two central missing leaves

Source `the November 2 reference manuscript` (SP) lines 2905-2925, 2937-2958.


against a moving free adjoint `Φ`.  Writing `⟨W⊥, Φ⟩ = ⟨W, Φ⟩ - Σ_j α_j ⟨E_j, Φ⟩`, it needs
(i) the physical pairing of the linearised flow with the free adjoint (`LinFreeAdjPairing`: the
derivative is the interaction term only), (ii) the amplitude equation `α' = H₀W` (`AmplWeakFTC`,
proved only for `ν ≤ ν₀(b)`, `b ≥ b₀`), (iii) the pairing of the frame columns `E_j(r)` with
`Φ(r)` (free adjoint tested against a smooth, non-compactly supported, time-dependent function),
(iv) the exact identity `H₀E = ΛK₀` (`H0ModeIdentity`; `K₀ = GE - E_z`, SP 2915-2918), which makes
the mode terms collapse to `Σ α_j (1 - EΛ)(movOscRes_j + movEulerRes_j)`, and (v) the moving form of
the interaction term (`u` versus `kerVelCx (dd ν r) (movingW ν w r)`, zero circulation).
Without train decay (`LadTrainBdd`) or `ν ≤ ν₀`, the pairing `∫ (u·∇E) φ` need not converge, so
the leaves carry `LadTrainBdd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

namespace Leaf2WeakEqNeeded

/-- **Leaf (i)** (SP 2937-2958): the physical pairing of the weak linearised flow with a regular
free adjoint flow changes only by the interaction term `-(u·∇E)`. -/
def LinFreeAdjPairing (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u → HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    ∀ s ∈ Icc t₁ t₂, ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ →
      ∀ r ∈ Icc t₁ s,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * g x =
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * φ r x) -
            ∫ r' in r..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
              (u r' x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r') x : ℝ) : ℂ) +
                u r' x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r') x : ℝ) : ℂ)) * φ r' x

/-- **Leaf (iv)** (SP 2915-2918): `M₀ = H₀E = ΛK₀`: the moving-time derivative functional `H₀` on
the frame columns equals the dual rows applied to `K₀ = GE - E_z`, i.e. to
`movOscRes + movEulerRes + λ_j E_j`. -/
def H0ModeIdentity (κ : PlanarFrameKernels) (P : PlanarData) (ν b : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) : Prop :=
  ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r → ∀ i j : Fin 2,
    movH0 κ tr r i (perE κ (dd ν r) j) =
      ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, perLam κ (dd ν r) i y *
        (movOscRes κ ν r j y + movEulerRes κ P tr r j y + modeEigen P j * perE κ (dd ν r) j y)

end Leaf2WeakEqNeeded

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
