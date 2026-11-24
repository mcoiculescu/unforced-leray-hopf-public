import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Needed
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1

/-!
# Frame-column pairing leaves for `ComplWeakEq` (`PartIII-a:T21/c3/3/1/1/2/2/3/c`)

Source `the November 2 reference manuscript` (SP) lines 2905-2925, 2937-2958.
Consumer: `PartIII-a:T21/c3/3/1/1/2/2/3`, which writes `W⊥ = W - Σ α_j E_j` and pairs each term with
the moving free adjoint `Φ`.
* `FramePairingFTC`: the moving pairing `r ↦ ⟨E_j(r), Φ(r)⟩`, `E_j = perE κ d(r) j`, is the integral of
  `a⁻² ⟨interactionTerm E_j - (movOscRes_j + movEulerRes_j + λ_j E_j), Φ⟩`
  (`K₀ = GE - E_z`, `GE - E_z = movOscRes + movEulerRes + λ E`; the free part of `G E` is
  `GE - interactionTerm E`).  Proof: cutoff of the non-compactly supported test column as in
  `NormAmplCutFTC` (`PartIII-a:T21/c5/1`), limit by `LadTrainBdd`.
* `MovingInteractionForm`: `∫ (u·∇E_c) φ = -a⁻² ∫ interactionTerm (movingW w) movingPhi φ`, by
  Biot-Savart uniqueness (`T21_2_1/Kernel/Unique.lean`) identifying `u` with `kerVelCx` of `W`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqFrame

/-- **Frame pairing leaf** (SP 2905-2925, 2937-2958): for `ν ≤ ν₀(b)`, `b ≥ b₀`, and a moving free
adjoint `Φ` of terminal datum `Γ` on `[t₁, s]`, for `t₁ ≤ r ≤ s' ≤ s`,
`⟨E_j(s'), Φ(s')⟩ - ⟨E_j(r), Φ(r)⟩ =
  ∫_{(r,s']} a⁻² ⟨interactionTerm E_j - (movOscRes_j + movEulerRes_j + λ_j E_j), Φ⟩`. -/
def FramePairingFTC (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ b₀ : ℝ, 1 ≤ b₀ ∧
    ∀ b : ℝ, b₀ ≤ b →
      ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
        ∀ t₁ s : ℝ, 0 ≤ t₁ → t₁ ≤ s → b ≤ clockTheta ν s →
        ∀ (Γ : ℝ × ℝ → ℂ) (Φ : ℝ → ℝ × ℝ → ℂ),
          MemLp Γ 2 (B0579.cellMeasure (dd ν s) (-m)) → MovingFreeAdjoint ν m tr t₁ s Γ Φ →
          ∀ r ∈ Icc t₁ s, ∀ s' ∈ Icc r s, ∀ j : Fin 2,
            (∫ y in B0579.cell (dd ν s'), perE κ (dd ν s') j y * Φ s' y) -
                ∫ y in B0579.cell (dd ν r), perE κ (dd ν r) j y * Φ r y =
              ∫ q in Ioc r s', (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
                ∫ y in B0579.cell (dd ν q),
                  (interactionTerm tr q (perE κ (dd ν q) j) y -
                    (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
                      modeEigen P j * perE κ (dd ν q) j y)) * Φ q y

/-- **Moving form of the interaction pairing** (SP 2863-2865, 2937-2958): for a linearised flow
with zero-circulation datum and a regular physical free adjoint `φ` (`r ∈ [t₁, s)`), the physical
term `∫ (u·∇E_c) φ` equals `-a(r)⁻²` times the moving pairing of `interactionTerm tr r (W(r))`
with `Φ(r) = movingPhi φ r`. -/
def MovingInteractionForm (ν m : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u → HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    ∀ (s : ℝ) (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ →
      ∀ r ∈ Ico t₁ s,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            (u r x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
              u r x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) * φ r x =
          -((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ∫ y in B0579.cell (dd ν r),
              interactionTerm tr r (movingW ν w r) y * movingPhi ν φ r y)

end Leaf2WeakEqFrame

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
