import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_org_switch
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L3_good

/-!
# Regime form of the variation-of-constants subtree (`ORG:T21-c3-2-regime`)

Source of record: `the November 2 reference manuscript` (SP), lines 2836-2852
(`prop:short-full-clock`: a fixed sufficiently large `b`, all sufficiently small `ν`), 2914-2925
(generator identity, `eq:short-causal-damped-complement`), 2974-2982 (`A_rel` is bounded for
`b ≥ b_prop`, `ν ≤ ν_prop(b)`), 3050-3051 (standing smallness).

Regime.  `FrameBlockContraction` (`Sub/PartIII-a_T21_c3.lean:88`) quantifies
`∀ m K, ∃ B C_B b₁, ∀ b ≥ b₁, ∃ ν₁, ∀ ν ∈ (0, ν₁]`: the block length `B` is fixed before the
threshold of `b`, and `ν₁` depends on `b`.  Every leaf of the block variation-of-constants identity
is therefore stated with `∀ K B, 0 < B → ∃ b₀, ∀ b ≥ b₀, 1 ≤ b → ∃ ν₀ > 0, ∀ ν ∈ (0, ν₀]`, the
shape of `ComplBlockDuhamelVoCReg` and `RelBlockRegularityReg`; thresholds combine by `max`/`min`.
Inputs that hold more uniformly enter as they are: `MovSolTestedDuhamelSmall` (`ν ≤ ν₀(m)`),
`ARelRoughSub.ARelRoughReg` (`b ≥ b₀(K)`, uniform in `B`), `FrelDiag` and `FrameTestedDuhamel`
(all `ν`).

The `…Regime` Props below have the bodies of the all-`ν` Props of
`Sub/PartIII-a_T21_c3_2_1_2_3_3_1.lean` and `Sub/PartIII-a_T21_c3_2_1_2_3_3_1_1_org_switch.lean`;
the assemblies are the proofs of `modeTestedDuhamel_of`, `complGeneratorSplit_of`,
`complMildTestedSmall_of`, `complMildEqRegSmall_of_tested`, `complMovingMildRegSmall_of` and
`complBlockDuhamelSplitReg_of_mildSmall` with the thresholds combined.  Final assembly:
`complBlockDuhamelVoCReg_of_regime`.  Leaf 1 for `ν ≤ ν₀(m)`: `MovSolDuhamelOfSmall`,
`movSolTestedDuhamelSmall_of'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub ComplMildSplit

namespace ComplMildTestedSplit

namespace Regime

/-! ## Regime forms of the leaves and of the intermediate identities -/

/-- `ModeTestedDuhamel` (SP 2898-2918, 2991-2997) in the regime `b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def ModeTestedDuhamelRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∃ FM : ℝ → Planar.L2w m, FMRep κ P m b K B ν hν hF tr t₁ w FM ∧
              ∀ M : ℝ → Planar.L2w m, MRep κ P m b K B ν hν hF t₁ w M →
                ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                  IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (FM σ)⟫_ℂ) volume 0 τ ∧
                  ⟪ψ, M τ⟫_ℂ = ⟪ψ, F_rel τ 0 (M 0)⟫_ℂ +
                    ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (FM σ)⟫_ℂ

/-- `AmplMovingFTC` (`(ΛW)' = H₀W` in moving time, SP 2916-2918, 2991-3000) in the regime
`b ≥ b₀`, `ν ≤ ν₀(b)` (the proved amplitude identity `AmplWeakFTC` holds there). -/
def AmplMovingFTCRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ j : Fin 2,
            IntervalIntegrable (nAmplDz κ P m b K ν hν hF tr t₁ w j) volume 0 B ∧
            ∀ σ₀ ∈ Icc (0 : ℝ) B, nAmpl κ P m b K ν hν hF t₁ w j σ₀ =
              nAmpl κ P m b K ν hν hF t₁ w j 0 +
                ∫ σ in (0 : ℝ)..σ₀, nAmplDz κ P m b K ν hν hF tr t₁ w j σ

/-- `ComplGeneratorSplit` (SP 2914-2925) in the regime `b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def ComplGeneratorSplitRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ Y G LV FM : ℝ → Planar.L2w m,
              YRep κ P m b K B ν hν hF t₁ w Y → GRep κ P m b K B ν hν hF tr t₁ w G →
              LVRep P m B ν tr t₁ w LV → FMRep κ P m b K B ν hν hF tr t₁ w FM →
              ∀ σ ∈ Icc (0 : ℝ) B, A_rel σ (Y σ) + G σ = LV σ - FM σ

/-- `MovDualMemLp` (the kernel of `H₀` lies in `X_{-m,d(s)}`, SP 2898-2918) in the regime
`b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def MovDualMemLpRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ i : Fin 2,
          MemLp (movingPhi ν (fun r' => physLamDual κ tr r' i) (ageAt ν t₁ σ)) 2
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) (-m))

/-- `MovH0Frame` (`M₀ = H₀E = ΛK₀`, SP 2916-2918) in the regime `b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def MovH0FrameRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ i k : Fin 2,
          movH0 κ tr (ageAt ν t₁ σ) i
              (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) k) =
            movM0 κ P tr (ageAt ν t₁ σ) i k

/-- `MovK0MemLp` (`K₀ = GE - E_z ∈ X_{m,d(s)}`, SP 2905, 2916) in the regime `b ≥ b₀`,
`ν ≤ ν₀(b)`. -/
def MovK0MemLpRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ j : Fin 2,
          MemLp (movK0 κ P tr (ageAt ν t₁ σ) j) 2
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m)

/-- `ComplMildTested` (tested mild identity of the normalised complement, SP 2914-2925,
2937-2945) in the regime `b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def ComplMildTestedRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ Y G : ℝ → Planar.L2w m,
              YRep κ P m b K B ν hν hF t₁ w Y → GRep κ P m b K B ν hν hF tr t₁ w G →
              AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) →
              (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) →
              IntegrableOn G (Icc (0 : ℝ) B) →
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                ⟪ψ, Y τ⟫_ℂ = ⟪ψ, F_rel τ 0 (Y 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (A_rel σ (Y σ) + G σ)⟫_ℂ

/-- `ComplMildEqReg` (mild identity under the regularity of leaf B) in the regime `b ≥ b₀`,
`ν ≤ ν₀(b)`. -/
def ComplMildEqRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ((∀ x : Planar.L2w m,
            ContinuousOn (fun p : ℝ × ℝ => F_rel p.1 p.2 x) (blockTriangle B)) ∧
          (∀ x : Planar.L2w m,
            AEStronglyMeasurable (fun r => A_rel r x) (volume.restrict (Icc (0 : ℝ) B))) ∧
          (∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A)) →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ Y G : ℝ → Planar.L2w m,
              YRep κ P m b K B ν hν hF t₁ w Y → GRep κ P m b K B ν hν hF tr t₁ w G →
              AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) →
              (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) →
              IntegrableOn G (Icc (0 : ℝ) B) →
              ∀ τ ∈ Icc (0 : ℝ) B,
                Y τ = F_rel τ 0 (Y 0) +
                  ∫ σ in (0 : ℝ)..τ, F_rel τ σ (A_rel σ (Y σ) + G σ)

/-- `ComplMovingMildReg` (leaf C: `Y`, `G` and the mild identity, SP 2914-2925, 2974-2982) in
the regime `b ≥ b₀`, `ν ≤ ν₀(b)`. -/
def ComplMovingMildRegime (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ν ≤ ν₀ → ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ((∀ x : Planar.L2w m,
            ContinuousOn (fun p : ℝ × ℝ => F_rel p.1 p.2 x) (blockTriangle B)) ∧
          (∀ x : Planar.L2w m,
            AEStronglyMeasurable (fun r => A_rel r x) (volume.restrict (Icc (0 : ℝ) B))) ∧
          (∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A)) →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            let F := periodizedFrame κ ν m b K hν hF
            ∃ Y G : ℝ → Planar.L2w m,
              (∀ τ ∈ Icc (0 : ℝ) B, ⇑(Y τ) =ᵐ[volume] fun z : ℂ =>
                ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
                    (compl F w (ageAt ν t₁ τ)) (cToPlane z)) ∧
              (∀ σ ∈ Icc (0 : ℝ) B, ⇑(G σ) =ᵐ[volume] fun z : ℂ =>
                ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
                    (fun y => ∑ j : Fin 2, ampl F w (ageAt ν t₁ σ) j *
                      complModeForce κ P F tr (ageAt ν t₁ σ) j y) (cToPlane z)) ∧
              AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) ∧
              (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) ∧
              IntegrableOn G (Icc (0 : ℝ) B) ∧
              (∀ τ ∈ Icc (0 : ℝ) B,
                Y τ = F_rel τ 0 (Y 0) +
                  ∫ σ in (0 : ℝ)..τ, F_rel τ σ (A_rel σ (Y σ) + G σ)) ∧
              AEStronglyMeasurable (compl F w t₁)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m) ∧
              AEStronglyMeasurable (compl F w t₂)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m) ∧
              ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
                AEStronglyMeasurable (complModeForce κ P F tr r j)
                  (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)

/-! ## Assemblies -/

/-- An all-`ν` amplitude identity gives the regime form (thresholds `b₀ = ν₀ = 1`). -/
theorem amplMovingFTCRegime_of_all (κ : PlanarFrameKernels) (h : AmplMovingFTC κ) :
    AmplMovingFTCRegime κ := by
  intro hκ P hP m hm K B hB
  exact ⟨1, fun b _ hb => ⟨1, one_pos, fun ν hν _ hF => h hκ P hP m hm K B b hB hb ν hν hF⟩⟩

/-- **Leaf 2 in the regime** (proof of `modeTestedDuhamel_of`). -/
theorem modeTestedDuhamelRegime_of (κ : PlanarFrameKernels) (hD : FrelDiag)
    (hE : FrameTestedDuhamel κ) (hA : AmplMovingFTCRegime κ) : ModeTestedDuhamelRegime κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := hA hκ P hP m hm K B hB
  refine ⟨b₀, fun b hbb hb => ?_⟩
  obtain ⟨ν₀, hν₀, hA'⟩ := hb₀ b hbb hb
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
  choose Ej Rj hErep hRrep hEd using
    hE hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr
  have hAm := hA' ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  have hDg := hD P hP m hm B b hB hb ν hν tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr
  refine ⟨fun σ => (nAmpl κ P m b K ν hν hF t₁ w 0 σ • Rj 0 σ +
      nAmplDz κ P m b K ν hν hF tr t₁ w 0 σ • Ej 0 σ) +
    (nAmpl κ P m b K ν hν hF t₁ w 1 σ • Rj 1 σ +
      nAmplDz κ P m b K ν hν hF tr t₁ w 1 σ • Ej 1 σ), ?_, ?_⟩
  · intro σ hσ
    filter_upwards [coeFn_lin4 _ _ _ _ (Rj 0 σ) (Ej 0 σ) (Rj 1 σ) (Ej 1 σ), hRrep 0 σ hσ,
      hRrep 1 σ hσ, hErep 0 σ hσ, hErep 1 σ hσ] with z h0 h1 h2 h3 h4
    rw [h0, h1, h2, h3, h4]
    unfold cellZeroExt
    by_cases hc : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
    · simp only [Set.indicator_of_mem hc, Fin.sum_univ_two, periodizedFrame_E]
      unfold nAmplDz nAmpl
      ring
    · simp only [Set.indicator_of_notMem hc, mul_zero, add_zero]
  · intro M hM τ hτ ψ hψ
    have hMdec : ∀ σ ∈ Icc (0 : ℝ) B, M σ = nAmpl κ P m b K ν hν hF t₁ w 0 σ • Ej 0 σ +
        nAmpl κ P m b K ν hν hF t₁ w 1 σ • Ej 1 σ := by
      intro σ hσ
      apply Lp.ext
      refine (Planar.wMeasure_ac m).ae_le ?_
      filter_upwards [hM σ hσ, coeFn_lin2 (nAmpl κ P m b K ν hν hF t₁ w 0 σ)
        (nAmpl κ P m b K ν hν hF t₁ w 1 σ) (Ej 0 σ) (Ej 1 σ), hErep 0 σ hσ, hErep 1 σ hσ]
        with z h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      unfold cellZeroExt
      by_cases hc : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
      · simp only [Set.indicator_of_mem hc, Fin.sum_univ_two, periodizedFrame_E]
        unfold nAmpl
        ring
      · simp only [Set.indicator_of_notMem hc, mul_zero, add_zero]
    have hsub : uIcc (0 : ℝ) τ ⊆ uIcc 0 B := by
      rw [uIcc_of_le hτ.1, uIcc_of_le hB.le]
      exact Icc_subset_Icc le_rfl hτ.2
    have hprod : ∀ j : Fin 2,
        IntervalIntegrable (fun x => nAmplDz κ P m b K ν hν hF tr t₁ w j x *
          ⟪ψ, F_rel τ x (Ej j x)⟫_ℂ) volume 0 τ ∧
        IntervalIntegrable (fun x => nAmpl κ P m b K ν hν hF t₁ w j x *
          ⟪ψ, F_rel τ x (Rj j x)⟫_ℂ) volume 0 τ ∧
        nAmpl κ P m b K ν hν hF t₁ w j τ * ⟪ψ, F_rel τ τ (Ej j τ)⟫_ℂ -
            nAmpl κ P m b K ν hν hF t₁ w j 0 * ⟪ψ, F_rel τ 0 (Ej j 0)⟫_ℂ =
          ∫ x in (0 : ℝ)..τ, (nAmplDz κ P m b K ν hν hF tr t₁ w j x *
              ⟪ψ, F_rel τ x (Ej j x)⟫_ℂ +
            nAmpl κ P m b K ν hν hF t₁ w j x * ⟪ψ, F_rel τ x (Rj j x)⟫_ℂ) := by
      intro j
      obtain ⟨hβi, hqrep⟩ := hEd j τ hτ ψ hψ
      obtain ⟨hai, harep⟩ := hAm j
      exact mul_sub_mul_of_primitive (a := fun x => nAmpl κ P m b K ν hν hF t₁ w j x)
        (q := fun x => ⟪ψ, F_rel τ x (Ej j x)⟫_ℂ) hτ.1 (hai.mono_set hsub) hβi
        (fun x hx => harep x ⟨hx.1, hx.2.trans hτ.2⟩) hqrep
    have hpt : ∀ σ, ⟪ψ, F_rel τ σ ((nAmpl κ P m b K ν hν hF t₁ w 0 σ • Rj 0 σ +
        nAmplDz κ P m b K ν hν hF tr t₁ w 0 σ • Ej 0 σ) +
        (nAmpl κ P m b K ν hν hF t₁ w 1 σ • Rj 1 σ +
          nAmplDz κ P m b K ν hν hF tr t₁ w 1 σ • Ej 1 σ))⟫_ℂ =
        (nAmplDz κ P m b K ν hν hF tr t₁ w 0 σ * ⟪ψ, F_rel τ σ (Ej 0 σ)⟫_ℂ +
            nAmpl κ P m b K ν hν hF t₁ w 0 σ * ⟪ψ, F_rel τ σ (Rj 0 σ)⟫_ℂ) +
          (nAmplDz κ P m b K ν hν hF tr t₁ w 1 σ * ⟪ψ, F_rel τ σ (Ej 1 σ)⟫_ℂ +
            nAmpl κ P m b K ν hν hF t₁ w 1 σ * ⟪ψ, F_rel τ σ (Rj 1 σ)⟫_ℂ) := by
      intro σ
      simp only [map_add, map_smul, inner_add_right, inner_smul_right]
      ring
    have hfun : (fun σ => ⟪ψ, F_rel τ σ ((nAmpl κ P m b K ν hν hF t₁ w 0 σ • Rj 0 σ +
        nAmplDz κ P m b K ν hν hF tr t₁ w 0 σ • Ej 0 σ) +
        (nAmpl κ P m b K ν hν hF t₁ w 1 σ • Rj 1 σ +
          nAmplDz κ P m b K ν hν hF tr t₁ w 1 σ • Ej 1 σ))⟫_ℂ) =
        fun σ => (nAmplDz κ P m b K ν hν hF tr t₁ w 0 σ * ⟪ψ, F_rel τ σ (Ej 0 σ)⟫_ℂ +
            nAmpl κ P m b K ν hν hF t₁ w 0 σ * ⟪ψ, F_rel τ σ (Rj 0 σ)⟫_ℂ) +
          (nAmplDz κ P m b K ν hν hF tr t₁ w 1 σ * ⟪ψ, F_rel τ σ (Ej 1 σ)⟫_ℂ +
            nAmpl κ P m b K ν hν hF t₁ w 1 σ * ⟪ψ, F_rel τ σ (Rj 1 σ)⟫_ℂ) :=
      funext hpt
    obtain ⟨i0a, i0b, e0⟩ := hprod 0
    obtain ⟨i1a, i1b, e1⟩ := hprod 1
    rw [hDg τ hτ] at e0 e1
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (i0a.add i0b).add (i1a.add i1b)
    · rw [hfun, intervalIntegral.integral_add (i0a.add i0b) (i1a.add i1b), ← e0, ← e1,
        hMdec τ hτ, hMdec 0 ⟨le_rfl, hB.le⟩]
      simp only [map_add, map_smul, inner_add_right, inner_smul_right]
      ring

/-- **Leaf 3 in the regime** (proof of `complGeneratorSplit_of`; the rough extension is the proved
`ARelRoughSub.aRelRoughReg`). -/
theorem complGeneratorSplitRegime_of (κ : PlanarFrameKernels)
    (h1 : ARelRoughSub.ARelRoughReg κ) (h4 : MovDualMemLpRegime κ) (h5 : MovH0FrameRegime κ)
    (h6 : MovK0MemLpRegime κ) : ComplGeneratorSplitRegime κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₁, -, hb₁⟩ := h1 hκ P hP m hm K
  obtain ⟨b₄, hb₄⟩ := h4 hκ P hP m hm K B hB
  obtain ⟨b₅, hb₅⟩ := h5 hκ P hP m hm K B hB
  obtain ⟨b₆, hb₆⟩ := h6 hκ P hP m hm K B hB
  refine ⟨max (max b₁ b₄) (max b₅ b₆), fun b hbb hb => ?_⟩
  obtain ⟨ν₁, hν₁, -, H1⟩ := hb₁ B b hB ((le_max_left _ _).trans ((le_max_left _ _).trans hbb))
  obtain ⟨ν₄, hν₄, H4⟩ := hb₄ b ((le_max_right _ _).trans ((le_max_left _ _).trans hbb)) hb
  obtain ⟨ν₅, hν₅, H5⟩ := hb₅ b ((le_max_left _ _).trans ((le_max_right _ _).trans hbb)) hb
  obtain ⟨ν₆, hν₆, H6⟩ := hb₆ b ((le_max_right _ _).trans ((le_max_right _ _).trans hbb)) hb
  refine ⟨min (min ν₁ ν₄) (min ν₅ ν₆), lt_min (lt_min hν₁ hν₄) (lt_min hν₅ hν₆), ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr f w u hFlow hCirc Y G LV FM hY hG hLV
    hFM σ hσ
  have e1 : ν ≤ ν₁ := hνs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e4 : ν ≤ ν₄ := hνs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e5 : ν ≤ ν₅ := hνs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e6 : ν ≤ ν₆ := hνs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsI : ageAt ν t₁ σ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν ht₁ h12 hBe hσ
  have hbs : b ≤ clockTheta ν (ageAt ν t₁ σ) :=
    hbt.trans (clockTheta_le_of_le hν (ht₁.trans hsI.1) hsI.2)
  exact gen_core κ P hm hb hν hF tr hFlow ht₁ (ageAt ν t₁ σ) hsI.1 hbs
    (H4 ν hν e4 hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (H5 ν hν e5 hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (H6 ν hν e6 hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (A_rel σ) (H1 ν ⟨hν, e1⟩ hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr σ hσ)
    _ (Y σ) (G σ) (LV σ) (FM σ) (hY σ hσ) (hG σ hσ) (hLV σ hσ) (hFM σ hσ)

/-- **`ComplMildTested` in the regime** (proof of `complMildTestedSmall_of`). -/
theorem complMildTestedRegime_of (κ : PlanarFrameKernels) (hV : MovSolTestedDuhamelSmall)
    (hM : ModeTestedDuhamelRegime κ) (hA : ComplGeneratorSplitRegime κ) :
    ComplMildTestedRegime κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨ν₁, hν₁, hV⟩ := hV m hm
  obtain ⟨bM, hbM⟩ := hM hκ P hP m hm K B hB
  obtain ⟨bA, hbA⟩ := hA hκ P hP m hm K B hB
  refine ⟨max bM bA, fun b hbb hb => ?_⟩
  obtain ⟨νM, hνM, hM'⟩ := hbM b ((le_max_left _ _).trans hbb) hb
  obtain ⟨νA, hνA, hA'⟩ := hbA b ((le_max_right _ _).trans hbb) hb
  refine ⟨min ν₁ (min νM νA), lt_min hν₁ (lt_min hνM hνA), ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
    f w u hFlow hCirc Y G hY hG _hYm _hYb _hGi τ hτ ψ hψ
  have e1 : ν ≤ ν₁ := hνs.trans (min_le_left _ _)
  have eM : ν ≤ νM := hνs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have eA : ν ≤ νA := hνs.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨V, LV, hVr, hLVr, hVd⟩ :=
    hV P hP B b hB hb ν hν e1 tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
  obtain ⟨FM, hFMr, hMd⟩ :=
    hM' ν hν eM hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
  have hgen := hA' ν hν eA hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr
    f w u hFlow hCirc Y G LV FM hY hG hLVr hFMr
  obtain ⟨hIV, hEV⟩ := hVd τ hτ ψ hψ
  obtain ⟨hIM, hEM⟩ :=
    hMd (fun σ => V σ - Y σ) (mRep_sub κ P m b K B ν hν hF t₁ w V Y hVr hY) τ hτ ψ hψ
  have hYτ : Y τ = V τ - (V τ - Y τ) := by abel
  have hcongr : ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (A_rel σ (Y σ) + G σ)⟫_ℂ =
      ∫ σ in (0 : ℝ)..τ, (⟪ψ, F_rel τ σ (LV σ)⟫_ℂ - ⟪ψ, F_rel τ σ (FM σ)⟫_ℂ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le hτ.1] at hσ
    have hσB : σ ∈ Icc (0 : ℝ) B := ⟨hσ.1, hσ.2.trans hτ.2⟩
    simp only [hgen σ hσB, map_sub, inner_sub_right]
  rw [hcongr, intervalIntegral.integral_sub hIV hIM, hYτ, inner_sub_right, hEV, hEM,
    map_sub, inner_sub_right]
  ring

/-- **Mild identity in the regime** (proof of `complMildEqRegSmall_of_tested`: density of the
smooth class). -/
theorem complMildEqRegime_of_tested (κ : PlanarFrameKernels)
    (hT : ComplMildTestedRegime κ) : ComplMildEqRegime κ := by
  intro hκ P hP m hm K B hB0
  obtain ⟨b₀, hb₀⟩ := hT hκ P hP m hm K B hB0
  refine ⟨b₀, fun b hbb hb => ?_⟩
  obtain ⟨ν₀, hν₀, hT⟩ := hb₀ b hbb hb
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF
    f w u hw hcirc Y G hY hG hYm hYb hGi τ hτ
  obtain ⟨hFc, hAm, K_A, hKA⟩ := hRegF
  obtain ⟨C_Y, hCY⟩ := hYb
  have hFτ : ∀ x, ContinuousOn (fun σ => F_rel τ σ x) (Icc 0 τ) := by
    intro x
    have hmaps : MapsTo (fun σ : ℝ => (τ, σ)) (Icc 0 τ) (blockTriangle B) :=
      fun σ hσ => ⟨hσ.1, hσ.2, hτ.2⟩
    exact (hFc x).comp (continuousOn_const.prodMk continuousOn_id) hmaps
  obtain ⟨M, hM⟩ := exists_bound_of_continuousOn_apply isCompact_Icc (F_rel τ) hFτ
  have hsub : Icc 0 τ ⊆ Icc 0 B := Icc_subset_Icc le_rfl hτ.2
  have hμ : volume.restrict (Icc 0 τ) ≤ volume.restrict (Icc (0 : ℝ) B) :=
    Measure.restrict_mono hsub le_rfl
  have hYm' : AEStronglyMeasurable Y (volume.restrict (Icc 0 τ)) := hYm.mono_measure hμ
  have hAm' : ∀ x, AEStronglyMeasurable (fun r => A_rel r x) (volume.restrict (Icc 0 τ)) :=
    fun x => (hAm x).mono_measure hμ
  have hGi' : IntegrableOn G (Icc 0 τ) := hGi.mono_set hsub
  have hAY : AEStronglyMeasurable (fun σ => A_rel σ (Y σ)) (volume.restrict (Icc 0 τ)) :=
    aesm_clm_apply A_rel hAm' hYm'
  have hFm : ∀ x, AEStronglyMeasurable (fun σ => F_rel τ σ x) (volume.restrict (Icc 0 τ)) :=
    fun x => (hFτ x).aestronglyMeasurable measurableSet_Icc
  have hhm : AEStronglyMeasurable (fun σ => F_rel τ σ (A_rel σ (Y σ) + G σ))
      (volume.restrict (Icc 0 τ)) :=
    aesm_clm_apply (F_rel τ) hFm (hAY.add hGi'.aestronglyMeasurable)
  have hhi : IntegrableOn (fun σ => F_rel τ σ (A_rel σ (Y σ) + G σ)) (Icc 0 τ) := by
    refine Integrable.mono' ((integrable_const (max M 0 * (max K_A 0 * max C_Y 0))).add
      (hGi'.norm.const_mul (max M 0))) hhm ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    have hσB : σ ∈ Icc 0 B := hsub hσ
    have h1 : ‖F_rel τ σ‖ ≤ max M 0 := (hM σ hσ).trans (le_max_left _ _)
    have h2 : ‖A_rel σ‖ ≤ max K_A 0 := (hKA σ hσB).trans (le_max_left _ _)
    have h3 : ‖Y σ‖ ≤ max C_Y 0 := (hCY σ hσB).trans (le_max_left _ _)
    have h4 : ‖A_rel σ (Y σ)‖ ≤ max K_A 0 * max C_Y 0 :=
      ((A_rel σ).le_opNorm _).trans (mul_le_mul h2 h3 (norm_nonneg _) (le_max_right _ _))
    calc ‖F_rel τ σ (A_rel σ (Y σ) + G σ)‖
        ≤ ‖F_rel τ σ‖ * ‖A_rel σ (Y σ) + G σ‖ := (F_rel τ σ).le_opNorm _
      _ ≤ max M 0 * (max K_A 0 * max C_Y 0 + ‖G σ‖) :=
          mul_le_mul h1 ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
            (le_max_right _ _)
      _ = max M 0 * (max K_A 0 * max C_Y 0) + max M 0 * ‖G σ‖ := by ring
  have hint : ∀ ψ : Planar.L2w m,
      ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (A_rel σ (Y σ) + G σ)⟫_ℂ =
        ⟪ψ, ∫ σ in (0 : ℝ)..τ, F_rel τ σ (A_rel σ (Y σ) + G σ)⟫_ℂ := by
    intro ψ
    rw [intervalIntegral.integral_of_le hτ.1, intervalIntegral.integral_of_le hτ.1]
    exact integral_inner (hhi.mono_set Ioc_subset_Icc_self) ψ
  set X : Planar.L2w m := Y τ -
    (F_rel τ 0 (Y 0) + ∫ σ in (0 : ℝ)..τ, F_rel τ σ (A_rel σ (Y σ) + G σ)) with hX
  have horth : ∀ ψ ∈ RelRegularityOrg.relSmoothClass m, ⟪ψ, X⟫_ℂ = 0 := by
    intro ψ hψ
    have h := hT ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel
      hFr hAr f w u hw hcirc Y G hY hG hYm ⟨C_Y, hCY⟩ hGi τ hτ ψ hψ
    rw [hX, inner_sub_right, inner_add_right, ← hint ψ, h]
    ring
  have hD := RelRegularityOrg.relB6b_leaf m hm
  have hcl : IsClosed {ψ : Planar.L2w m | ⟪ψ, X⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hall : ∀ ψ : Planar.L2w m, ⟪ψ, X⟫_ℂ = 0 := by
    intro ψ
    have hmem : ψ ∈ closure (RelRegularityOrg.relSmoothClass m) := by
      rw [hD.closure_eq]; trivial
    exact closure_minimal (fun ψ hψ => horth ψ hψ) hcl hmem
  have hX0 : X = 0 := inner_self_eq_zero.1 (hall X)
  exact sub_eq_zero.1 hX0

/-- **Leaf C in the regime** (proof of `complMovingMildRegSmall_of`). -/
theorem complMovingMildRegime_of (κ : PlanarFrameKernels) (h1 : ComplYExists κ)
    (h2 : ComplGExists κ) (h3 : ComplMildEqRegime κ) : ComplMovingMildRegime κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := h3 hκ P hP m hm K B hB
  refine ⟨b₀, fun b hbb hb => ?_⟩
  obtain ⟨ν₀, hν₀, h3⟩ := hb₀ b hbb hb
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF f w u hFlow hCirc
  dsimp only
  obtain ⟨Y, hY, hYm, hYb, hc1, hc2⟩ :=
    h1 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  obtain ⟨G, hG, hGi, hcm⟩ :=
    h2 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  exact ⟨Y, G, hY, hG, hYm, hYb, hGi,
    h3 ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF
      f w u hFlow hCirc Y G hY hG hYm hYb hGi, hc1, hc2, hcm⟩

/-- **Block Duhamel split in the regime** (proof of `complBlockDuhamelSplitReg_of_mildSmall`). -/
theorem complBlockDuhamelSplitReg_of_mildRegime (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ)
    (hMild : ComplMovingMildRegime κ) :
    ComplBlockDuhamelSplitReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₁, hb₁⟩ := hMild hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := hReg hκ P hP m hm K B hB
  refine ⟨max b₀ b₁, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, hRegν⟩ := hb₀ b ((le_max_left _ _).trans hb) hb1
  obtain ⟨ν₁, hν₁, hMild⟩ := hb₁ b ((le_max_right _ _).trans hb) hb1
  refine ⟨min ν₀ ν₁, lt_min hν₀ hν₁, fun ν hν hνle' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc => ?_⟩
  dsimp only
  have hνle : ν ≤ ν₀ := hνle'.trans (min_le_left _ _)
  have hνle₁ : ν ≤ ν₁ := hνle'.trans (min_le_right _ _)
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  obtain ⟨hFc, hAm, hAb⟩ := hRegν ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂
    hB_eq F_rel A_rel hF_rel hA_rel
  obtain ⟨Y, G, hYrep, hGrep, hYm, hYb, hGi, hYmild, hc₁, hc₂, hcmf⟩ :=
    hMild ν hν hνle₁ hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
      F_rel A_rel hF_rel hA_rel ⟨hFc, hAm, hAb⟩ f w u hFlow hCirc
  have hid := hVoC (Planar.L2w m) B F_rel A_rel U_rel hB hDuh hFc hAm hAb Y G hYm hYb hGi
    hYmild
  have hN₁₂ : 0 < clockN P ν t₁ t₂ := clockN_pos P hν ht₁ ht₂
  -- terminal complement
  have hA :
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
          (compl (periodizedFrame κ ν m b K hν hF) w t₂) =
        ENNReal.ofReal (clockN P ν t₁ t₂) * ENNReal.ofReal ‖Y B‖ := by
    have hrep := hYrep B ⟨hB.le, le_rfl⟩
    rw [ageAt_eq_of_movingZ_sub hν ht₂ hB_eq] at hrep
    exact (ofReal_mul_norm_eq_xNorm hN₁₂ hc₂ (Y B) hrep).symm
  -- entrance complement
  have hB0 : ENNReal.ofReal ‖Y 0‖ =
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
        (compl (periodizedFrame κ ν m b K hν hF) w t₁) := by
    have hrep := hYrep 0 ⟨le_rfl, hB.le⟩
    rw [ageAt_zero hν ht₁, clockN_self P hν ht₁] at hrep
    have h1 := ofReal_mul_norm_eq_xNorm one_pos hc₁ (Y 0) hrep
    rwa [ENNReal.ofReal_one, one_mul] at h1
  -- forcing
  have hC : ∀ σ ∈ Ioc (0 : ℝ) B,
      ENNReal.ofReal ‖G σ‖ ≤ ENNReal.ofReal ((clockN P ν t₁ (ageAt ν t₁ σ))⁻¹) *
        ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j‖ *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
            (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr (ageAt ν t₁ σ) j) := by
    intro σ hσ
    have hs : ageAt ν t₁ σ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν ht₁ h12 hB_eq ⟨hσ.1.le, hσ.2⟩
    have hrep := hGrep σ ⟨hσ.1.le, hσ.2⟩
    generalize ageAt ν t₁ σ = s at hs hrep ⊢
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have hNs : 0 < clockN P ν t₁ s := clockN_pos P hν ht₁ hs0
    set F := periodizedFrame κ ν m b K hν hF
    set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
    have hmeas : ∀ j : Fin 2, AEStronglyMeasurable
        (fun y => ampl F w s j * complModeForce κ P F tr s j y) (B0579.cellMeasure d m) :=
      fun j => (hcmf s hs j).const_mul _
    have hV : AEStronglyMeasurable
        (fun y => ∑ j : Fin 2, ampl F w s j * complModeForce κ P F tr s j y)
        (B0579.cellMeasure d m) := by
      simp only [Fin.sum_univ_two]
      exact (hmeas 0).add (hmeas 1)
    have heq := ofReal_mul_norm_eq_xNorm hNs hV (G σ) hrep
    have htri : xNorm d m (fun y => ∑ j : Fin 2, ampl F w s j * complModeForce κ P F tr s j y) ≤
        ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w s j‖ * xNorm d m (complModeForce κ P F tr s j) := by
      have h0 := xNorm_smul_complModeForce κ P F tr d s 0 (ampl F w s 0)
      have h1 := xNorm_smul_complModeForce κ P F tr d s 1 (ampl F w s 1)
      simp only [Fin.sum_univ_two]
      rw [← h0, ← h1]
      exact eLpNorm_add_le (hmeas 0) (hmeas 1) (by norm_num)
    have hone : ENNReal.ofReal (clockN P ν t₁ s)⁻¹ * ENNReal.ofReal (clockN P ν t₁ s) = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hNs.le), inv_mul_cancel₀ hNs.ne',
        ENNReal.ofReal_one]
    calc ENNReal.ofReal ‖G σ‖
        = ENNReal.ofReal (clockN P ν t₁ s)⁻¹ *
            (ENNReal.ofReal (clockN P ν t₁ s) * ENNReal.ofReal ‖G σ‖) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ _ := by
          rw [heq]
          gcongr
  refine ⟨ENNReal.ofReal (clockN P ν t₁ t₂) *
      (ENNReal.ofReal ‖U_rel B 0‖ * ENNReal.ofReal ‖Y 0‖),
    fun r => ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
      (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
        ENNReal.ofReal ‖G (movingZ ν r - movingZ ν t₁)‖)), ?_, ?_, ?_⟩
  · have hcv := lintegral_Ioc_block_eq hν ht₁ h12 hB_eq
      (fun σ => ENNReal.ofReal ‖U_rel B σ‖ * ENNReal.ofReal ‖G σ‖)
    rw [hA, hid, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hcv, ← mul_add]
    gcongr
    exact ofReal_norm_voc_le _ _ _ _ hB.le
  · rw [hB0, ← mul_assoc, ← ENNReal.ofReal_mul hN₁₂.le]
  · intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have hmem := movingZ_sub_mem_Icc hν ht₁ ⟨hr.1.le, hr.2⟩
    rw [hB_eq] at hmem
    have hσ : movingZ ν r - movingZ ν t₁ ∈ Ioc (0 : ℝ) B := by
      refine ⟨lt_of_le_of_ne hmem.1 fun h0 => ?_, hmem.2⟩
      have := movingZ_inj hν ht₁ hr0 (by linarith)
      linarith [hr.1]
    have hGr := hC _ hσ
    rw [ageAt_movingZ_sub hν hr0] at hGr
    have hNr : 0 < clockN P ν t₁ r := clockN_pos P hν ht₁ hr0
    have hkey : (clockN P ν t₁ r)⁻¹ * clockN P ν t₁ t₂ = clockN P ν r t₂ :=
      clockN_inv_mul_clockN P hν ht₁ hr0 ht₂
    have ha : 0 ≤ (clockA ν r) ^ (-2 : ℝ) :=
      Real.rpow_nonneg (by unfold clockA; positivity) _
    have hNr₂ : 0 ≤ clockN P ν r t₂ := (clockN_pos P hν hr0 ht₂).le
    calc ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
            ENNReal.ofReal ‖G (movingZ ν r - movingZ ν t₁)‖))
        ≤ ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
            (ENNReal.ofReal ((clockN P ν t₁ r)⁻¹) *
              ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                  (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)))) := by
          gcongr
      _ = ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
            (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
            ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) := by
          rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hNr₂, ← hkey,
            ENNReal.ofReal_mul (inv_nonneg.2 hNr.le)]
          ring

/-- **Final assembly in the regime**: the variation-of-constants target `ComplBlockDuhamelVoCReg`
from `DuhamelVoCAbstract`, leaf B (`RelBlockRegularityReg`), `ComplYExists`, `ComplGExists` and the
tested mild identity `ComplMildTestedRegime`. -/
theorem complBlockDuhamelVoCReg_of_regime (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ) (h1 : ComplYExists κ)
    (h2 : ComplGExists κ) (hT : ComplMildTestedRegime κ) : ComplBlockDuhamelVoCReg κ :=
  complBlockDuhamelVoCReg_of κ (complBlockDuhamelSplitReg_of_mildRegime κ hVoC hReg
    (complMovingMildRegime_of κ h1 h2 (complMildEqRegime_of_tested κ hT)))

/-- `ComplMildTestedRegime` from its seven inputs (Leaf 1, the three inputs of Leaf 2 and the
three open inputs of Leaf 3; the rough extension is `ARelRoughSub.aRelRoughReg`). -/
theorem complMildTestedRegime_of_leaves (κ : PlanarFrameKernels)
    (hV : MovSolTestedDuhamelSmall) (hD : FrelDiag) (hE : FrameTestedDuhamel κ)
    (hA : AmplMovingFTCRegime κ) (h4 : MovDualMemLpRegime κ) (h5 : MovH0FrameRegime κ)
    (h6 : MovK0MemLpRegime κ) : ComplMildTestedRegime κ :=
  complMildTestedRegime_of κ hV (modeTestedDuhamelRegime_of κ hD hE hA)
    (complGeneratorSplitRegime_of κ (ARelRoughSub.aRelRoughReg κ) h4 h5 h6)

/-! ## Leaf 1 in the small-viscosity regime -/

/-- `MovSolDuhamelOf` (tested Duhamel identity for any representatives `V`, `LV`, SP 2861-2866,
2937-2945) for `ν ≤ ν₀(m)`: pairing `-(u·∇E)` with the backward free flow in `X_{-m}` uses the
weighted train gradient bound, which Part I gives only for small `ν` (SP 3050-3051). -/
def MovSolDuhamelOfSmall : Prop :=
  ∀ m : ℝ, 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V → LVRep P m B ν tr t₁ w LV →
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) volume 0 τ ∧
                ⟪ψ, V τ⟫_ℂ = ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ

/-- An all-`ν` tested Duhamel identity gives the small-viscosity form. -/
theorem movSolDuhamelOfSmall_of_all (h : MovSolDuhamelOf) : MovSolDuhamelOfSmall :=
  fun m hm => ⟨1, one_pos, fun P hP B b hB hb ν hν _ => h P hP m hm B b hB hb ν hν⟩

/-- **Leaf 1 for `ν ≤ ν₀(m)`** from `movSolExistsSmall`-type existence and
`MovSolDuhamelOfSmall`. -/
theorem movSolTestedDuhamelSmall_of' (hA : MovSolExistsSmall) (hB : MovSolDuhamelOfSmall) :
    MovSolTestedDuhamelSmall := by
  intro m hm
  obtain ⟨ν₁, hν₁, h⟩ := hA m hm
  obtain ⟨ν₂, hν₂, hB⟩ := hB m hm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂,
    fun P hP B b hB0 hb ν hν hνs tr htr t₁ t₂ h1 h12 hθ hZ F hF f w u hfl hz => ?_⟩
  obtain ⟨V, LV, hV, hLV⟩ := h P hP B b hB0 hb ν hν (hνs.trans (min_le_left _ _)) tr htr t₁ t₂
    h1 h12 hθ hZ f w u hfl hz
  exact ⟨V, LV, hV, hLV, hB P hP B b hB0 hb ν hν (hνs.trans (min_le_right _ _)) tr htr t₁ t₂
    h1 h12 hθ hZ F hF f w u hfl hz V LV hV hLV⟩

end Regime

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
