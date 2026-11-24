import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildMild
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY.Ampl
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Interaction

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1` (Leaf C3' `ComplMildTested`): reduction to eight leaves

Source of record: `the November 2 reference manuscript` (SP), lines 2861-2866
(moving equation `W' = GW`, `G = θ⁻¹D + L`), 2898-2918 (frame identities), 2914-2925
(`K₀ = GE - E_z`, `(ΛW)' = H₀W`, `M₀ = H₀E = ΛK₀`, `eq:short-causal-damped-complement`),
2937-2945 (periodized relative free evolution `\bar F_{rel}`).

This file does NOT prove `ComplMildTested`; `complMildTested_of_leaves` proves it from the leaves
below.  At an age `s = s(σ)` of the block (`N = N(t₁, s)`, `d = d(s)`, `I_d` zero extension,
`W = J_{a(s)}⁻¹ w(s)`, `α_j = Λ_j W`) the normalised complement is `Y = V - M`,
`V = N⁻¹ I_d W` (`VRep`), `M = N⁻¹ I_d Σ_j α_j E_j` (`MRep`).  Formally
`V' = (G_free - β₀) V + LV` and `M' = (G_free - β₀) M + FM` with `LV = N⁻¹ I_d L_int W` (`LVRep`)
and `FM = N⁻¹ I_d Σ_j (α_j (E_z - G_free E_j) + (H₀)_j(W) E_j)` (`FMRep`, `movFreeRes`).

Proved here:
* `complMildTested_of`: `MovSolTestedDuhamel`, `ModeTestedDuhamel`, `ComplGeneratorSplit` give
  `ComplMildTested` (linearity; `Y = V - M`).
* `complGeneratorSplit_of` (`gen_core`, `gen_pointwise`): the substitution of SP 2919-2925,
  `A_rel σ (Y σ) + G σ = LV σ - FM σ`, from `ARelRough`, `MovDualMemLp`, `MovH0Frame`,
  `MovK0MemLp` (`Λ r = 0`, linearity of `L_int` via
  `RelIntA.ae_integrableOn_kerVelCx`, linearity of `H₀`, `frameProj` of `K₀ - λE`).
* `modeTestedDuhamel_of`: `M = Σ_j a_j E_j`, product rule for primitives
  (`mul_sub_mul_of_primitive`, Fubini on the square), from `FrelDiag`, `FrameTestedDuhamel`,
  `AmplMovingFTC`.

Leaves (analytic content):
* `MovSolTestedDuhamel`: PDE duality of `IsLinearisedFlow` against the backward free cylinder flow
  in moving variables (`V`, `LV` exist; tested Duhamel relative to `F_rel`).
* `FrelDiag`: `F_rel τ τ = id` (pinning at equal ages, density of the pinned class).
* `FrameTestedDuhamel`: tested Duhamel (two-parameter) for the smooth frame vectors `E_j`.
* `AmplMovingFTC`: `(ΛW)' = H₀W` for the normalised amplitudes in moving time.
* `ARelRough`: `A_rel σ` acts by the pinned formula on cell-supported `X_{m,d}` data.
* `MovDualMemLp`: the kernel of `H₀` lies in `X_{-m,d}`.
* `MovH0Frame`: `H₀ E = Λ K₀` (`M₀`).
* `MovK0MemLp`: `K₀ ∈ X_{m,d}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

open ComplMildSplit

/-! ## Moving objects of the split -/

/-- Free moving residual of mode `j`: `∂_z E_j - G_free E_j`, `G_free W = θ⁻¹ D W - V·∇W`
(SP 2861-2866, 2905, 2916). -/
def movFreeRes (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movEz κ ν r j y -
    ((clockTheta ν r : ℂ)⁻¹ * movD (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y -
      (((movingTrainV tr r y 0 : ℝ) : ℂ) *
          pdCx 0 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y +
        ((movingTrainV tr r y 1 : ℝ) : ℂ) *
          pdCx 1 (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y))

/-- Representation of the normalised zero-extended moving solution `V = N⁻¹ I_d W`. -/
def VRep (P : PlanarData) (m B ν t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ)
    (V : ℝ → Planar.L2w m) : Prop :=
  ∀ τ ∈ Icc (0 : ℝ) B, ⇑(V τ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
        (movingW ν w (ageAt ν t₁ τ)) (cToPlane z)

/-- Representation of the interaction forcing `LV = N⁻¹ I_d L_int W` of `V`. -/
def LVRep (P : PlanarData) (m B ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (LV : ℝ → Planar.L2w m) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) B, ⇑(LV σ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        (movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ))) (cToPlane z)

/-- Representation of the normalised zero-extended mode part `M = N⁻¹ I_d Σ_j α_j E_j`. -/
def MRep (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (b K B ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ)
    (M : ℝ → Planar.L2w m) : Prop :=
  ∀ τ ∈ Icc (0 : ℝ) B, ⇑(M τ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
        (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ τ) j *
          (periodizedFrame κ ν m b K hν hF).E (ageAt ν t₁ τ) j y)
        (cToPlane z)

/-- Representation of the mode forcing
`FM = N⁻¹ I_d Σ_j (α_j (E_z - G_free E_j) + (H₀)_j(W) E_j)` of `M`. -/
def FMRep (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (b K B ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (FM : ℝ → Planar.L2w m) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) B, ⇑(FM σ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        (fun y => ∑ j : Fin 2,
          (ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j *
              movFreeRes κ tr (ageAt ν t₁ σ) j y +
            movH0 κ tr (ageAt ν t₁ σ) j (movingW ν w (ageAt ν t₁ σ)) *
              (periodizedFrame κ ν m b K hν hF).E (ageAt ν t₁ σ) j y))
        (cToPlane z)

/-! ## The three leaves -/

/-- **Leaf 1 (PDE duality for the moving solution, SP 2861-2866, 2937-2945)**: the normalised
moving solution `V` and its interaction forcing `LV` exist in `L²_m`, and `V` satisfies the
tested Duhamel identity relative to `F_rel` (weak equation of `IsLinearisedFlow` tested
against the backward free cylinder flow of `ψ`). -/
def MovSolTestedDuhamel : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∃ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V ∧ LVRep P m B ν tr t₁ w LV ∧
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) volume 0 τ ∧
                ⟪ψ, V τ⟫_ℂ = ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ

/-- **Leaf 2 (frame part, SP 2898-2918, 2991-2997)**: the mode forcing `FM` exists in `L²_m`, and
the mode part `M` satisfies the tested Duhamel identity relative to `F_rel` (amplitude identity
`(ΛW)' = H₀W` in moving time, Duhamel for the smooth periodized frame vectors, product rule). -/
def ModeTestedDuhamel (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
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

/-- **Leaf 3 (generator identity, SP 2914-2925)**: on the block, the damped complement
interaction applied to the rough complement plus the mode forcing equals `LV - FM`
(`A_rel` identified on `Y σ` from its values on smooth data, `Λ r = 0`, `H₀E = ΛK₀`, linearity
of `L_int` and `H₀` along `W = Σ α_j E_j + r`). -/
def ComplGeneratorSplit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
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

/-! ## Composition -/

/-- `V - Y` represents the mode part. -/
theorem mRep_sub (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (b K B ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ)
    (V Y : ℝ → Planar.L2w m) (hV : VRep P m B ν t₁ w V)
    (hY : YRep κ P m b K B ν hν hF t₁ w Y) :
    MRep κ P m b K B ν hν hF t₁ w (fun σ => V σ - Y σ) := by
  intro τ hτ
  have hsub : ⇑(V τ - Y τ) =ᵐ[volume] ⇑(V τ) - ⇑(Y τ) :=
    (Planar.volume_ac m).ae_le (Lp.coeFn_sub (V τ) (Y τ))
  filter_upwards [hsub, hV τ hτ, hY τ hτ] with z h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  unfold cellZeroExt compl
  by_cases hz : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
  · simp only [Set.indicator_of_mem hz]
    ring
  · simp only [Set.indicator_of_notMem hz]
    ring

/-- **`ComplMildTested` from the three leaves.** -/
theorem complMildTested_of (κ : PlanarFrameKernels) (hV : MovSolTestedDuhamel)
    (hM : ModeTestedDuhamel κ) (hA : ComplGeneratorSplit κ) : ComplMildTested κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
    f w u hFlow hCirc Y G hY hG _hYm _hYb _hGi τ hτ ψ hψ
  obtain ⟨V, LV, hVr, hLVr, hVd⟩ :=
    hV P hP m hm B b hB hb ν hν tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
  obtain ⟨FM, hFMr, hMd⟩ :=
    hM hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
  have hgen := hA hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr
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

/-! ## Leaf 3 from four analytic inputs (the substitution of SP 2914-2925) -/

/-- **Input 3a (rough extension of `IsDampedComplBlockInt`, SP 2974-2978)**: on the block, `A_rel σ`
acts on every cell-supported `X ∈ L²_m` with `X|cell ∈ X_{m,d}` by the pinned formula. -/
def ARelRough (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ∀ σ ∈ Icc (0 : ℝ) B, ∀ Φ : ℝ × ℝ → ℂ,
            MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) →
            ∀ X : Planar.L2w m,
              (⇑X =ᵐ[volume] fun z : ℂ =>
                cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) Φ (cToPlane z)) →
              ⇑(A_rel σ X) =ᵐ[volume] fun z : ℂ =>
                cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
                  (movDampedComplInt κ P tr (ageAt ν t₁ σ) Φ) (cToPlane z)

/-- **Input 3b (moving dual kernel in `X_{-m,d}`, SP 2898-2918)**: the kernel of `H₀`,
`movingPhi(physLamDual)`, lies in `X_{-m,d(s)}` at every age of the block. -/
def MovDualMemLp (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ i : Fin 2,
          MemLp (movingPhi ν (fun r' => physLamDual κ tr r' i) (ageAt ν t₁ σ)) 2
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) (-m))

/-- **Input 3c (`M₀ = H₀E = ΛK₀`, SP 2916-2918)**: the moving pairing derivative of the frame
vectors is the `Λ`-pairing of the generator residuals. -/
def MovH0Frame (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ i k : Fin 2,
          movH0 κ tr (ageAt ν t₁ σ) i
              (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) k) =
            movM0 κ P tr (ageAt ν t₁ σ) i k

/-- **Input 3d (`K₀ = GE - E_z ∈ X_{m,d}`, SP 2905, 2916)**: the unprojected mode residuals lie
in `X_{m,d(s)}` at every age of the block. -/
def MovK0MemLp (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ σ ∈ Icc (0 : ℝ) B, ∀ j : Fin 2,
          MemLp (movK0 κ P tr (ageAt ν t₁ σ) j) 2
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m)

theorem clockTheta_le_of_le {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t) :
    clockTheta ν t ≤ clockTheta ν s := by
  unfold clockTheta clockA
  have h1 : 0 < ν * (1 + ν * s) := by positivity
  exact inv_anti₀ h1 (by nlinarith [mul_le_mul_of_nonneg_left hst (mul_self_nonneg ν)])

theorem setIntegral_mul_const_mul {S : Set (ℝ × ℝ)} (g Φ : ℝ × ℝ → ℂ) (c : ℂ) :
    ∫ y in S, g y * (c * Φ y) = c * ∫ y in S, g y * Φ y := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem setIntegral_const_mul_mul {S : Set (ℝ × ℝ)} (g Φ : ℝ × ℝ → ℂ) (c : ℂ) :
    ∫ y in S, (c * Φ y) * g y = c * ∫ y in S, Φ y * g y := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem setIntegral_mul_sub_two {S : Set (ℝ × ℝ)} {g W E0 E1 : ℝ × ℝ → ℂ} (a0 a1 : ℂ)
    (hW : IntegrableOn (fun x => g x * W x) S) (h0 : IntegrableOn (fun x => g x * E0 x) S)
    (h1 : IntegrableOn (fun x => g x * E1 x) S) :
    ∫ x in S, g x * (W x - (a0 * E0 x + a1 * E1 x)) =
      (∫ x in S, g x * W x) - (a0 * (∫ x in S, g x * E0 x) + a1 * (∫ x in S, g x * E1 x)) := by
  have heq : (fun x => g x * (W x - (a0 * E0 x + a1 * E1 x))) =
      fun x => g x * W x - (a0 * (g x * E0 x) + a1 * (g x * E1 x)) := by
    funext x; ring
  have hs : IntegrableOn (fun x => a0 * (g x * E0 x) + a1 * (g x * E1 x)) S :=
    (h0.const_mul a0).add (h1.const_mul a1)
  rw [heq, integral_sub hW hs, integral_add (h0.const_mul a0) (h1.const_mul a1),
    integral_const_mul, integral_const_mul]

theorem setIntegral_sub_two_mul {S : Set (ℝ × ℝ)} {g W E0 E1 : ℝ × ℝ → ℂ} (a0 a1 : ℂ)
    (hW : IntegrableOn (fun x => W x * g x) S) (h0 : IntegrableOn (fun x => E0 x * g x) S)
    (h1 : IntegrableOn (fun x => E1 x * g x) S) :
    ∫ x in S, (W x - (a0 * E0 x + a1 * E1 x)) * g x =
      (∫ x in S, W x * g x) - (a0 * (∫ x in S, E0 x * g x) + a1 * (∫ x in S, E1 x * g x)) := by
  have heq : (fun x => (W x - (a0 * E0 x + a1 * E1 x)) * g x) =
      fun x => W x * g x - (a0 * (E0 x * g x) + a1 * (E1 x * g x)) := by
    funext x; ring
  have hs : IntegrableOn (fun x => a0 * (E0 x * g x) + a1 * (E1 x * g x)) S :=
    (h0.const_mul a0).add (h1.const_mul a1)
  rw [heq, integral_sub hW hs, integral_add (h0.const_mul a0) (h1.const_mul a1),
    integral_const_mul, integral_const_mul]

theorem kerVelCx_const_mul (d : ℝ) (c : ℂ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (k : Fin 2) :
    kerVelCx d (fun z => c * Φ z) y k = c * kerVelCx d Φ y k := by
  unfold kerVelCx
  exact setIntegral_const_mul_mul _ _ c

theorem movLInt_const_mul {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (c : ℂ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    movLInt tr r (fun z => c * Φ z) y = c * movLInt tr r Φ y := by
  unfold movLInt
  rw [kerVelCx_const_mul, kerVelCx_const_mul]
  ring

theorem movH0_const_mul (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2) (c : ℂ)
    (Φ : ℝ × ℝ → ℂ) : movH0 κ tr r i (fun z => c * Φ z) = c * movH0 κ tr r i Φ := by
  unfold movH0
  rw [setIntegral_mul_const_mul]
  ring

theorem movLamPair_const_mul (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) (c : ℂ)
    (Φ : ℝ × ℝ → ℂ) : movLamPair κ ν r j (fun z => c * Φ z) = c * movLamPair κ ν r j Φ := by
  unfold movLamPair
  exact setIntegral_mul_const_mul _ _ c

theorem compl_eq_two {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) :
    compl F w s = fun x =>
      movingW ν w s x - (ampl F w s 0 * F.E s 0 x + ampl F w s 1 * F.E s 1 x) := by
  funext x
  simp [compl, Fin.sum_univ_two]

theorem periodizedFrame_E (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (s : ℝ) :
    (periodizedFrame κ ν m b K hν hF).E s = perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) := rfl

theorem periodizedFrame_lam (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (s : ℝ) :
    (periodizedFrame κ ν m b K hν hF).lam s = perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) :=
  rfl

/-- `E_z - G_free E_j = L_int E_j - K₀` (definitions of `movK0`, `movL`). -/
theorem movFreeRes_eq (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    movFreeRes κ tr r j y =
      movLInt tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y - movK0 κ P tr r j y := by
  unfold movFreeRes movK0
  rw [movOscRes_add_movEulerRes_add_eigen, movL_eq_drift_add_movLInt]
  ring

/-- Pointwise substitution (SP 2919-2925): on `ker Λ`, `𝓑 - (G_free - β₀)` applied to `N⁻¹ r` plus
the mode forcing is `N⁻¹ (L_int W - Σ_j (α_j (E_z - G_free E_j) + (H₀)_j W E_j))`. -/
theorem gen_pointwise (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) (y : ℝ × ℝ) (N : ℂ)
    (hlam : ∀ j, movLamPair κ ν s j (compl (periodizedFrame κ ν m b K hν hF) w s) = 0)
    (hLI : movLInt tr s (compl (periodizedFrame κ ν m b K hν hF) w s) y =
      movLInt tr s (movingW ν w s) y -
        (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
            movLInt tr s (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0) y +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
            movLInt tr s (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1) y))
    (hH : ∀ i, movH0 κ tr s i (compl (periodizedFrame κ ν m b K hν hF) w s) =
      movH0 κ tr s i (movingW ν w s) -
        (ampl (periodizedFrame κ ν m b K hν hF) w s 0 * movM0 κ P tr s i 0 +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 * movM0 κ P tr s i 1))
    (hCF : ∀ j, complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr s j y =
      (movK0 κ P tr s j y - modeEigen P j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j y) -
        ((movM0 κ P tr s 0 j - modeEigen P j * (if (0 : Fin 2) = j then 1 else 0)) *
            perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0 y +
          (movM0 κ P tr s 1 j - modeEigen P j * (if (1 : Fin 2) = j then 1 else 0)) *
            perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1 y)) :
    movDampedComplInt κ P tr s (fun x => N * compl (periodizedFrame κ ν m b K hν hF) w s x) y +
        N * (∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w s j *
          complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr s j y) =
      N * movLInt tr s (movingW ν w s) y -
        N * (∑ j : Fin 2,
          (ampl (periodizedFrame κ ν m b K hν hF) w s j * movFreeRes κ tr s j y +
            movH0 κ tr s j (movingW ν w s) * (periodizedFrame κ ν m b K hν hF).E s j y)) := by
  have hker : ∀ j : Fin 2,
      movLamPair κ ν s j (fun x => N * compl (periodizedFrame κ ν m b K hν hF) w s x) = 0 := by
    intro j
    rw [movLamPair_const_mul, hlam j, mul_zero]
  unfold movDampedComplInt
  rw [movFrameRankPert_of_lam_eq_zero κ P tr s _ hker, movLInt_const_mul]
  simp only [Fin.sum_univ_two, movH0_const_mul, hLI, hH, hCF, movFreeRes_eq κ P,
    periodizedFrame_E]
  simp
  ring

/-- The generator identity at one age `s` of the block, from the inputs at `s`. -/
theorem gen_core (κ : PlanarFrameKernels) (P : PlanarData) {m b K ν : ℝ} (hm : 8 < m)
    (hb : 1 ≤ b) (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {t : ℝ} {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hFlow : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (ht : 0 ≤ t)
    (s : ℝ) (hts : t ≤ s) (hbs : b ≤ clockTheta ν s)
    (hφ : ∀ i : Fin 2, MemLp (movingPhi ν (fun r' => physLamDual κ tr r' i) s) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)))
    (h5 : ∀ i k : Fin 2,
      movH0 κ tr s i (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) k) = movM0 κ P tr s i k)
    (hK : ∀ j : Fin 2, MemLp (movK0 κ P tr s j) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m))
    (A : Planar.L2w m →L[ℂ] Planar.L2w m)
    (hA : ∀ Φ : ℝ × ℝ → ℂ,
      MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m) →
      ∀ X : Planar.L2w m,
        (⇑X =ᵐ[volume] fun z : ℂ =>
          cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) Φ (cToPlane z)) →
        ⇑(A X) =ᵐ[volume] fun z : ℂ =>
          cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (movDampedComplInt κ P tr s Φ)
            (cToPlane z))
    (N : ℂ) (Yσ Gσ LVσ FMσ : Planar.L2w m)
    (hY : ⇑Yσ =ᵐ[volume] fun z : ℂ =>
      N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (compl (periodizedFrame κ ν m b K hν hF) w s) (cToPlane z))
    (hG : ⇑Gσ =ᵐ[volume] fun z : ℂ =>
      N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w s j *
          complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr s j y) (cToPlane z))
    (hLV : ⇑LVσ =ᵐ[volume] fun z : ℂ =>
      N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (movLInt tr s (movingW ν w s)) (cToPlane z))
    (hFM : ⇑FMσ =ᵐ[volume] fun z : ℂ =>
      N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (fun y => ∑ j : Fin 2,
          (ampl (periodizedFrame κ ν m b K hν hF) w s j * movFreeRes κ tr s j y +
            movH0 κ tr s j (movingW ν w s) * (periodizedFrame κ ν m b K hν hF).E s j y))
        (cToPlane z)) :
    A Yσ + Gσ = LVσ - FMσ := by
  have hs0 : 0 ≤ s := ht.trans hts
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν s) :=
    ComplMildYAux.cellLen_one_le_of_theta hν hs0 hb hbs
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hm1 : (1 : ℝ) < m := by linarith
  have hWf : MemLp (movingW ν w s) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m) :=
    ComplCouplingSub.memLp_movingW hm0 hν ht hts hFlow
  have hE : ∀ j, MemLp (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m) := fun j =>
    ComplCouplingSub.memLp_frame_E (periodizedFrame κ ν m b K hν hF) hs0 hbs j
  have hr : MemLp (compl (periodizedFrame κ ν m b K hν hF) w s) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m) :=
    ComplCouplingSub.memLp_compl (periodizedFrame κ ν m b K hν hF) hm0 hν ht hts hbs hFlow
  have hdual : ∀ i j : Fin 2, ∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
      perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x = if i = j then 1 else 0 :=
    hF.1 s hs0 hbs
  have ha : ∀ i, ampl (periodizedFrame κ ν m b K hν hF) w s i =
      ∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
        perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x * movingW ν w s x := fun i => rfl
  -- `Λ r = 0`
  have hlam : ∀ j, movLamPair κ ν s j (compl (periodizedFrame κ ν m b K hν hF) w s) = 0 := by
    intro j
    have hW1 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd1 j hWf
    have hE0 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd1 j (hE 0)
    have hE1 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd1 j (hE 1)
    have key : movLamPair κ ν s j (compl (periodizedFrame κ ν m b K hν hF) w s) =
        (∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x * movingW ν w s x) -
          (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
              (∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
                perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x *
                  perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0 x) +
            ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
              (∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
                perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x *
                  perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1 x)) := by
      unfold movLamPair movingCell
      rw [compl_eq_two, periodizedFrame_E]
      exact setIntegral_mul_sub_two _ _ hW1 hE0 hE1
    rw [key, ← ha j, hdual j 0, hdual j 1]
    fin_cases j <;> simp
  -- linearity of `H₀`
  have hH : ∀ i, movH0 κ tr s i (compl (periodizedFrame κ ν m b K hν hF) w s) =
      movH0 κ tr s i (movingW ν w s) -
        (ampl (periodizedFrame κ ν m b K hν hF) w s 0 * movM0 κ P tr s i 0 +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 * movM0 κ P tr s i 1) := by
    intro i
    have hW1 := (ComplCouplingSub.xNorm_pairing_bound (hφ i) hWf).1
    have hE0 := (ComplCouplingSub.xNorm_pairing_bound (hφ i) (hE 0)).1
    have hE1 := (ComplCouplingSub.xNorm_pairing_bound (hφ i) (hE 1)).1
    rw [← h5 i 0, ← h5 i 1]
    unfold movH0 movingCell
    rw [compl_eq_two, periodizedFrame_E]
    rw [show (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
        movingPhi ν (fun r' => physLamDual κ tr r' i) s y *
          (fun x => movingW ν w s x -
            (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
                perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0 x +
              ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
                perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1 x)) y) = _ from
      setIntegral_mul_sub_two _ _ hW1 hE0 hE1]
    ring
  -- the mode forcing
  have hCF : ∀ j y, complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr s j y =
      (movK0 κ P tr s j y - modeEigen P j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j y) -
        ((movM0 κ P tr s 0 j - modeEigen P j * (if (0 : Fin 2) = j then 1 else 0)) *
            perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0 y +
          (movM0 κ P tr s 1 j - modeEigen P j * (if (1 : Fin 2) = j then 1 else 0)) *
            perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1 y) := by
    intro j y
    have hI : ∀ i, ∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
        perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x *
          (movOscRes κ ν s j x + movEulerRes κ P tr s j x) =
          movM0 κ P tr s i j - modeEigen P j * (if i = j then 1 else 0) := by
      intro i
      have hKi := ComplCouplingSub.integrableOn_perLam_mul κ hm hd1 i (hK j)
      have hEi := ComplCouplingSub.integrableOn_perLam_mul κ hm hd1 i (hE j)
      have heq : (fun x => perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x *
            (movOscRes κ ν s j x + movEulerRes κ P tr s j x)) =
          fun x => perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x * movK0 κ P tr s j x -
            modeEigen P j * (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) i x *
              perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) j x) := by
        funext x
        unfold movK0
        ring
      rw [heq, integral_sub hKi (hEi.const_mul _), integral_const_mul, hdual i j]
      rfl
    unfold complModeForce frameProj
    simp only [Fin.sum_univ_two, periodizedFrame_lam, periodizedFrame_E, movingCell]
    rw [hI 0, hI 1]
    unfold movK0
    ring
  -- representation of `A Yσ`
  have hYσ : ⇑Yσ =ᵐ[volume] fun z : ℂ =>
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (fun x => N * compl (periodizedFrame κ ν m b K hν hF) w s x) (cToPlane z) := by
    filter_upwards [hY] with z hz
    rw [hz]
    unfold cellZeroExt
    by_cases hc : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
    · simp only [Set.indicator_of_mem hc]
    · simp only [Set.indicator_of_notMem hc, mul_zero]
  have eA := hA (fun x => N * compl (periodizedFrame κ ν m b K hν hF) w s x) (hr.const_mul N)
    Yσ hYσ
  -- a.e. integrability of the kernel integrands
  have hKW := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 hWf
  have hK0 :=
    BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 (hE 0)
  have hK1 :=
    BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hd1 hm1 (hE 1)
  have hcell : MeasurableSet (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))) :=
    B0579.measurableSet_cell _
  have hKall : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) →
      (∀ k : Fin 2, IntegrableOn (fun z => movingW ν w s z *
          ((kerD (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (y - z) k : ℝ) : ℂ))
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))) ∧
      (∀ k : Fin 2, IntegrableOn (fun z => perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0 z *
          ((kerD (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (y - z) k : ℝ) : ℂ))
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))) ∧
      (∀ k : Fin 2, IntegrableOn (fun z => perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1 z *
          ((kerD (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (y - z) k : ℝ) : ℂ))
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))) := by
    rw [← ae_restrict_iff' hcell]
    filter_upwards [hKW, hK0, hK1] with y a b c using ⟨a, b, c⟩
  have hKz :=
    BlockPropagatorSub.measurePreserving_cToPlane_volume.quasiMeasurePreserving.ae hKall
  -- pointwise identity
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ),
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
          (movDampedComplInt κ P tr s (fun x => N * compl (periodizedFrame κ ν m b K hν hF) w s x))
          (cToPlane z) +
        N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
          (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w s j *
            complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr s j y) (cToPlane z) =
      N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
          (movLInt tr s (movingW ν w s)) (cToPlane z) -
        N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
          (fun y => ∑ j : Fin 2,
            (ampl (periodizedFrame κ ν m b K hν hF) w s j * movFreeRes κ tr s j y +
              movH0 κ tr s j (movingW ν w s) * (periodizedFrame κ ν m b K hν hF).E s j y))
          (cToPlane z) := by
    filter_upwards [hKz] with z hz
    unfold cellZeroExt
    by_cases hc : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
    · simp only [Set.indicator_of_mem hc]
      obtain ⟨hiW, hi0, hi1⟩ := hz hc
      have hLI : movLInt tr s (compl (periodizedFrame κ ν m b K hν hF) w s) (cToPlane z) =
          movLInt tr s (movingW ν w s) (cToPlane z) -
            (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
                movLInt tr s (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0) (cToPlane z) +
              ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
                movLInt tr s (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1) (cToPlane z)) := by
        have hk : ∀ k : Fin 2,
            kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
                (compl (periodizedFrame κ ν m b K hν hF) w s) (cToPlane z) k =
              kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (movingW ν w s) (cToPlane z) k -
                (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
                    kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
                      (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 0) (cToPlane z) k +
                  ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
                    kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
                      (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) 1) (cToPlane z) k) := by
          intro k
          unfold kerVelCx
          rw [compl_eq_two, periodizedFrame_E]
          exact setIntegral_sub_two_mul _ _ (hiW k) (hi0 k) (hi1 k)
        unfold movLInt
        rw [hk 0, hk 1]
        ring
      exact gen_pointwise κ P hν hF tr w s (cToPlane z) N hlam hLI
        (fun i => by rw [hH i]) (fun j => hCF j _)
    · simp only [Set.indicator_of_notMem hc, mul_zero, add_zero, sub_zero]
  -- assemble
  apply Lp.ext
  refine (Planar.wMeasure_ac m).ae_le ?_
  have e1 := (Planar.volume_ac m).ae_le (Lp.coeFn_add (A Yσ) Gσ)
  have e2 := (Planar.volume_ac m).ae_le (Lp.coeFn_sub LVσ FMσ)
  filter_upwards [e1, e2, eA, hG, hLV, hFM, hpt] with z z1 z2 z3 z4 z5 z6 z7
  rw [z1, z2, Pi.add_apply, Pi.sub_apply, z3, z4, z5, z6]
  exact z7

/-- **Leaf 3 from its four inputs.** -/
theorem complGeneratorSplit_of (κ : PlanarFrameKernels) (h1 : ARelRough κ)
    (h4 : MovDualMemLp κ) (h5 : MovH0Frame κ) (h6 : MovK0MemLp κ) : ComplGeneratorSplit κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr f w u hFlow
    hCirc Y G LV FM hY hG hLV hFM σ hσ
  have hsI : ageAt ν t₁ σ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν ht₁ h12 hBe hσ
  have hbs : b ≤ clockTheta ν (ageAt ν t₁ σ) :=
    hbt.trans (clockTheta_le_of_le hν (ht₁.trans hsI.1) hsI.2)
  exact gen_core κ P hm hb hν hF tr hFlow ht₁ (ageAt ν t₁ σ) hsI.1 hbs
    (h4 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (h5 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (h6 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe σ hσ)
    (A_rel σ) (h1 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe A_rel hAr σ hσ)
    _ (Y σ) (G σ) (LV σ) (FM σ) (hY σ hσ) (hG σ hσ) (hLV σ hσ) (hFM σ hσ)

/-- **`ComplMildTested` from Leaves 1, 2 and the four inputs of Leaf 3.** -/
theorem complMildTested_of_inputs (κ : PlanarFrameKernels) (hV : MovSolTestedDuhamel)
    (hM : ModeTestedDuhamel κ) (h1 : ARelRough κ) (h4 : MovDualMemLp κ) (h5 : MovH0Frame κ)
    (h6 : MovK0MemLp κ) : ComplMildTested κ :=
  complMildTested_of κ hV hM (complGeneratorSplit_of κ h1 h4 h5 h6)

/-! ## Leaf 2 from three inputs (product rule for the mode part) -/

/-- Fubini on the square: `∫₀^T α Q + ∫₀^T A β = A(T) Q(T)` for the primitives `A`, `Q`. -/
theorem primitive_mul_identity {T : ℝ} {α β : ℝ → ℂ}
    (hα : IntegrableOn α (Ioc 0 T)) (hβ : IntegrableOn β (Ioc 0 T)) :
    (∫ x in Ioc 0 T, α x * ∫ y in Ioc 0 x, β y) + (∫ y in Ioc 0 T, (∫ x in Ioc 0 y, α x) * β y) =
      (∫ x in Ioc 0 T, α x) * ∫ y in Ioc 0 T, β y := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T) with hμ
  have hF : Integrable (fun p : ℝ × ℝ => α p.1 * β p.2) (μ.prod μ) := hα.mul_prod hβ
  set S1 : Set (ℝ × ℝ) := {p | p.2 ≤ p.1} with hS1def
  set S2 : Set (ℝ × ℝ) := {p | p.1 < p.2} with hS2def
  have hS1 : MeasurableSet S1 := measurableSet_le measurable_snd measurable_fst
  have hS2 : MeasurableSet S2 := measurableSet_lt measurable_fst measurable_snd
  have h1 : (∫ x in Ioc 0 T, α x * ∫ y in Ioc 0 x, β y) =
      ∫ p, S1.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) p ∂(μ.prod μ) := by
    rw [integral_prod _ (hF.indicator hS1)]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hind : (fun y => S1.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) (x, y)) =
        (Iic x).indicator (fun y => α x * β y) := by
      funext y
      by_cases hy : y ≤ x
      · rw [Set.indicator_of_mem (show (x, y) ∈ S1 from hy),
          Set.indicator_of_mem (show y ∈ Iic x from hy)]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ S1 from hy),
          Set.indicator_of_notMem (show y ∉ Iic x from hy)]
    have hset : Iic x ∩ Ioc 0 T = Ioc 0 x := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans hx.2⟩
    rw [hind, integral_indicator measurableSet_Iic, hμ, Measure.restrict_restrict measurableSet_Iic,
      hset, integral_const_mul]
  have h2 : (∫ y in Ioc 0 T, (∫ x in Ioc 0 y, α x) * β y) =
      ∫ p, S2.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) p ∂(μ.prod μ) := by
    rw [integral_prod_symm _ (hF.indicator hS2)]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have hind : (fun x => S2.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) (x, y)) =
        (Iio y).indicator (fun x => α x * β y) := by
      funext x
      by_cases hx : x < y
      · rw [Set.indicator_of_mem (show (x, y) ∈ S2 from hx),
          Set.indicator_of_mem (show x ∈ Iio y from hx)]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ S2 from hx),
          Set.indicator_of_notMem (show x ∉ Iio y from hx)]
    have hset : Iio y ∩ Ioc 0 T = Ioo 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.le.trans hy.2⟩
    rw [hind, integral_indicator measurableSet_Iio, hμ, Measure.restrict_restrict measurableSet_Iio,
      hset, integral_mul_const, integral_Ioc_eq_integral_Ioo]
  have hsum : ∀ p : ℝ × ℝ, S1.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) p +
      S2.indicator (fun p : ℝ × ℝ => α p.1 * β p.2) p = α p.1 * β p.2 := by
    intro p
    by_cases hp : p.2 ≤ p.1
    · rw [Set.indicator_of_mem (show p ∈ S1 from hp),
        Set.indicator_of_notMem (show p ∉ S2 from not_lt.2 hp), add_zero]
    · rw [Set.indicator_of_notMem (show p ∉ S1 from hp),
        Set.indicator_of_mem (show p ∈ S2 from lt_of_not_ge hp), zero_add]
  rw [h1, h2, ← integral_add (hF.indicator hS1) (hF.indicator hS2)]
  simp only [hsum]
  exact integral_prod_mul α β

/-- **Product rule for primitives** (integration by parts for absolutely continuous scalars). -/
theorem mul_sub_mul_of_primitive {T : ℝ} (hT : 0 ≤ T) {a q α β : ℝ → ℂ}
    (hα : IntervalIntegrable α volume 0 T) (hβ : IntervalIntegrable β volume 0 T)
    (ha : ∀ x ∈ Icc (0 : ℝ) T, a x = a 0 + ∫ y in (0 : ℝ)..x, α y)
    (hq : ∀ x ∈ Icc (0 : ℝ) T, q x = q 0 + ∫ y in (0 : ℝ)..x, β y) :
    IntervalIntegrable (fun x => α x * q x) volume 0 T ∧
      IntervalIntegrable (fun x => a x * β x) volume 0 T ∧
      a T * q T - a 0 * q 0 = ∫ x in (0 : ℝ)..T, (α x * q x + a x * β x) := by
  have huI : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT
  have hαI : IntegrableOn α (uIcc 0 T) := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hα
    |>.mono_set (by rw [huI])
  have hβI : IntegrableOn β (uIcc 0 T) := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hβ
    |>.mono_set (by rw [huI])
  have hAc : ContinuousOn (fun x => ∫ y in (0 : ℝ)..x, α y) (uIcc 0 T) :=
    intervalIntegral.continuousOn_primitive_interval hαI
  have hQc : ContinuousOn (fun x => ∫ y in (0 : ℝ)..x, β y) (uIcc 0 T) :=
    intervalIntegral.continuousOn_primitive_interval hβI
  have hac : ContinuousOn a (uIcc 0 T) := by
    have h : ContinuousOn (fun x => a 0 + ∫ y in (0 : ℝ)..x, α y) (uIcc 0 T) :=
      continuousOn_const.add hAc
    refine h.congr fun x hx => ?_
    rw [huI] at hx
    exact ha x hx
  have hqc : ContinuousOn q (uIcc 0 T) := by
    have h : ContinuousOn (fun x => q 0 + ∫ y in (0 : ℝ)..x, β y) (uIcc 0 T) :=
      continuousOn_const.add hQc
    refine h.congr fun x hx => ?_
    rw [huI] at hx
    exact hq x hx
  have i1 : IntervalIntegrable (fun x => α x * q x) volume 0 T := hα.mul_continuousOn hqc
  have i2 : IntervalIntegrable (fun x => a x * β x) volume 0 T := hβ.continuousOn_mul hac
  refine ⟨i1, i2, ?_⟩
  have iAQ : IntervalIntegrable (fun x => α x * ∫ y in (0 : ℝ)..x, β y) volume 0 T :=
    hα.mul_continuousOn hQc
  have iAB : IntervalIntegrable (fun x => (∫ y in (0 : ℝ)..x, α y) * β x) volume 0 T :=
    hβ.continuousOn_mul hAc
  have hcongr : ∫ x in (0 : ℝ)..T, (α x * q x + a x * β x) =
      ∫ x in (0 : ℝ)..T, ((q 0 * α x + α x * ∫ y in (0 : ℝ)..x, β y) +
        (a 0 * β x + (∫ y in (0 : ℝ)..x, α y) * β x)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [huI] at hx
    rw [ha x hx, hq x hx]
    ring
  rw [hcongr, intervalIntegral.integral_add ((hα.const_mul _).add iAQ)
      ((hβ.const_mul _).add iAB),
    intervalIntegral.integral_add (hα.const_mul _) iAQ,
    intervalIntegral.integral_add (hβ.const_mul _) iAB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hαo : IntegrableOn α (Ioc 0 T) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hα
  have hβo : IntegrableOn β (Ioc 0 T) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hβ
  have key := primitive_mul_identity hαo hβo
  have e1 : ∫ x in (0 : ℝ)..T, α x * ∫ y in (0 : ℝ)..x, β y =
      ∫ x in Ioc 0 T, α x * ∫ y in Ioc 0 x, β y := by
    rw [intervalIntegral.integral_of_le hT]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [intervalIntegral.integral_of_le hx.1.le]
  have e2 : ∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..x, α y) * β x =
      ∫ y in Ioc 0 T, (∫ x in Ioc 0 y, α x) * β y := by
    rw [intervalIntegral.integral_of_le hT]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [intervalIntegral.integral_of_le hx.1.le]
  have eT : a T = a 0 + ∫ y in (0 : ℝ)..T, α y := ha T ⟨hT, le_rfl⟩
  have eTq : q T = q 0 + ∫ y in (0 : ℝ)..T, β y := hq T ⟨hT, le_rfl⟩
  rw [e1, e2, eT, eTq]
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at *
  linear_combination (-1 : ℂ) * key

/-- Representation of the zero-extended frame vector `I_d E_j(s)`. -/
def ERep (κ : PlanarFrameKernels) (m B ν t₁ : ℝ) (j : Fin 2) (Ej : ℝ → Planar.L2w m) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) B, ⇑(Ej σ) =ᵐ[volume] fun z : ℂ =>
    cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
      (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) j) (cToPlane z)

/-- Representation of the relative free residual `I_d (E_z - (G_free - β₀) E_j)`. -/
def RRep (κ : PlanarFrameKernels) (P : PlanarData) (m B ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ : ℝ) (j : Fin 2)
    (Rj : ℝ → Planar.L2w m) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) B, ⇑(Rj σ) =ᵐ[volume] fun z : ℂ =>
    cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
      (fun y => movFreeRes κ tr (ageAt ν t₁ σ) j y +
        ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ) *
          perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) j y) (cToPlane z)

/-- Normalised amplitude `a_j(σ) = N⁻¹ α_j(s(σ))`. -/
def nAmpl (κ : PlanarFrameKernels) (P : PlanarData) (m b K ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (j : Fin 2) (σ : ℝ) : ℂ :=
  ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
    ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j

/-- Its moving-time derivative `a_j' = N⁻¹ (H₀)_j W - β₀ a_j` (SP 2916, 2998-3000). -/
def nAmplDz (κ : PlanarFrameKernels) (P : PlanarData) (m b K ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (j : Fin 2) (σ : ℝ) : ℂ :=
  ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
      movH0 κ tr (ageAt ν t₁ σ) j (movingW ν w (ageAt ν t₁ σ)) -
    ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ) * nAmpl κ P m b K ν hν hF t₁ w j σ

/-- **Input 2a (`\bar F_{rel}(t,t) = I`, SP 2941)**: the relative free evolution is the identity at
equal ages of the block. -/
def FrelDiag : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ τ ∈ Icc (0 : ℝ) B, ∀ X : Planar.L2w m, F_rel τ τ X = X

/-- **Input 2b (frame vectors, SP 2898-2918, 2941)**: the zero-extended frame vectors `E_j` and
their relative free residuals `R_j = I_d (E_z - (G_free - β₀) E_j)` lie in `L²_m`, and
`σ₀ ↦ ⟪ψ, F_rel τ σ₀ (E_j σ₀)⟫` is the primitive of `⟪ψ, F_rel τ σ (R_j σ)⟫` on `[0, τ]`
(Duhamel for the smooth periodized frame vectors). -/
def FrameTestedDuhamel (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ j : Fin 2, ∃ Ej Rj : ℝ → Planar.L2w m,
            ERep κ m B ν t₁ j Ej ∧ RRep κ P m B ν tr t₁ j Rj ∧
            ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
              IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (Rj σ)⟫_ℂ) volume 0 τ ∧
              ∀ σ₀ ∈ Icc (0 : ℝ) τ, ⟪ψ, F_rel τ σ₀ (Ej σ₀)⟫_ℂ =
                ⟪ψ, F_rel τ 0 (Ej 0)⟫_ℂ + ∫ σ in (0 : ℝ)..σ₀, ⟪ψ, F_rel τ σ (Rj σ)⟫_ℂ

/-- **Input 2c (amplitude identity `(ΛW)' = H₀W` in moving time, SP 2916-2918, 2991-3000)**: the
normalised amplitudes are primitives of `N⁻¹ (H₀)_j W - β₀ a_j` on the block. -/
def AmplMovingFTC (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
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

theorem coeFn_lin2 {m : ℝ} (c0 c1 : ℂ) (E0 E1 : Planar.L2w m) :
    ⇑(c0 • E0 + c1 • E1) =ᵐ[volume] fun z => c0 * E0 z + c1 * E1 z := by
  filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_add (c0 • E0) (c1 • E1)),
    (Planar.volume_ac m).ae_le (Lp.coeFn_smul c0 E0),
    (Planar.volume_ac m).ae_le (Lp.coeFn_smul c1 E1)] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

theorem coeFn_lin4 {m : ℝ} (c0 d0 c1 d1 : ℂ) (R0 E0 R1 E1 : Planar.L2w m) :
    ⇑((c0 • R0 + d0 • E0) + (c1 • R1 + d1 • E1)) =ᵐ[volume]
      fun z => (c0 * R0 z + d0 * E0 z) + (c1 * R1 z + d1 * E1 z) := by
  filter_upwards [(Planar.volume_ac m).ae_le
      (Lp.coeFn_add (c0 • R0 + d0 • E0) (c1 • R1 + d1 • E1)),
    coeFn_lin2 c0 d0 R0 E0, coeFn_lin2 c1 d1 R1 E1] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

/-- **Leaf 2 from its three inputs.** -/
theorem modeTestedDuhamel_of (κ : PlanarFrameKernels) (hD : FrelDiag)
    (hE : FrameTestedDuhamel κ) (hA : AmplMovingFTC κ) : ModeTestedDuhamel κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow
    hCirc
  choose Ej Rj hErep hRrep hEd using
    hE hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr
  have hAm := hA hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
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

/-- **`ComplMildTested` from Leaf 1 and the seven inputs of Leaves 2 and 3.** -/
theorem complMildTested_of_leaves (κ : PlanarFrameKernels) (hV : MovSolTestedDuhamel)
    (hD : FrelDiag) (hE : FrameTestedDuhamel κ) (hA : AmplMovingFTC κ) (h1 : ARelRough κ)
    (h4 : MovDualMemLp κ) (h5 : MovH0Frame κ) (h6 : MovK0MemLp κ) : ComplMildTested κ :=
  complMildTested_of κ hV (modeTestedDuhamel_of κ hD hE hA) (complGeneratorSplit_of κ h1 h4 h5 h6)

end ComplMildTestedSplit
end UnforcedLeray.Short.IIIa
