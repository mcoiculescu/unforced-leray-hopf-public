import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_org
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildReg

/-!
# Small-viscosity regime switch for `ComplMildTested` (`PartIII-a:T21/c3/2/1/2/3/3/1/1/1/org/switch`)

Source of record: `the November 2 reference manuscript` (SP) lines 2914-2925, 2974-2982,
standing smallness 3050-3051.  The all-`ν` `MovSolExists`/`MovSolTestedDuhamel` are not provable from
Part I; they are superseded by `MovSolTestedDuhamelSmall` (`ν ≤ ν₀(m)`).  New names, with the quantifier
`∃ ν₀ > 0` after `m` and `ν ≤ ν₀` after `hν`:
* `ComplMildTestedSmall`, `complMildTestedSmall_of`;
* `ComplMildEqRegSmall`, `complMildEqRegSmall_of_tested`;
* `ComplMovingMildRegSmall`, `complMovingMildRegSmall_of`;
* `complBlockDuhamelSplitReg_of_mildSmall`, `complBlockDuhamelVoCReg_of_leavesSmall` (final assembly).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub ComplMildSplit

namespace ComplMildTestedSplit

/-- `ComplMildTested` for `ν ≤ ν₀(m)`. -/
def ComplMildTestedSmall (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
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

def ComplMildEqRegSmall (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
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

def ComplMovingMildRegSmall (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
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

theorem complMildTestedSmall_of (κ : PlanarFrameKernels) (hV : MovSolTestedDuhamelSmall)
    (hM : ModeTestedDuhamel κ) (hA : ComplGeneratorSplit κ) : ComplMildTestedSmall κ := by
  intro hκ P hP m hm
  obtain ⟨ν₀, hν₀, hV⟩ := hV m hm
  refine ⟨ν₀, hν₀, ?_⟩
  intro K B b hB hb ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
    f w u hFlow hCirc Y G hY hG _hYm _hYb _hGi τ hτ ψ hψ
  obtain ⟨V, LV, hVr, hLVr, hVd⟩ :=
    hV P hP B b hB hb ν hν hνs tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr f w u hFlow hCirc
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

theorem complMildEqRegSmall_of_tested (κ : PlanarFrameKernels)
    (hT : ComplMildTestedSmall κ) : ComplMildEqRegSmall κ := by
  intro hκ P hP m hm
  obtain ⟨ν₀, hν₀, hT⟩ := hT hκ P hP m hm
  refine ⟨ν₀, hν₀, ?_⟩
  intro K B b hB0 hb ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF
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
    have h := hT K B b hB0 hb ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel
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

theorem complMovingMildRegSmall_of (κ : PlanarFrameKernels) (h1 : ComplYExists κ)
    (h2 : ComplGExists κ) (h3 : ComplMildEqRegSmall κ) :
    ComplMovingMildRegSmall κ := by
  intro hκ P hP m hm
  obtain ⟨ν₀, hν₀, h3⟩ := h3 hκ P hP m hm
  refine ⟨ν₀, hν₀, ?_⟩
  intro K B b hB hb ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF
    f w u hFlow hCirc
  dsimp only
  obtain ⟨Y, hY, hYm, hYb, hc1, hc2⟩ :=
    h1 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  obtain ⟨G, hG, hGi, hcm⟩ :=
    h2 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  exact ⟨Y, G, hY, hG, hYm, hYb, hGi,
    h3 K B b hB hb ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr hRegF
      f w u hFlow hCirc Y G hY hG hYm hYb hGi, hc1, hc2, hcm⟩

theorem complBlockDuhamelSplitReg_of_mildSmall (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ)
    (hMild : ComplMovingMildRegSmall κ) :
    ComplBlockDuhamelSplitReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨ν₁, hν₁, hMild⟩ := hMild hκ P hP m hm
  obtain ⟨b₀, hb₀⟩ := hReg hκ P hP m hm K B hB
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, hRegν⟩ := hb₀ b hb hb1
  refine ⟨min ν₀ ν₁, lt_min hν₀ hν₁, fun ν hν hνle' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc => ?_⟩
  dsimp only
  have hνle : ν ≤ ν₀ := hνle'.trans (min_le_left _ _)
  have hνle₁ : ν ≤ ν₁ := hνle'.trans (min_le_right _ _)
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  obtain ⟨hFc, hAm, hAb⟩ := hRegν ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂
    hB_eq F_rel A_rel hF_rel hA_rel
  obtain ⟨Y, G, hYrep, hGrep, hYm, hYb, hGi, hYmild, hc₁, hc₂, hcmf⟩ :=
    hMild K B b hB hb1 ν hν hνle₁ hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
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

/-- **Final assembly** (regime form, `ν ≤ ν₀(m)`). -/
theorem complBlockDuhamelVoCReg_of_leavesSmall (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ) (h1 : ComplYExists κ)
    (h2 : ComplGExists κ) (hT : ComplMildTestedSmall κ) : ComplBlockDuhamelVoCReg κ :=
  complBlockDuhamelVoCReg_of κ (complBlockDuhamelSplitReg_of_mildSmall κ hVoC hReg
    (complMovingMildRegSmall_of κ h1 h2 (complMildEqRegSmall_of_tested κ hT)))

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
