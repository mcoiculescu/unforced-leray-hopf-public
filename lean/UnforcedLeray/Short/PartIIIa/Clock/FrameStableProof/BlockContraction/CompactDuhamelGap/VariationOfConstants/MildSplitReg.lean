import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplit

/-!
# Regime form of the block Duhamel split (`PartIII-a:T21/c3/2/1/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2974-2982.
The source bounds `A_rel` only for `b ≥ b_prop` and `ν ≤ ν_prop(b)`.  The `Reg` variants insert the
quantifiers `∃ b₀, ∀ b ≥ b₀, ∃ ν₀ > 0, ∀ ν ≤ ν₀` after `K B`:
* `RelBlockRegularityReg`: regime form of `RelBlockRegularity` (leaf B);
* `ComplBlockDuhamelSplitReg`, `ComplBlockDuhamelVoCReg`: regime forms of the split and of the
  variation-of-constants target;
* `complBlockDuhamelSplitReg_of_mild`, `complBlockDuhamelVoCReg_of_mild`: assembly from the leaves
  (`DuhamelVoCAbstract`, `RelBlockRegularityReg`, `ComplMovingMildReg`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub

namespace VariationOfConstantsMildSub

/-- Regime form of leaf B (SP 2974-2982). -/
def RelBlockRegularityReg (κ : PlanarFrameKernels) : Prop :=
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
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          (∀ x : Planar.L2w m,
            ContinuousOn (fun p : ℝ × ℝ => F_rel p.1 p.2 x) (blockTriangle B)) ∧
          (∀ x : Planar.L2w m,
            AEStronglyMeasurable (fun r => A_rel r x) (volume.restrict (Icc (0 : ℝ) B))) ∧
          (∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A)

/-- Regime form of `ComplMovingMild` (leaf C): the mild identity is asserted only under the
regularity conclusion of leaf B (`RelBlockRegularityReg`), which is what the source supplies
(SP 2974-2982, 2914-2925). -/
def ComplMovingMildReg (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
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

/-- Regime form of `ComplBlockDuhamelSplit`. -/
def ComplBlockDuhamelSplitReg (κ : PlanarFrameKernels) : Prop :=
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
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
            (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            let F := periodizedFrame κ ν m b K hν hF
            ∃ (H : ℝ≥0∞) (G : ℝ → ℝ≥0∞),
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
                H + ∫⁻ r in Ioc t₁ t₂, G r ∧
              H ≤ ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ∧
              ∀ r ∈ Ioc t₁ t₂,
                G r ≤
                  ENNReal.ofReal
                      ((clockA ν r) ^ (-2 : ℝ) *
                        (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
                    (∑ j : Fin 2,
                      ENNReal.ofReal ‖ampl F w r j‖ *
                        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                          (complModeForce κ P F tr r j))

/-- **Assembly (regime form)**: the three leaves give `ComplBlockDuhamelSplitReg κ`. -/
theorem complBlockDuhamelSplitReg_of_mild (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ) (hMild : ComplMovingMildReg κ) :
    ComplBlockDuhamelSplitReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := hReg hκ P hP m hm K B hB
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, hRegν⟩ := hb₀ b hb hb1
  refine ⟨ν₀, hν₀, fun ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc => ?_⟩
  dsimp only
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  obtain ⟨hFc, hAm, hAb⟩ := hRegν ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂
    hB_eq F_rel A_rel hF_rel hA_rel
  obtain ⟨Y, G, hYrep, hGrep, hYm, hYb, hGi, hYmild, hc₁, hc₂, hcmf⟩ :=
    hMild hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
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

/-- Regime form of `ComplBlockDuhamelVoC` (same quantifier insertion as the split). -/
def ComplBlockDuhamelVoCReg (κ : PlanarFrameKernels) : Prop :=
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
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
            (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            let F := periodizedFrame κ ν m b K hν hF
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
              ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
                ∫⁻ r in Ioc t₁ t₂,
                  ENNReal.ofReal
                      ((clockA ν r) ^ (-2 : ℝ) *
                        (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
                    (∑ j : Fin 2,
                      ENNReal.ofReal ‖ampl F w r j‖ *
                        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                          (complModeForce κ P F tr r j))

/-- Regime form of `complBlockDuhamelVoC_of`. -/
theorem complBlockDuhamelVoCReg_of (κ : PlanarFrameKernels)
    (hSplit : ComplBlockDuhamelSplitReg κ) : ComplBlockDuhamelVoCReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := hSplit hκ P hP m hm K B hB
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, h⟩ := hb₀ b hb hb1
  refine ⟨ν₀, hν₀, fun ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc => ?_⟩
  dsimp only
  obtain ⟨H, G, hsplit, hH, hG_pt⟩ :=
    h ν hν hνle hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
      F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  refine voc_ennreal_bound_of_split hsplit hH ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hG_pt r hr

/-- Regime form of `complBlockDuhamelVoC_of_mild`. -/
theorem complBlockDuhamelVoCReg_of_mild (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularityReg κ) (hMild : ComplMovingMildReg κ) :
    ComplBlockDuhamelVoCReg κ :=
  complBlockDuhamelVoCReg_of κ (complBlockDuhamelSplitReg_of_mild κ hVoC hReg hMild)

end VariationOfConstantsMildSub

end UnforcedLeray.Short.IIIa
