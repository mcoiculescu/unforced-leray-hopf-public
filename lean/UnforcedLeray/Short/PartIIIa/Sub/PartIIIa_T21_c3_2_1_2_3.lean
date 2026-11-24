import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplit

/-!
# `PartIII-a:T21/c3/2/1/2/3`: split of Leaf C (`ComplMovingMild`) into three PDE leaves

Source: `the November 2 reference manuscript` lines 2914-2925.
* `ComplYExists` (C1): the normalised zero-extended complement `Y` exists in `Planar.L2w m`,
  is measurable and bounded on the block, and `compl` is measurable at `t₁`, `t₂`.
* `ComplGExists` (C2): the mode forcing `G` exists, is integrable, with measurable `complModeForce`.
* `ComplMildEq` (C3, weak-to-mild duality): any such `Y`, `G` satisfy the mild equation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildSplit

/-- Representation of `Y` (SP 2914-2925). -/
def YRep (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (b K B ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ)
    (Y : ℝ → Planar.L2w m) : Prop :=
  ∀ τ ∈ Icc (0 : ℝ) B, ⇑(Y τ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
        (compl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ τ)) (cToPlane z)

/-- Representation of `G` (SP 2914-2925). -/
def GRep (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (b K B ν : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (G : ℝ → Planar.L2w m) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) B, ⇑(G σ) =ᵐ[volume] fun z : ℂ =>
    ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        (fun y => ∑ j : Fin 2, ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j *
          complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr (ageAt ν t₁ σ) j y)
        (cToPlane z)

/-- Leaf C1: existence of `Y`. -/
def ComplYExists (κ : PlanarFrameKernels) : Prop :=
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
            ∃ Y : ℝ → Planar.L2w m, YRep κ P m b K B ν hν hF t₁ w Y ∧
              AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) ∧
              (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) ∧
              AEStronglyMeasurable (compl (periodizedFrame κ ν m b K hν hF) w t₁)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m) ∧
              AEStronglyMeasurable (compl (periodizedFrame κ ν m b K hν hF) w t₂)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m)

/-- Leaf C2: existence of `G`. -/
def ComplGExists (κ : PlanarFrameKernels) : Prop :=
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
            ∃ G : ℝ → Planar.L2w m, GRep κ P m b K B ν hν hF tr t₁ w G ∧
              IntegrableOn G (Icc (0 : ℝ) B) ∧
              ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
                AEStronglyMeasurable
                  (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)
                  (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)

/-- Leaf C3: weak-to-mild duality for the represented `Y`, `G`. -/
def ComplMildEq (κ : PlanarFrameKernels) : Prop :=
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

theorem complMovingMild_of (κ : PlanarFrameKernels) (h1 : ComplYExists κ)
    (h2 : ComplGExists κ) (h3 : ComplMildEq κ) :
    VariationOfConstantsMildSub.ComplMovingMild κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
    f w u hFlow hCirc
  dsimp only
  obtain ⟨Y, hY, hYm, hYb, hc1, hc2⟩ :=
    h1 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  obtain ⟨G, hG, hGi, hcm⟩ :=
    h2 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc
  exact ⟨Y, G, hY, hG, hYm, hYb, hGi,
    h3 hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
      f w u hFlow hCirc Y G hY hG hYm hYb hGi, hc1, hc2, hcm⟩

end ComplMildSplit
end UnforcedLeray.Short.IIIa
