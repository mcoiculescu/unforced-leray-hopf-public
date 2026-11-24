import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB6

/-!
# `PartIII-a:T21/c3/2/1/2/3/3` (Leaf C3 `ComplMildEq`): reduction to a tested identity

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925.

This file does NOT prove `ComplMildEq`. It isolates its PDE content.

* As stated, `ComplMildEq` asserts an identity involving the Bochner integral
  `∫₀^τ F_rel τ σ (A_rel σ (Y σ) + G σ)`, which is `0` unless the integrand is integrable. Its
  hypotheses pin `F_rel`, `A_rel` only on test data; the integrability needs the regularity of
  leaf B (`VariationOfConstantsMildSub.RelBlockRegularity`: strong continuity of `F_rel` on the
  block triangle, strong measurability and boundedness of `A_rel`).
* `ComplMildTested` (the PDE content, weak-to-mild duality, SP 2914-2925): the mild identity
  tested against smooth compactly supported `ψ` (`RelRegularityOrg.relSmoothClass`), with the
  integral of the scalar pairing.
* `complMildEq_of_tested` (proved): `RelBlockRegularity κ → ComplMildTested κ → ComplMildEq κ`
  (Banach–Steinhaus bound for `F_rel τ ·` on `[0, τ]`, strong measurability of strongly
  measurable operator families applied to strongly measurable paths, `integral_inner`, density
  `RelRegularityOrg.relB6b_leaf`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildSplit

/-- **Leaf C3' (PDE, weak-to-mild duality, SP 2914-2925)**: the mild equation of the normalised
zero-extended moving complement relative to `(F_rel, A_rel)`, tested against smooth compactly
supported `ψ`, with the integral of the scalar pairing. -/
def ComplMildTested (κ : PlanarFrameKernels) : Prop :=
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
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                ⟪ψ, Y τ⟫_ℂ = ⟪ψ, F_rel τ 0 (Y 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (A_rel σ (Y σ) + G σ)⟫_ℂ

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A strongly measurable operator family applied to a simple path is strongly measurable. -/
theorem aesm_clm_apply_simpleFunc {μ : Measure ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ∀ x, AEStronglyMeasurable (fun r => A r x) μ) (s : SimpleFunc ℝ E) :
    AEStronglyMeasurable (fun r => A r (s r)) μ := by
  refine SimpleFunc.induction (motive := fun s => AEStronglyMeasurable (fun r => A r (s r)) μ)
    ?_ ?_ s
  · intro c S hS
    have heq : (fun r => A r ((SimpleFunc.piecewise S hS (SimpleFunc.const ℝ c)
        (SimpleFunc.const ℝ 0)) r)) = S.indicator (fun r => A r c) := by
      funext r
      by_cases hr : r ∈ S
      · simp [SimpleFunc.coe_piecewise, Set.piecewise, hr]
      · simp [SimpleFunc.coe_piecewise, Set.piecewise, hr]
    rw [heq]
    exact (hA c).indicator hS
  · intro f g _ hf hg
    have heq : (fun r => A r ((f + g) r)) = fun r => A r (f r) + A r (g r) := by
      funext r
      simp [SimpleFunc.coe_add, map_add]
    rw [heq]
    exact hf.add hg

/-- A strongly measurable operator family applied to a strongly measurable path. -/
theorem aesm_clm_apply {μ : Measure ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ∀ x, AEStronglyMeasurable (fun r => A r x) μ) {Y : ℝ → E}
    (hY : AEStronglyMeasurable Y μ) : AEStronglyMeasurable (fun r => A r (Y r)) μ := by
  have hZ := hY.stronglyMeasurable_mk
  have h1 : AEStronglyMeasurable (fun r => A r (hY.mk Y r)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun n r => A r (hZ.approx n r))
      (fun n => aesm_clm_apply_simpleFunc A hA (hZ.approx n))
      (Eventually.of_forall fun r => ((A r).continuous.tendsto _).comp (hZ.tendsto_approx r))
  refine h1.congr ?_
  filter_upwards [hY.ae_eq_mk] with r hr
  rw [hr]

/-- Banach–Steinhaus: a strongly continuous operator family on a compact set is bounded. -/
theorem exists_bound_of_continuousOn_apply [CompleteSpace E] {S : Set ℝ} (hS : IsCompact S)
    (T : ℝ → E →L[ℂ] E) (hT : ∀ x, ContinuousOn (fun r => T r x) S) :
    ∃ M, ∀ r ∈ S, ‖T r‖ ≤ M := by
  have h : ∀ x, ∃ C, ∀ r : S, ‖(fun r : S => T r) r x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hT x)
    exact ⟨C, fun r => hC r r.2⟩
  obtain ⟨M, hM⟩ := banach_steinhaus h
  exact ⟨M, fun r hr => hM ⟨r, hr⟩⟩

end Abstract

/-- **Reduction of Leaf C3**: the regularity of leaf B and the tested identity give the mild
equation. -/
theorem complMildEq_of_tested (κ : PlanarFrameKernels)
    (hB : VariationOfConstantsMildSub.RelBlockRegularity κ) (hT : ComplMildTested κ) :
    ComplMildEq κ := by
  intro hκ P hP m hm K B b hB0 hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
    f w u hw hcirc Y G hY hG hYm hYb hGi τ hτ
  obtain ⟨hFc, hAm, K_A, hKA⟩ :=
    hB hκ P hP m hm K B b hB0 hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel hFr hAr
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
    have h := hT hκ P hP m hm K B b hB0 hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel A_rel
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

end ComplMildSplit
end UnforcedLeray.Short.IIIa
