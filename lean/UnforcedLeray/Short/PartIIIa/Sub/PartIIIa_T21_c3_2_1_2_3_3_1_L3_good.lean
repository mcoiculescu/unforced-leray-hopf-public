import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L3

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/3/1`: the good-age package on the block regime (BLOCKED)

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925
(`eq:short-causal-damped-complement`), 2974-2978 (the interaction is bounded on `X_{m,d}`).

Target (not proved here): `GoodAtBlock κ` (defined in `…_L3.lean`, namespace
`ComplMildTestedSplit`, not `ComplMildTestedSplit.ARelRoughSub`).

Regime. `1 ≤ b ≤ θ(r) = (ν(1+νr))⁻¹` forces `ν ≤ 1` and `d(r) = ν⁻²/√(1+νr) ≥ ν^{-3/2} ≥ 1`, so
the clause `1 ≤ d(r)` of `GoodAt` is not the obstruction.

Obstruction. `GoodAt` asks for an `X_{m,d}` bound of `movLInt W = -(K_d W)·∇E_mov` for every
`W ∈ X_{m,d}`. For `W` with nonzero cell integral `Γ`, `(K_d W)₁ → ∓Γ/(2d)` as `y₂ → ±∞`
(`kerD = Cyl.bsKernel d`, the full cylinder kernel), so the bound needs weighted decay of
`∂₁E_mov(r)` on the moving cell (`IIb.IsCylWeightedCoeff … (movingTrainGradE tr r)`); the same
decay is needed for `movLamDualEulerSub` (the `kerAdj` term against `∇E_c`) to lie in
`X_{-m,d}`, which the a.e. additivity clause also uses. `IsBUCTrain` gives only bounded
derivatives; the train tails of Part I (`TrainVorticityGaussianTail`, `TrainFluctuationDecay`,
`RescaledTrainBoundsBUC`) are stated only for `ν ≤ ν₀`. Hence `GoodAtBlock` is not derivable for
`ν ∈ (ν₀, 1/b]`; and for `θ(r) < b₀` the proved inputs `trainCoeff_bounds`,
`movLamDualHeatBound`, `movLamDualEulerSubBound` (all `b ≥ b₀`, `ν ≤ ν₀(b)`) do not apply
(`complModeForceOscillator` already holds with `b₀ = ν₀ = 1`).

Proved here: the regime-restricted package `goodAtBlockReg` (`b ≥ b₀`, `ν ≤ ν₀(b)`, directly from
`OrgSplit.RelIntA.goodAt_package`) and the correspondingly restricted rough extension

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub BlockPropagatorInteriorSub

namespace ComplMildTestedSplit

namespace ARelRoughSub

/-- `GoodAtBlock` restricted to the regime of `OrgSplit.RelIntA.goodAt_package`:
`b ≥ b₀(κ, P, m, K)` and `ν ≤ ν₀(b)`. -/
def GoodAtBlockReg (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ, ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ ν ∈ Ioc 0 ν₀, PerFrameFacts κ ν m b K →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
          ∃ K_A : ℝ, 0 ≤ K_A ∧ OrgSplit.RelIntA.GoodAt κ P m K_A tr r

/-- The good-age package on the restricted block regime. -/
theorem goodAtBlockReg (κ : PlanarFrameKernels) : GoodAtBlockReg κ := by
  intro hκ P _hP m hm K
  obtain ⟨K_A, b₀, hK, hb₀, H⟩ := OrgSplit.RelIntA.goodAt_package κ hκ P m hm K
  refine ⟨b₀, hb₀, fun b hb => ?_⟩
  obtain ⟨ν₀, hν₀, hν₀1, H'⟩ := H b hb
  exact ⟨ν₀, hν₀, hν₀1, fun ν hν hF tr htr r hr hθ => ⟨K_A, hK, H' ν hν hF tr htr r hr hθ⟩⟩

/-- `ARelRough` restricted to the regime `b ≥ b₀`, `ν ≤ ν₀(b)` of `goodAtBlockReg`. -/
def ARelRoughReg (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ, ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ B b : ℝ, 0 < B → b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ ν ∈ Ioc 0 ν₀, PerFrameFacts κ ν m b K →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
            IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
            ∀ σ ∈ Icc (0 : ℝ) B, ∀ Φ : ℝ × ℝ → ℂ,
              MemLp Φ 2
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) →
              ∀ X : Planar.L2w m,
                (⇑X =ᵐ[volume] fun z : ℂ =>
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) Φ
                    (cToPlane z)) →
                ⇑(A_rel σ X) =ᵐ[volume] fun z : ℂ =>
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
                    (movDampedComplInt κ P tr (ageAt ν t₁ σ) Φ) (cToPlane z)

/-- The restricted rough extension, from the restricted good-age package. -/
theorem aRelRoughReg (κ : PlanarFrameKernels) : ARelRoughReg κ := by
  intro hκ P hP m hm K
  obtain ⟨b₀, hb₀, H⟩ := goodAtBlockReg κ hκ P hP m hm K
  refine ⟨b₀, hb₀, fun B b _hB hb => ?_⟩
  obtain ⟨ν₀, hν₀, hν₀1, H'⟩ := H b hb
  refine ⟨ν₀, hν₀, hν₀1, fun ν hνI hF tr htr t₁ t₂ ht₁ _ht₁₂ hbθ hZ A_rel hA σ hσ Φ _hΦ X hX =>
    ?_⟩
  have hν : 0 < ν := hνI.1
  have ht₂ : 0 ≤ t₂ := ht₁.trans _ht₁₂
  have hs : 0 ≤ ageAt ν t₁ σ :=
    RelExteriorSub.ageAt_nonneg hν ht₁ ht₂ hσ.1 (by rw [hZ]; exact hσ.2)
  have hle : ageAt ν t₁ σ ≤ t₂ := by
    have h := ageAt_mono_on_block hν ht₁ ht₂ hZ hσ.1 hσ.2 le_rfl
    rwa [ageAt_eq_of_movingZ_sub hν ht₂ hZ] at h
  have hθ : b ≤ clockTheta ν (ageAt ν t₁ σ) :=
    hbθ.trans (clockTheta_le_of_le hν hs hle)
  obtain ⟨K_A, hK, hGA⟩ := H' ν hνI hF tr htr _ hs hθ
  exact aRel_rough_of_goodAt hA hσ hK hGA Φ X hX

end ARelRoughSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
