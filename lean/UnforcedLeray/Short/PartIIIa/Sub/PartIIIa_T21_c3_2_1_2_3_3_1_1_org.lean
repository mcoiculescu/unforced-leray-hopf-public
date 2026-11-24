import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_A

/-!
# Small-viscosity form of `MovSolTestedDuhamel`

The weighted train gradient bound behind Leaf A is available only for `ν ≤ ν₀(m)`
(`CutFTCDual.ladTrainBddAll_unconditional`), the standing smallness of the shorter proof (SP 2861-2873,
3050-3051). `MovSolTestedDuhamelSmall` is `MovSolTestedDuhamel` for `ν ≤ ν₀(m)`; it follows from
`movSolExistsSmall` and `MovSolDuhamelOf` (all `ν`). The all-`ν` `MovSolExists` is not provable from
Part I; consumers (`complMildTested_of`, `ComplMildTested`) need the matching `ν ≤ ν₀(m)` form.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

/-- `MovSolTestedDuhamel` in the small-viscosity regime `ν ≤ ν₀(m)`. -/
def MovSolTestedDuhamelSmall : Prop :=
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
            ∃ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V ∧ LVRep P m B ν tr t₁ w LV ∧
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) volume 0 τ ∧
                ⟪ψ, V τ⟫_ℂ = ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ

theorem movSolTestedDuhamelSmall_of (hA : MovSolExistsSmall) (hB : MovSolDuhamelOf) :
    MovSolTestedDuhamelSmall := by
  intro m hm
  obtain ⟨ν₀, hν₀, h⟩ := hA m hm
  refine ⟨ν₀, hν₀, fun P hP B b hB0 hb ν hν hνs tr htr t₁ t₂ h1 h12 hθ hZ F hF f w u hfl hz => ?_⟩
  obtain ⟨V, LV, hV, hLV⟩ := h P hP B b hB0 hb ν hν hνs tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl hz
  exact ⟨V, LV, hV, hLV, hB P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ F hF f w u hfl hz
    V LV hV hLV⟩

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
