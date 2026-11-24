import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/1`: split of `MovSolTestedDuhamel` (SP 2861-2866, 2937-2945)

`MovSolTestedDuhamel` = existence of `V = N⁻¹ I_d W`, `LV = N⁻¹ I_d L_int W` in `L²_m`
(`MovSolExists`) + tested Duhamel for any such representatives (`MovSolDuhamelOf`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

/-- **Leaf A** (SP 2861-2866): `V`, `LV` exist in `L²_m` as the normalised zero extensions
of `W = J_a⁻¹ w` and `L_int W` (`W ∈ X_{m,d}`, `L_int W ∈ L²_m` from the weak equation). -/
def MovSolExists : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∃ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V ∧ LVRep P m B ν tr t₁ w LV

/-- **Leaf B** (SP 2937-2945): tested Duhamel relative to `F_rel` for any representatives
`V`, `LV` (weak equation tested against the backward free cylinder flow of `ψ`). -/
def MovSolDuhamelOf : Prop :=
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
            ∀ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V → LVRep P m B ν tr t₁ w LV →
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) volume 0 τ ∧
                ⟪ψ, V τ⟫_ℂ = ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ

theorem movSolTestedDuhamel_of (hA : MovSolExists) (hB : MovSolDuhamelOf) :
    MovSolTestedDuhamel := by
  intro P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ F hF f w u hfl hz
  obtain ⟨V, LV, hV, hLV⟩ := hA P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl hz
  exact ⟨V, LV, hV, hLV, hB P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ F hF f w u hfl hz
    V LV hV hLV⟩

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
