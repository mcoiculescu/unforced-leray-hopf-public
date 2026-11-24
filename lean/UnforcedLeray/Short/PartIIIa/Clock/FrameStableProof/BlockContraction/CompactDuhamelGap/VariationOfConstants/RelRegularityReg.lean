import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularityOrg
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplitReg

/-!
# Regime form of the PDE leaves of `RelBlockRegularity` (`PartIII-a:T21/c3/2/1/2/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2974-2982.
The source gives the `A_rel` bound only for `b ≥ b_prop`, `ν ≤ ν_prop(b)`.  `RelB5Reg` is `RelB5`
with these regime quantifiers; `relBlockRegularityReg_of_leaves` assembles
`RelBlockRegularityReg` from `RelB1`, `RelB34`, `RelB5Reg`, `RelB6` (the other leaves are
unchanged).  The free `RelB5` is false as stated for `b` or `ν` outside the regime and is not used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub
namespace RelRegularityOrg

/-- Leaf `RelB5` in the source regime (SP 2974-2982). -/
def RelB5Reg (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ → ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → 1 ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ ν ∈ Ioc 0 ν₀, ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
    RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
      ∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A

theorem relBlockRegularityReg_of_leaves (κ : PlanarFrameKernels)
    (h1 : RelB1 κ) (h34 : RelB34 κ) (h5 : RelB5Reg κ) (h6 : RelB6 κ) :
    VariationOfConstantsMildSub.RelBlockRegularityReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := h5 hκ P hP m hm K B hB
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, h5'⟩ := hb₀ b hb hb1
  refine ⟨ν₀, hν₀, fun ν hν hνle hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBz F_rel A_rel hFp hAp => ?_⟩
  have ctx : RelCtx κ P m K B b ν tr t₁ t₂ := ⟨hκ, hP, hm, hB, hb1, hν, hF, htr, ht₁, ht₁₂, hbt, hBz⟩
  refine ⟨fun x => ?_, fun x => ?_, h5' ν ⟨hν, hνle⟩ tr t₁ t₂ ctx A_rel hAp⟩
  · obtain ⟨M, hM⟩ := h1 P m K B b ν tr t₁ t₂ ctx F_rel hFp
    refine continuousOn_of_dense_bdd (blockTriangle B) (fun p => F_rel p.1 p.2) M hM _
      (h34.1 P m K B b ν tr t₁ t₂ ctx) (fun W hW => ?_) x
    obtain ⟨G, hG, hGp⟩ := h34.2 P m K B b ν tr t₁ t₂ ctx W hW
    refine hG.congr (fun p hp => ?_)
    obtain ⟨hp0, hp1, hp2⟩ := hp
    obtain ⟨f, hf, ω₀, hω, hag⟩ := hW p.2 ⟨hp0, hp1.trans hp2⟩
    have e1 := hFp p.2 p.1 hp0 hp1 hp2 f hf ω₀ hω W hag
    have e2 := hGp p ⟨hp0, hp1, hp2⟩ f hf ω₀ hω hag
    exact Lp.ext ((Planar.wMeasure_ac m).ae_le (e1.trans e2.symm))
  · exact aestronglyMeasurable_of_dense _ A_rel (relSmoothClass m) (h6.2 m hm)
      (fun W hW => h6.1 P m K B b ν tr t₁ t₂ ctx A_rel hAp W hW) x

end RelRegularityOrg
end UnforcedLeray.Short.IIIa
