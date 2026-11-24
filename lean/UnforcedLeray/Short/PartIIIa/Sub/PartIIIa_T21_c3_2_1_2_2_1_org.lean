import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularityOrg

/-!
# `PartIII-a:T21/c3/2/1/2/2/1/org`: corrected leaves for the `F_rel` part of `RelBlockRegularity`

Source of record: `the November 2 reference manuscript` (SP) 2919-2925, 2941-2970.

Diagnosis.  `IsPeriodizedRelFreeBlockEvol` pins `F_rel τ σ` for each fixed `σ` separately, on the
set of `W` that agree on the cell `d(s)` (`s = ageAt ν t₁ σ`) with `JscaleInv f` for a cylinder test
`f`, with arbitrary exterior values.  That per-`σ` class is dense in `Planar.L2w m` (cell tests are
dense in the weighted cell `L²`, the exterior is free), so `F_rel τ σ` is determined.  The old
`RelB3` asked one `W` to be of this form for every `σ` at once (the cells `d(s)` differ with `s`),
which is not the density used by the source and is not claimed here.  The source's route
(SP 2960-2970): a uniform energy bound on the dense per-`σ` class gives the operator bound
(`RelB1`), and then strong continuity in `(τ, σ)` of the explicit pinned expression
(`F_rel = N⁻¹ (I_t F_free R_s + S(t,s)(I - Π_s))`, with strong continuity of the free flow in the start
age and of the dilation) extends from the uniform bound.

This file replaces `RelB3`, `RelB4`, `RelB34` (left untouched in `RelRegularityOrg`) by:
* `RelB3s`: per-`σ` density of the class `relFreeClassAt`;
* `RelB1c`: uniform energy bound on that class (SP 2962-2970);
* `RelB4s`: strong continuity of any pinned, uniformly bounded `F_rel` (SP 2960-2970);
and proves `relB1_of` and `relBlockRegularity_of'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub VariationOfConstantsMildSub
open RelRegularityOrg
namespace RelRegularityOrg2

/-- The dense class at one start position `σ`: `W` agrees on the cell `d(s)` with `JscaleInv f`
for `f₁ + I f₂` with cylinder tests `f₁, f₂` each carrying a free cylinder flow from age `s = ageAt ν t₁ σ`
(exterior values of `W` arbitrary; SP 2919-2921, 2941). -/
def relFreeClassAt (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ σ : ℝ) :
    Set (Planar.L2w m) :=
  {W | let s := ageAt ν t₁ σ
    let d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
    ∃ f₁ f₂ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁ ∧ B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂ ∧
      (∃ ω₁ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f₁ ω₁) ∧
      (∃ ω₂ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f₂ ω₂) ∧
        ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d_s →
          (W : ℂ → ℂ) z = JscaleInv (clockA ν s)
            (fun x => ((f₁ x : ℝ) : ℂ) + Complex.I * ((f₂ x : ℝ) : ℂ)) (cToPlane z)}

/-- Per-`σ` density of `relFreeClassAt` in `Planar.L2w m` (SP 2919-2921; existence of the free
cylinder flow for cylinder tests, density of cell tests in the weighted cell `L²`, exterior free). -/
def RelB3s (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ σ ∈ Icc (0 : ℝ) B, Dense (relFreeClassAt ν m tr t₁ σ)

/-- Uniform energy bound of the pinned `F_rel` on the per-`σ` class (SP 2962-2970,
`eq:short-causal-free-moving` with the weighted energy identity). -/
def RelB1c (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∃ M : ℝ, ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
        ∀ W ∈ relFreeClassAt ν m tr t₁ σ, ‖F_rel τ σ W‖ ≤ M * ‖W‖

/-- Strong continuity on the block triangle of a pinned, uniformly bounded `F_rel`
(SP 2960-2970: strong continuity of the free cylinder flow in start age and time, of the dilation
`S(t,s)`, and of the cell rescaling, extended by the uniform bound). -/
def RelB4s (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      (∃ M : ℝ, ∀ p ∈ blockTriangle B, ‖F_rel p.1 p.2‖ ≤ M) →
      ∀ W : Planar.L2w m, ContinuousOn (fun p => F_rel p.1 p.2 W) (blockTriangle B)

/-- `RelB1` from the per-`σ` density and the class bound. -/
theorem relB1_of (κ : PlanarFrameKernels) (h3 : RelB3s κ) (h1 : RelB1c κ) : RelB1 κ := by
  intro P m K B b ν tr t₁ t₂ ctx F_rel hFp
  obtain ⟨M, hM⟩ := h1 P m K B b ν tr t₁ t₂ ctx
  refine ⟨max M 0, fun p hp => ?_⟩
  obtain ⟨hp0, hp1, hp2⟩ := hp
  have hσ : p.2 ∈ Icc (0 : ℝ) B := ⟨hp0, hp1.trans hp2⟩
  have hdense := h3 P m K B b ν tr t₁ t₂ ctx p.2 hσ
  have hcl : IsClosed {W : Planar.L2w m | ‖F_rel p.1 p.2 W‖ ≤ max M 0 * ‖W‖} :=
    isClosed_le ((F_rel p.1 p.2).continuous.norm) (continuous_const.mul continuous_norm)
  have hsub : relFreeClassAt ν m tr t₁ p.2 ⊆ {W : Planar.L2w m | ‖F_rel p.1 p.2 W‖ ≤ max M 0 * ‖W‖} :=
    fun W hW => (hM F_rel hFp p.2 p.1 hp0 hp1 hp2 W hW).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hall : ∀ W, ‖F_rel p.1 p.2 W‖ ≤ max M 0 * ‖W‖ := fun W => by
    have : W ∈ closure (relFreeClassAt ν m tr t₁ p.2) := hdense W
    exact (closure_minimal hsub hcl) this
  exact (F_rel p.1 p.2).opNorm_le_bound (le_max_right _ _) hall

/-- `RelBlockRegularity` from the corrected leaves. -/
theorem relBlockRegularity_of' (κ : PlanarFrameKernels)
    (h1 : RelB1 κ) (h4 : RelB4s κ) (h5 : RelB5 κ) (h6 : RelB6 κ) :
    VariationOfConstantsMildSub.RelBlockRegularity κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBz F_rel A_rel hFp hAp
  have ctx : RelCtx κ P m K B b ν tr t₁ t₂ := ⟨hκ, hP, hm, hB, hb, hν, hF, htr, ht₁, ht₁₂, hbt, hBz⟩
  refine ⟨fun x => ?_, fun x => ?_, h5 P m K B b ν tr t₁ t₂ ctx A_rel hAp⟩
  · exact h4 P m K B b ν tr t₁ t₂ ctx F_rel hFp (h1 P m K B b ν tr t₁ t₂ ctx F_rel hFp) x
  · exact aestronglyMeasurable_of_dense _ A_rel (relSmoothClass m) (h6.2 m hm)
      (fun W hW => h6.1 P m K B b ν tr t₁ t₂ ctx A_rel hAp W hW) x

theorem relBlockRegularity_of_leaves' (κ : PlanarFrameKernels)
    (h3 : RelB3s κ) (h1c : RelB1c κ) (h4 : RelB4s κ) (h5 : RelB5 κ) (h6 : RelB6 κ) :
    VariationOfConstantsMildSub.RelBlockRegularity κ :=
  relBlockRegularity_of' κ (relB1_of κ h3 h1c) h4 h5 h6

end RelRegularityOrg2
end UnforcedLeray.Short.IIIa
