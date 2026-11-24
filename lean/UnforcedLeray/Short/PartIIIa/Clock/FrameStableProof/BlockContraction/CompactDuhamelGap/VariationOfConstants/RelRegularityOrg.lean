import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplit

/-!
# `PartIII-a:T21/c3/2/1/2/2`: organization of `RelBlockRegularity`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925 and
2962-2982.  `IsPeriodizedRelFreeBlockEvol` / `IsDampedComplBlockInt` pin `F_rel`, `A_rel` only a.e.
on dense test classes, so `RelBlockRegularity` needs the PDE facts below (leaves).  This file proves
`relBlockRegularity_of` from them (3-epsilon / density argument).

Leaves (each a `Prop` over the binders of `RelBlockRegularity`):
* `RelB1` (SP 2962-2970): uniform bound of `F_rel` on `blockTriangle B` (free cylinder energy bound
  `IIb.IsFreeCylFlow`, extension from the dense class).
* `RelB3` (SP 2919-2921): density of `relFreeClass` (cell-restricted `JscaleInv` of cylinder tests
  with a free cylinder flow from every start age of the block; existence of the flow included).
* `RelB4` (SP 2960-2970): continuity of the pinned expression in `(τ, σ)` (continuity of the free
  cylinder flow in the start age).
* `RelB5` (SP 2974-2982): uniform bound of `A_rel` on `[0, B]`.
* `RelB6a` (SP 2974-2978): measurability of `r ↦ A_rel r W` for smooth compactly supported `W`.
* `RelB6b`: density of smooth compactly supported representatives in `Planar.L2w m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub VariationOfConstantsMildSub
namespace RelRegularityOrg

/-- Standing data of `RelBlockRegularity` (all hypotheses before `F_rel`, `A_rel`). -/
def RelCtx (κ : PlanarFrameKernels) (P : PlanarData) (m K B b ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) : Prop :=
  IsSeedKernels κ ∧ IsPlanarReference P ∧ 8 < m ∧ 0 < B ∧ 1 ≤ b ∧ 0 < ν ∧
    PerFrameFacts κ ν m b K ∧ UnforcedLeray.Short.PartI.IsBUCTrain tr ∧
    0 ≤ t₁ ∧ t₁ ≤ t₂ ∧ b ≤ clockTheta ν t₂ ∧ movingZ ν t₂ - movingZ ν t₁ = B

/-- Dense class: `W` agrees on the cell with `JscaleInv f` for a cylinder test `f` carrying a free
cylinder flow, at every start age of the block. -/
def relFreeClass (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ B : ℝ) :
    Set (Planar.L2w m) :=
  {W | ∀ σ ∈ Icc (0 : ℝ) B,
    let s := ageAt ν t₁ σ
    let d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
    ∃ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f ∧
      ∃ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀ ∧
        ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d_s →
          (W : ℂ → ℂ) z = JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)}

/-- Smooth compactly supported representatives in `Planar.L2w m`. -/
def relSmoothClass (m : ℝ) : Set (Planar.L2w m) :=
  {W | ∃ Φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
    ⇑W =ᵐ[volume] fun z : ℂ => Φ (cToPlane z)}

def RelB1 (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      ∃ M : ℝ, ∀ p ∈ blockTriangle B, ‖F_rel p.1 p.2‖ ≤ M

def RelB3 (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    Dense (relFreeClass ν m tr t₁ B)

def RelB4 (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ W ∈ relFreeClass ν m tr t₁ B,
      ∃ G : ℝ × ℝ → Planar.L2w m, ContinuousOn G (blockTriangle B) ∧
        ∀ p ∈ blockTriangle B,
          let s := ageAt ν t₁ p.2
          let t := ageAt ν t₁ p.1
          let d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
          let d_t := cellLen (ν ^ (-2 : ℝ)) (clockA ν t)
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀ →
              (∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d_s →
                (W : ℂ → ℂ) z = JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)) →
              ⇑(G p) =ᵐ[volume] fun z : ℂ =>
                ((clockN P ν s t : ℂ)⁻¹) *
                  periodizedExt d_s d_t
                    (JscaleInv (clockA ν t) (fun x => ((ω₀ t x : ℝ) : ℂ)))
                    (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane z)

def RelB5 (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
      ∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A

def RelB6a (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
      ∀ W ∈ relSmoothClass m,
        AEStronglyMeasurable (fun r => A_rel r W) (volume.restrict (Icc (0 : ℝ) B))

def RelB6b : Prop := ∀ m : ℝ, 8 < m → Dense (relSmoothClass m)

theorem continuousOn_of_dense_bdd {α E : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Set α) (T : α → E →L[ℂ] E) (M : ℝ)
    (hM : ∀ p ∈ S, ‖T p‖ ≤ M) (D : Set E) (hD : Dense D)
    (hc : ∀ x ∈ D, ContinuousOn (fun p => T p x) S) (x : E) :
    ContinuousOn (fun p => T p x) S := by
  intro p hp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hpos : 0 < ε / (3 * (M + 1)) := by positivity
  obtain ⟨y, hy, hyD⟩ := Metric.dense_iff.mp hD x _ hpos
  have hy' : dist x y < ε / (3 * (M + 1)) := by simpa [dist_comm] using hy
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hc y hyD p hp) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun q hq hqd => ?_⟩
  have hb : ∀ r ∈ S, dist (T r x) (T r y) < ε / 3 := by
    intro r hr
    rw [dist_eq_norm, ← map_sub]
    calc ‖T r (x - y)‖ ≤ ‖T r‖ * ‖x - y‖ := (T r).le_opNorm _
      _ ≤ M * ‖x - y‖ := by gcongr; exact hM r hr
      _ < (M + 1) * (ε / (3 * (M + 1))) := by
          rw [← dist_eq_norm]
          calc M * dist x y ≤ (M + 1) * dist x y := by gcongr; linarith
            _ < (M + 1) * (ε / (3 * (M + 1))) := by gcongr
      _ = ε / 3 := by field_simp
  have h1 := hb q hq
  have h2 := hb p hp
  have h3 := hδ' hq hqd
  calc dist (T q x) (T p x) ≤ dist (T q x) (T q y) + dist (T q y) (T p y) + dist (T p y) (T p x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := dist_comm (T p y) (T p x)
        rw [this]; linarith
    _ = ε := by ring

theorem aestronglyMeasurable_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure ℝ) (T : ℝ → E →L[ℂ] E) (D : Set E) (hD : Dense D)
    (hc : ∀ x ∈ D, AEStronglyMeasurable (fun r => T r x) μ) (x : E) :
    AEStronglyMeasurable (fun r => T r x) μ := by
  obtain ⟨y, hyD, hy⟩ := mem_closure_iff_seq_limit.mp (hD x)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n r => T r (y n)) (g := fun r => T r x)
    (fun n => hc _ (hyD n)) (Filter.Eventually.of_forall fun r => ?_)
  exact ((T r).continuous.tendsto x).comp hy

/-- Conditional regularity: `RelBlockRegularity` from the PDE leaves. -/
theorem relBlockRegularity_of (κ : PlanarFrameKernels)
    (h1 : RelB1 κ) (h3 : RelB3 κ) (h4 : RelB4 κ) (h5 : RelB5 κ) (h6a : RelB6a κ)
    (h6b : RelB6b) :
    VariationOfConstantsMildSub.RelBlockRegularity κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBz F_rel A_rel hFp hAp
  have ctx : RelCtx κ P m K B b ν tr t₁ t₂ := ⟨hκ, hP, hm, hB, hb, hν, hF, htr, ht₁, ht₁₂, hbt, hBz⟩
  refine ⟨fun x => ?_, fun x => ?_, h5 P m K B b ν tr t₁ t₂ ctx A_rel hAp⟩
  · obtain ⟨M, hM⟩ := h1 P m K B b ν tr t₁ t₂ ctx F_rel hFp
    refine continuousOn_of_dense_bdd (blockTriangle B) (fun p => F_rel p.1 p.2) M hM _
      (h3 P m K B b ν tr t₁ t₂ ctx) (fun W hW => ?_) x
    obtain ⟨G, hG, hGp⟩ := h4 P m K B b ν tr t₁ t₂ ctx W hW
    refine hG.congr (fun p hp => ?_)
    obtain ⟨hp0, hp1, hp2⟩ := hp
    obtain ⟨f, hf, ω₀, hω, hag⟩ := hW p.2 ⟨hp0, hp1.trans hp2⟩
    have e1 := hFp p.2 p.1 hp0 hp1 hp2 f hf ω₀ hω W hag
    have e2 := hGp p ⟨hp0, hp1, hp2⟩ f hf ω₀ hω hag
    exact Lp.ext ((Planar.wMeasure_ac m).ae_le (e1.trans e2.symm))
  · exact aestronglyMeasurable_of_dense _ A_rel (relSmoothClass m) (h6b m hm)
      (fun W hW => h6a P m K B b ν tr t₁ t₂ ctx A_rel hAp W hW) x

/-- Leaf grouping (R4): density and continuity of the free-flow class. -/
def RelB34 (κ : PlanarFrameKernels) : Prop := RelB3 κ ∧ RelB4 κ
/-- Leaf grouping (R4): measurability data of `A_rel`. -/
def RelB6 (κ : PlanarFrameKernels) : Prop := RelB6a κ ∧ RelB6b

theorem relBlockRegularity_of_leaves (κ : PlanarFrameKernels)
    (h1 : RelB1 κ) (h34 : RelB34 κ) (h5 : RelB5 κ) (h6 : RelB6 κ) :
    VariationOfConstantsMildSub.RelBlockRegularity κ :=
  relBlockRegularity_of κ h1 h34.1 h34.2 h5 h6.1 h6.2

end RelRegularityOrg
end UnforcedLeray.Short.IIIa
