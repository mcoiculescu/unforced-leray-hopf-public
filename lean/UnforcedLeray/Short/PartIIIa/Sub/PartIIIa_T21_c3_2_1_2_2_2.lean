import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_1_org

/-!
# Sub file for `PartIII-a:T21/c3/2/1/2/2/2` (RelB4s): reduction to local dense continuity `RelB4loc`

Source: `the November 2 reference manuscript` lines 2941-2970.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub
open RelRegularityOrg
namespace RelRegularityOrg2

/-- 3-epsilon argument at one point: a uniformly bounded operator family is strongly continuous
within `S` at `p` if it is so on a dense set of vectors. -/
theorem continuousWithinAt_of_dense_bdd {α E : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Set α) (T : α → E →L[ℂ] E) (M : ℝ)
    (hM : ∀ p ∈ S, ‖T p‖ ≤ M) {p : α} (hp : p ∈ S) (D : Set E) (hD : Dense D)
    (hc : ∀ x ∈ D, ContinuousWithinAt (fun q => T q x) S p) (x : E) :
    ContinuousWithinAt (fun q => T q x) S p := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hpos : 0 < ε / (3 * (M + 1)) := by positivity
  obtain ⟨y, hy, hyD⟩ := Metric.dense_iff.mp hD x _ hpos
  have hy' : dist x y < ε / (3 * (M + 1)) := by simpa [dist_comm] using hy
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hc y hyD) (ε / 3) (by positivity)
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

/-- Local dense continuity of the pinned relative free evolution (SP 2941-2970): near every point
`p₀` of the block triangle there is a dense set of `W` on which `p ↦ F_rel p.1 p.2 W` is continuous
at `p₀` within the triangle (free cylinder flow continuous in start age, datum and time; strong
continuity of the cell rescaling, of the periodized extension and of the dilation `S(t,s)`). -/
def RelB4loc (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      ∀ p₀ ∈ blockTriangle B, ∃ D : Set (Planar.L2w m), Dense D ∧
        ∀ W ∈ D, ContinuousWithinAt (fun p : ℝ × ℝ => F_rel p.1 p.2 W) (blockTriangle B) p₀

/-- `RelB4s` from the local dense continuity and the uniform bound. -/
theorem relB4s_of_loc (κ : PlanarFrameKernels) (h : RelB4loc κ) : RelB4s κ := by
  intro P m K B b ν tr t₁ t₂ ctx F_rel hF hM W p₀ hp₀
  obtain ⟨M, hM⟩ := hM
  obtain ⟨D, hD, hc⟩ := h P m K B b ν tr t₁ t₂ ctx F_rel hF p₀ hp₀
  exact continuousWithinAt_of_dense_bdd (blockTriangle B) (fun p => F_rel p.1 p.2) M hM hp₀ D hD
    hc W

end RelRegularityOrg2
end UnforcedLeray.Short.IIIa
