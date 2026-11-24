import UnforcedLeray.Short.PartIIb.Sub.T12_1_1_3
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Leaf `PartII-b:T12/1/1/3/2`: the planar Leray projection is bounded on `L^r`

Source: `the November 2 reference manuscript` lines 1670, 1923-1926. For `F ∈ L² ∩ L^r`,
`G_i = f̃_i - Σ_k S_{ik} f̃_k` with `f̃_k = planeComp F k`. Each `S_{ik}` is bounded on `L^r`
(`UnforcedLeray.CZ.lp_bound`, with transpose `S_{ki}`), `‖f̃_k‖_r ≤ ‖F‖_r`, and the Euclidean norm
of a vector is at most the sum of the absolute values of its components.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The Euclidean norm of a planar vector is at most the sum of the norms of its components. -/
theorem rieszGLr_norm_le_sum (v : RMerid) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have h : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [h]
  nlinarith [mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 1))]

/-- `f̃_k` of a field in `L² ∩ L^r`, as an element of `L²(Fin 2 → ℝ)`. -/
def rieszGLr_f {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) : Fin 2 → PlaneL2 :=
  fun k => (planeComp_memLp hF k).toLp _

theorem rieszGLr_f_ae {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) (k : Fin 2) :
    (rieszGLr_f hF k : (Fin 2 → ℝ) → ℝ) =ᵐ[volume] planeComp F k :=
  (planeComp_memLp hF k).coeFn_toLp

/-- The `i`-th component of the Leray projection, transported to `ℝ²`. -/
def rieszGLr_comp (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) (i : Fin 2) : ℝ × ℝ → ℝ :=
  fun z => ((rieszGLr_f hF i - ∑ k, S i k (rieszGLr_f hF k) : PlaneL2) :
    (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z)

theorem rieszGLr_planeRieszG_eq (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) :
    planeRieszG S F = fun z => WithLp.toLp 2 (fun i => rieszGLr_comp S hF i z) := by
  rw [planeRieszG, dif_pos hF]
  rfl

theorem rieszGLr_comp_aesm (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) (i : Fin 2) : AEStronglyMeasurable (rieszGLr_comp S hF i) volume :=
  (Lp.aestronglyMeasurable _).comp_measurePreserving (volume_preserving_finTwoArrow ℝ).symm

theorem rieszGLr_planeComp_eLpNorm {p : ℝ≥0∞} {F : ℝ × ℝ → RMerid} {k : Fin 2}
    (hFk : AEStronglyMeasurable (fun z => F z k) volume) :
    eLpNorm (planeComp F k) p volume = eLpNorm (fun z => F z k) p volume := by
  have e : planeComp F k = (fun z => F z k) ∘ MeasurableEquiv.finTwoArrow := rfl
  rw [e]
  exact eLpNorm_comp_measurePreserving hFk (volume_preserving_finTwoArrow ℝ)

/-- **Leaf `PartII-b:T12/1/1/3/2`**: `‖G‖_r ≤ C ‖F‖_r` and `G ∈ L^r` for `F ∈ L² ∩ L^r`. -/
theorem planeRieszGLr : PlaneRieszGLr := by
  intro S B hS r hr
  have hbd : ∀ i k : Fin 2, ∃ C : ℝ≥0, ∀ f : PlaneL2, MemLp f (ENNReal.ofReal r) volume →
      eLpNorm (S i k f) (ENNReal.ofReal r) volume ≤ C * eLpNorm f (ENNReal.ofReal r) volume :=
    fun i k => UnforcedLeray.CZ.lp_bound (hS.1 i k) (hS.1 k i) (fun f g => hS.2.1 i k f g) hr
  choose C hC using hbd
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le
  refine ⟨((2 + ∑ i, ∑ k, C i k : ℝ≥0) : ℝ), by positivity, fun F hF2 hFr => ?_⟩
  set P : ℝ≥0∞ := ENNReal.ofReal r with hPdef
  have hFm : ∀ k : Fin 2, AEStronglyMeasurable (fun z : ℝ × ℝ => F z k) volume := fun k =>
    ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hF2.1
  have hfP : ∀ k : Fin 2, MemLp (rieszGLr_f hF2 k : (Fin 2 → ℝ) → ℝ) P volume := fun k =>
    MemLp.ae_eq (rieszGLr_f_ae hF2 k).symm (planeComp_memLp hFr k)
  have hfk_le : ∀ k : Fin 2, eLpNorm (rieszGLr_f hF2 k : (Fin 2 → ℝ) → ℝ) P volume ≤
      eLpNorm F P volume := by
    intro k
    rw [eLpNorm_congr_ae (rieszGLr_f_ae hF2 k), rieszGLr_planeComp_eLpNorm (hFm k)]
    exact eLpNorm_mono (fun z => by simpa using PiLp.norm_apply_le (F z) k)
  -- the components on ℝ²
  have hi_bd : ∀ i : Fin 2, eLpNorm (rieszGLr_comp S hF2 i) P volume ≤
      (1 + ∑ k, (C i k : ℝ≥0∞)) * eLpNorm F P volume := by
    intro i
    have hgc : (((rieszGLr_f hF2 i - ∑ k, S i k (rieszGLr_f hF2 k) : PlaneL2) :
        (Fin 2 → ℝ) → ℝ)) =ᵐ[volume] fun x => (rieszGLr_f hF2 i : (Fin 2 → ℝ) → ℝ) x -
          ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (rieszGLr_f hF2 i) (∑ k, S i k (rieszGLr_f hF2 k)),
        Lp.coeFn_fun_finsetSum Finset.univ (fun k => S i k (rieszGLr_f hF2 k))] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
    have e1 : eLpNorm (rieszGLr_comp S hF2 i) P volume = eLpNorm
        (fun x => (rieszGLr_f hF2 i : (Fin 2 → ℝ) → ℝ) x -
          ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) P volume := by
      rw [← eLpNorm_congr_ae hgc]
      exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable _)
        (volume_preserving_finTwoArrow ℝ).symm
    have hsm : AEStronglyMeasurable (fun x => ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x)
        volume := by
      have e : (fun x => ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) =
          ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) := by
        funext x
        simp [Finset.sum_apply]
      rw [e]
      exact Finset.aestronglyMeasurable_sum _ fun k _ => Lp.aestronglyMeasurable _
    have e2 := eLpNorm_sub_le (μ := volume) (p := P) (Lp.aestronglyMeasurable (rieszGLr_f hF2 i))
      hsm hP1
    have e3 : eLpNorm (fun x => ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) P volume ≤
        ∑ k, eLpNorm (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) P volume := by
      have h := eLpNorm_sum_le (μ := volume) (p := P)
        (f := fun k (x : Fin 2 → ℝ) => (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x)
        (s := Finset.univ) (fun k _ => Lp.aestronglyMeasurable _) hP1
      have e : (∑ k : Fin 2, fun x => (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) =
          fun x => ∑ k : Fin 2, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x := by
        funext x
        simp [Finset.sum_apply]
      rw [e] at h
      exact h
    have e4 : ∀ k : Fin 2, eLpNorm (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) P volume ≤
        (C i k : ℝ≥0∞) * eLpNorm F P volume :=
      fun k => (hC i k (rieszGLr_f hF2 k) (hfP k)).trans (mul_le_mul_of_nonneg_left (hfk_le k) (by positivity))
    rw [e1]
    calc eLpNorm (fun x => (rieszGLr_f hF2 i : (Fin 2 → ℝ) → ℝ) x -
          ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) P volume
        ≤ eLpNorm (rieszGLr_f hF2 i : (Fin 2 → ℝ) → ℝ) P volume +
          eLpNorm (fun x => ∑ k, (S i k (rieszGLr_f hF2 k) : (Fin 2 → ℝ) → ℝ) x) P volume := e2
      _ ≤ eLpNorm F P volume + ∑ k, (C i k : ℝ≥0∞) * eLpNorm F P volume :=
          add_le_add (hfk_le i) (e3.trans (Finset.sum_le_sum fun k _ => e4 k))
      _ = (1 + ∑ k, (C i k : ℝ≥0∞)) * eLpNorm F P volume := by
          rw [add_mul, one_mul, Finset.sum_mul]
  -- the vector field
  have hgm : ∀ i : Fin 2, AEStronglyMeasurable (rieszGLr_comp S hF2 i) volume :=
    rieszGLr_comp_aesm S hF2
  have hG_le : eLpNorm (planeRieszG S F) P volume ≤
      ∑ i, eLpNorm (rieszGLr_comp S hF2 i) P volume := by
    have h1 : eLpNorm (planeRieszG S F) P volume ≤
        eLpNorm (fun z => ∑ i, ‖rieszGLr_comp S hF2 i z‖) P volume :=
      eLpNorm_mono_real (fun z => by
        rw [rieszGLr_planeRieszG_eq S hF2]
        exact rieszGLr_norm_le_sum _)
    have h2 : eLpNorm (fun z => ∑ i, ‖rieszGLr_comp S hF2 i z‖) P volume ≤
        ∑ i, eLpNorm (fun z => ‖rieszGLr_comp S hF2 i z‖) P volume := by
      have h := eLpNorm_sum_le (μ := volume) (p := P)
        (f := fun i (z : ℝ × ℝ) => ‖rieszGLr_comp S hF2 i z‖) (s := Finset.univ)
        (fun i _ => (hgm i).norm) hP1
      have e : (∑ i : Fin 2, fun z => ‖rieszGLr_comp S hF2 i z‖) =
          fun z => ∑ i : Fin 2, ‖rieszGLr_comp S hF2 i z‖ := by
        funext z
        simp [Finset.sum_apply]
      rw [e] at h
      exact h
    simp only [eLpNorm_norm] at h2
    exact h1.trans h2
  have hcomb : ∑ i, eLpNorm (rieszGLr_comp S hF2 i) P volume ≤
      ((2 + ∑ i, ∑ k, C i k : ℝ≥0) : ℝ≥0∞) * eLpNorm F P volume := by
    calc ∑ i, eLpNorm (rieszGLr_comp S hF2 i) P volume
        ≤ ∑ i, (1 + ∑ k, (C i k : ℝ≥0∞)) * eLpNorm F P volume :=
          Finset.sum_le_sum fun i _ => hi_bd i
      _ = ((2 + ∑ i, ∑ k, C i k : ℝ≥0) : ℝ≥0∞) * eLpNorm F P volume := by
          rw [← Finset.sum_mul]
          congr 1
          push_cast
          simp only [Fin.sum_univ_two]
          ring
  have hbound : eLpNorm (planeRieszG S F) P volume ≤
      ENNReal.ofReal ((2 + ∑ i, ∑ k, C i k : ℝ≥0) : ℝ) * eLpNorm F P volume := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hG_le.trans hcomb
  have hlt : eLpNorm F P volume < ⊤ := hFr.2
  have hmem : MemLp (planeRieszG S F) P volume := by
    refine memLp_piLp_iff.2 fun i => ⟨?_, ?_⟩
    · rw [rieszGLr_planeRieszG_eq S hF2]
      exact hgm i
    · rw [rieszGLr_planeRieszG_eq S hF2]
      exact lt_of_le_of_lt (hi_bd i) (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 (by simp [ENNReal.sum_ne_top])) hlt)
  exact ⟨hmem, hbound⟩

end UnforcedLeray.Short.IIb
