import UnforcedLeray.Short.PartIIb.Sub.T12_1_1_3
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Leaf `PartII-b:T12/1/1/3/1`: the planar Leray projection is an `L²` contraction

Source: `the November 2 reference manuscript` lines 1670, 1923-1926. With
`f_k = planeComp F k` in `L²(Fin 2 → ℝ)`, the components of `planeRieszG S F` are
`g_i = f_i - Σ_k S_{ik} f_k`; the `L²` norm of a vector field is the square root of the sum of the
squared component norms, and the contraction clause of `IsPlaneRieszFamily` gives
`Σ_i ‖g_i‖² ≤ Σ_i ‖f_i‖²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Pointwise Pythagoras in `ℝ²` (Euclidean norm). -/
theorem rieszGL2_enorm_sq_eq_sum (v : RMerid) : ‖v‖ₑ ^ 2 = ∑ i, ‖v i‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- The square of the `L²` norm of a vector field is the sum of the squared norms of its
components. -/
theorem rieszGL2_eLpNorm_sq_eq_sum {G : ℝ × ℝ → RMerid}
    (hG : ∀ i : Fin 2, AEStronglyMeasurable (fun z => G z i) volume) :
    eLpNorm G 2 volume ^ 2 = ∑ i, eLpNorm (fun z => G z i) 2 volume ^ 2 := by
  have key : ∀ {E : Type} [NormedAddCommGroup E] (f : ℝ × ℝ → E),
      eLpNorm f 2 volume ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 := by
    intro E _ f
    have h1 := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure (ℝ × ℝ))) (f := f)
      (p := 2) two_ne_zero
    have e2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by simp
    have e3 : ((2 : ℝ≥0) : ℝ) = 2 := by simp
    rw [e2, e3] at h1
    simp only [ENNReal.rpow_two] at h1
    exact h1
  rw [key G]
  simp only [key]
  simp_rw [rieszGL2_enorm_sq_eq_sum]
  rw [lintegral_finset_sum']
  exact fun i _ => (hG i).enorm.pow_const 2

theorem planeRieszGL2_comp_eLpNorm {F : ℝ × ℝ → RMerid} {k : Fin 2}
    (hFk : AEStronglyMeasurable (fun z => F z k) volume) :
    eLpNorm (planeComp F k) 2 volume = eLpNorm (fun z => F z k) 2 volume :=
  by
  have e : planeComp F k = (fun z => F z k) ∘ MeasurableEquiv.finTwoArrow := rfl
  rw [e]
  exact eLpNorm_comp_measurePreserving hFk (volume_preserving_finTwoArrow ℝ)

/-- **Leaf `PartII-b:T12/1/1/3/1`**: `G ∈ L²`, `‖G‖₂ ≤ ‖F‖₂`. -/
theorem planeRieszGL2 : PlaneRieszGL2 := by
  intro S B hS F hF
  have hFm : ∀ k : Fin 2, AEStronglyMeasurable (fun z : ℝ × ℝ => F z k) volume := fun k =>
    ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hF.1
  set f : Fin 2 → PlaneL2 := fun k => (planeComp_memLp hF k).toLp _ with hf
  have hGeq : planeRieszG S F = fun z => WithLp.toLp 2 (fun i =>
      ((f i - ∑ k, S i k (f k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z)) := by
    rw [planeRieszG, dif_pos hF]
  have hgm : ∀ i : Fin 2, AEStronglyMeasurable (fun z =>
      ((f i - ∑ k, S i k (f k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z))
      volume :=
    fun i => (Lp.aestronglyMeasurable _).comp_measurePreserving
      (volume_preserving_finTwoArrow ℝ).symm
  have hcomp : ∀ i : Fin 2, AEStronglyMeasurable (fun z => planeRieszG S F z i) volume := by
    intro i
    rw [hGeq]
    exact hgm i
  -- norms of the components
  have hG2 : eLpNorm (planeRieszG S F) 2 volume ^ 2 = ∑ i, ‖f i - ∑ k, S i k (f k)‖ₑ ^ 2 := by
    rw [rieszGL2_eLpNorm_sq_eq_sum hcomp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : eLpNorm (fun z => planeRieszG S F z i) 2 volume =
        eLpNorm ((f i - ∑ k, S i k (f k) : PlaneL2) : (Fin 2 → ℝ) → ℝ) 2 volume := by
      rw [hGeq]
      exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable _)
        (volume_preserving_finTwoArrow ℝ).symm
    rw [h1, ← Lp.enorm_def]
  have hF2 : eLpNorm F 2 volume ^ 2 = ∑ k, ‖f k‖ₑ ^ 2 := by
    rw [rieszGL2_eLpNorm_sq_eq_sum hFm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Lp.enorm_def, eLpNorm_congr_ae (planeComp_memLp hF k).coeFn_toLp,
      planeRieszGL2_comp_eLpNorm (hFm k)]
  have hsq : ∀ x : PlaneL2, ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hineq : ∑ i, ‖f i - ∑ k, S i k (f k)‖ₑ ^ 2 ≤ ∑ i, ‖f i‖ₑ ^ 2 := by
    simp only [hsq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hS.2.2.1 f)
  have hle : eLpNorm (planeRieszG S F) 2 volume ^ 2 ≤ eLpNorm F 2 volume ^ 2 := by
    rw [hG2, hF2]
    exact hineq
  have hle' : eLpNorm (planeRieszG S F) 2 volume ≤ eLpNorm F 2 volume :=
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  have hmem : MemLp (planeRieszG S F) 2 volume := by
    refine memLp_piLp_iff.2 fun i => ?_
    rw [hGeq]
    exact (Lp.memLp _).comp_measurePreserving (volume_preserving_finTwoArrow ℝ).symm
  exact ⟨hmem, hle'⟩

end UnforcedLeray.Short.IIb
