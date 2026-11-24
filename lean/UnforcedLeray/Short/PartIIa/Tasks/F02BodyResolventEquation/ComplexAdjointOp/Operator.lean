import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/8` helper: the real adjoint semigroup as an operator on `L^p`

Source of record: `the November 2 reference manuscript`, lines 1363-1370.
Builds `adjSemigroupLp hp ν s : L^p(ℝ³) →L[ℝ] L^p(ℝ³)` from the pointwise formula `adjFree`
(`Sub/F02.lean`), exactly as `B0418.freeSemigroupLp` is built from `freeEvolution`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.ComplexAdjointOpAux

open UnforcedLeray.AncientLocalization UnforcedLeray.B0418

variable {p : ℝ≥0∞}

theorem adjFree_memLp (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u : SpatialField} (hu : MemLp u p volume)
    (ν s : ℝ) : MemLp (adjFree ν s u) p volume :=
  SpatialScaling.memLp_spatialScale (flow_memLp hp1 hp hu _) _ (Real.exp_pos _).ne'

theorem adjFree_congr_ae {u v : SpatialField} (h : u =ᵐ[volume] v) (ν s : ℝ) :
    adjFree ν s u =ᵐ[volume] adjFree ν s v :=
  SpatialScaling.ae_eq_spatialScale (flow_congr_ae h _) _ (Real.exp_pos _).ne'

theorem adjFree_sub (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u v : SpatialField}
    (hu : MemLp u p volume) (hv : MemLp v p volume) (ν s : ℝ) :
    adjFree ν s (u - v) = adjFree ν s u - adjFree ν s v := by
  unfold adjFree SpatialScaling.spatialScale
  rw [flow_sub hp1 hp hu hv]
  funext x
  simp only [Pi.sub_apply, smul_sub]

theorem adjFree_smul (c : ℝ) (ν s : ℝ) (u : SpatialField) :
    adjFree ν s (c • u) = c • adjFree ν s u := by
  unfold adjFree SpatialScaling.spatialScale
  rw [flow_smul]
  funext x
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

theorem adjFree_add (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u v : SpatialField}
    (hu : MemLp u p volume) (hv : MemLp v p volume) (ν s : ℝ) :
    adjFree ν s (u + v) = adjFree ν s u + adjFree ν s v := by
  have h1 := adjFree_sub hp1 hp (hu.add hv) hv ν s
  rw [add_sub_cancel_right] at h1
  rw [h1, sub_add_cancel]

/-- The constant `‖e^{-s}‖ · (e^{3s/2})^{1/p}` of the transport bound. -/
def adjConst (p : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ‖Real.exp (-s)‖ₑ * (ENNReal.ofReal |((Real.exp (-s / 2)) ^ 3)⁻¹|) ^ (1 / p).toReal

theorem adjConst_ne_top (p : ℝ≥0∞) (s : ℝ) : adjConst p s ≠ ⊤ :=
  ENNReal.mul_ne_top (enorm_ne_top) (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    ENNReal.ofReal_ne_top)

theorem eLpNorm_adjFree_le (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u : SpatialField}
    (hu : MemLp u p volume) (ν s : ℝ) :
    eLpNorm (adjFree ν s u) p volume ≤ adjConst p s * eLpNorm u p volume := by
  unfold adjFree
  rw [eLpNorm_spatialScale_Lp hp _ (Real.exp_pos _ |>.ne')]
  unfold adjConst
  rw [← mul_assoc]
  gcongr
  exact eLpNorm_flow_le hp1 hp hu _

/-- The real adjoint semigroup on `L^p(ℝ³; ℝ³)`, `1 ≤ p < ∞`. -/
def adjSemigroupLp [Fact (1 ≤ p)] (hp : p ≠ ∞) (ν s : ℝ) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := fun u => (adjFree_memLp Fact.out hp (Lp.memLp u) ν s).toLp _
      map_add' := by
        intro u v
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have h := adjFree_congr_ae (Lp.coeFn_add u v) ν s
        rwa [adjFree_add Fact.out hp (Lp.memLp u) (Lp.memLp v)] at h
      map_smul' := by
        intro c u
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        have h := adjFree_congr_ae (Lp.coeFn_smul c u) ν s
        rwa [adjFree_smul] at h }
    (adjConst p s).toReal
    (by
      intro u
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have hle := eLpNorm_adjFree_le Fact.out hp (Lp.memLp u) ν s
      calc (eLpNorm (adjFree ν s u) p volume).toReal
          ≤ (adjConst p s * eLpNorm u p volume).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top (adjConst_ne_top p s)
              (Lp.memLp u).2.ne) hle
        _ = (adjConst p s).toReal * (eLpNorm u p volume).toReal := ENNReal.toReal_mul)

theorem adjSemigroupLp_apply [Fact (1 ≤ p)] (hp : p ≠ ∞) (ν s : ℝ)
    (u : Lp Space p (volume : Measure Space)) :
    adjSemigroupLp hp ν s u =
      (adjFree_memLp Fact.out hp (Lp.memLp u) ν s).toLp (adjFree ν s u) := rfl

/-- The class `S'_ν(s)u` is represented by the pointwise formula `adjFree`. -/
theorem coeFn_adjSemigroupLp [Fact (1 ≤ p)] (hp : p ≠ ∞) (ν s : ℝ)
    (u : Lp Space p (volume : Measure Space)) :
    (adjSemigroupLp hp ν s u : SpatialField) =ᵐ[volume] adjFree ν s u := by
  rw [adjSemigroupLp_apply]
  exact MemLp.coeFn_toLp (adjFree_memLp Fact.out hp (Lp.memLp u) ν s)

end UnforcedLeray.Short.PartIIa.ComplexAdjointOpAux
