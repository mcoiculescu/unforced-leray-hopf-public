import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.AdjointFormula
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.ComplexAdjointOp.Operator
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.ComplexAdjointOp.Algebra

/-!
# Part II-a, task `PartII-a:F02/8`: the complex adjoint as a bounded operator

Source of record: `the November 2 reference manuscript`, lines 1363-1370.
Proves the Prop `ComplexAdjointOp` of `Sub/F02.lean`. The operator is
`A = B0421.cx (adjSemigroupLp)` (`Operator.lean`); the duality is the real adjoint formula
`AdjointFormula` (`AdjointFormula.lean`) applied to the four real pieces of the bilinear pairing
(`Algebra.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open ComplexAdjointOpAux

/-- The real and imaginary parts of a complex field, as a decomposition at each point. -/
theorem ae_decomp_cvec {r : ℝ≥0∞} [Fact (1 ≤ r)] (h : Lp CVec3 r (volume : Measure Space)) :
    ∀ᵐ y ∂(volume : Measure Space), (h : Space → CVec3) y =
      ofReV ((reV.compLpL r volume h : SpatialField) y) +
        ofImV ((imV.compLpL r volume h : SpatialField) y) := by
  filter_upwards [reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := r) h,
    imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := r) h] with y e1 e2
  rw [e1, e2, ofReV_reV_add_ofImV_imV]

/-- The coefficient formula of the complexified adjoint operator. -/
theorem coeFn_cx_adjSemigroup {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ⊤) (ν s : ℝ)
    (g : Lp CVec3 r (volume : Measure Space)) :
    (B0421.cx (adjSemigroupLp hr ν s) g : Space → CVec3) =ᵐ[volume] fun y =>
      ofReV (adjFree ν s (reV.compLpL r volume g : SpatialField) y) +
        ofImV (adjFree ν s (imV.compLpL r volume g : SpatialField) y) := by
  rw [B0421.cx_apply]
  filter_upwards [Lp.coeFn_add
      (ofReV.compLpL r volume (adjSemigroupLp hr ν s (reV.compLpL r volume g)))
      (ofImV.compLpL r volume (adjSemigroupLp hr ν s (imV.compLpL r volume g))),
    ofReV.coeFn_compLpL (μ := (volume : Measure Space)) (p := r)
      (adjSemigroupLp hr ν s (reV.compLpL r volume g)),
    ofImV.coeFn_compLpL (μ := (volume : Measure Space)) (p := r)
      (adjSemigroupLp hr ν s (imV.compLpL r volume g)),
    coeFn_adjSemigroupLp hr ν s (reV.compLpL r volume g),
    coeFn_adjSemigroupLp hr ν s (imV.compLpL r volume g)] with y h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, h4, h5]

/-- **The complex adjoint as a bounded operator** (task `PartII-a:F02/8`): the Prop
`ComplexAdjointOp`. -/
theorem complexAdjointOp : UnforcedLeray.Short.PartIIa.ComplexAdjointOp := by
  unfold UnforcedLeray.Short.PartIIa.ComplexAdjointOp
  intro q _ hq hq1 ν s hν hs
  have hp' : conjExp q ≠ ⊤ := conjExp_ne_top hq1
  refine ⟨B0421.cx (adjSemigroupLp hp' ν s), ?_, ?_⟩
  · intro g h
    rw [innerPair_apply, innerPair_apply]
    have L : ∫ y, dotL ((B0421.cx (adjSemigroupLp hp' ν s) g) y) (h y) =
        ∫ y, dotL (ofReV (adjFree ν s (reV.compLpL (conjExp q) volume g : SpatialField) y) +
          ofImV (adjFree ν s (imV.compLpL (conjExp q) volume g : SpatialField) y))
          (ofReV ((reV.compLpL q volume h : SpatialField) y) +
            ofImV ((imV.compLpL q volume h : SpatialField) y)) := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_cx_adjSemigroup hp' ν s g, ae_decomp_cvec h] with y e1 e2
      rw [e1, e2]
    have R : ∫ y, dotL (g y) ((B0421.freeC hq ν s h) y) =
        ∫ y, dotL (ofReV ((reV.compLpL (conjExp q) volume g : SpatialField) y) +
          ofImV ((imV.compLpL (conjExp q) volume g : SpatialField) y))
          (ofReV (AncientLocalization.freeEvolution ν s
              (reV.compLpL q volume h : SpatialField) y) +
            ofImV (AncientLocalization.freeEvolution ν s
              (imV.compLpL q volume h : SpatialField) y)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_decomp_cvec g, B0421.coeFn_freeC hq ν s h] with y e1 e2
      rw [e1, e2]
    rw [L, R]
    have hG1 : MemLp (reV.compLpL (conjExp q) volume g : SpatialField) (conjExp q) volume :=
      Lp.memLp _
    have hG2 : MemLp (imV.compLpL (conjExp q) volume g : SpatialField) (conjExp q) volume :=
      Lp.memLp _
    have hH1 : MemLp (reV.compLpL q volume h : SpatialField) q volume := Lp.memLp _
    have hH2 : MemLp (imV.compLpL q volume h : SpatialField) q volume := Lp.memLp _
    have hSH1 : MemLp (AncientLocalization.freeEvolution ν s
        (reV.compLpL q volume h : SpatialField)) q volume :=
      B0418.freeEvolution_memLp Fact.out hq hH1 ν s
    have hSH2 : MemLp (AncientLocalization.freeEvolution ν s
        (imV.compLpL q volume h : SpatialField)) q volume :=
      B0418.freeEvolution_memLp Fact.out hq hH2 ν s
    have hAG1 := adjFree_memLp Fact.out hp' hG1 ν s
    have hAG2 := adjFree_memLp Fact.out hp' hG2 ν s
    have e11 := (adjointFormula ν s hν hs (conjExp q) q hp' hq
      (reV.compLpL (conjExp q) volume g : SpatialField) (reV.compLpL q volume h : SpatialField)
      hG1 hH1).symm
    have e22 := (adjointFormula ν s hν hs (conjExp q) q hp' hq
      (imV.compLpL (conjExp q) volume g : SpatialField) (imV.compLpL q volume h : SpatialField)
      hG2 hH2).symm
    have e12 := (adjointFormula ν s hν hs (conjExp q) q hp' hq
      (reV.compLpL (conjExp q) volume g : SpatialField) (imV.compLpL q volume h : SpatialField)
      hG1 hH2).symm
    have e21 := (adjointFormula ν s hν hs (conjExp q) q hp' hq
      (imV.compLpL (conjExp q) volume g : SpatialField) (reV.compLpL q volume h : SpatialField)
      hG2 hH1).symm
    rw [integral_dotL_split (adjFree ν s (reV.compLpL (conjExp q) volume g : SpatialField))
      (adjFree ν s (imV.compLpL (conjExp q) volume g : SpatialField))
      (reV.compLpL q volume h : SpatialField) (imV.compLpL q volume h : SpatialField)
      (ComplexAdjointOpAux.integrable_inner_of_memLp hAG1 hH1) (ComplexAdjointOpAux.integrable_inner_of_memLp hAG2 hH2)
      (ComplexAdjointOpAux.integrable_inner_of_memLp hAG1 hH2) (ComplexAdjointOpAux.integrable_inner_of_memLp hAG2 hH1),
      integral_dotL_split (reV.compLpL (conjExp q) volume g : SpatialField)
      (imV.compLpL (conjExp q) volume g : SpatialField)
      (AncientLocalization.freeEvolution ν s (reV.compLpL q volume h : SpatialField))
      (AncientLocalization.freeEvolution ν s (imV.compLpL q volume h : SpatialField))
      (ComplexAdjointOpAux.integrable_inner_of_memLp hG1 hSH1) (ComplexAdjointOpAux.integrable_inner_of_memLp hG2 hSH2)
      (ComplexAdjointOpAux.integrable_inner_of_memLp hG1 hSH2) (ComplexAdjointOpAux.integrable_inner_of_memLp hG2 hSH1)]
    rw [e11, e22, e12, e21]
  · intro g v hgv
    have hR : (reV.compLpL (conjExp q) volume g : SpatialField) =ᵐ[volume]
        fun z => reV (v z) := by
      filter_upwards [reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := conjExp q) g,
        hgv] with z h1 h2
      rw [h1, h2]
    have hI : (imV.compLpL (conjExp q) volume g : SpatialField) =ᵐ[volume]
        fun z => imV (v z) := by
      filter_upwards [imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := conjExp q) g,
        hgv] with z h1 h2
      rw [h1, h2]
    filter_upwards [coeFn_cx_adjSemigroup hp' ν s g, adjFree_congr_ae hR ν s,
      adjFree_congr_ae hI ν s] with y h1 h2 h3
    rw [h1, h2, h3]
    rfl

end UnforcedLeray.Short.PartIIa
