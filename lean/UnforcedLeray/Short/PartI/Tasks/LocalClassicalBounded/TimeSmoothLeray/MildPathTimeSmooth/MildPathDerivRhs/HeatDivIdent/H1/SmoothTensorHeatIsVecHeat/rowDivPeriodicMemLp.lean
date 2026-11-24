import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2
import UnforcedLeray.Lib.HeatCylinder.WeakOutput

/-!
# `rowDivPeriodicMemLp`: the row divergence of a smooth cylinder tensor is periodic and `L²`

Proves `RowDivPeriodicMemLp` (defined in `PartI_T02_1_4_4_1_5_1_1_2.lean`, source
`the November 2 reference manuscript` lines 3594-3625). The row divergence is
expressed through the classical iterated derivatives `iterD [e₁] S` and `iterD [e₂] S`, whose
normalized `L²` membership is `HeatCylinder.memLp_tensor_iterD_cylSmooth_normalized`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

theorem rowDivPeriodicMemLp : RowDivPeriodicMemLp := by
  intro c hc S hS
  have hdiff : ∀ z : Plane, HasFDerivAt S (fderiv ℝ S z) z := fun z =>
    ((hS.smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have a11 : ∀ z v, fderiv ℝ (fun x => (S x).1.1) z v = (fderiv ℝ S z v).1.1 := fun z v => by
    rw [((hdiff z).fst.fst).fderiv]; rfl
  have a21 : ∀ z v, fderiv ℝ (fun x => (S x).2.1) z v = (fderiv ℝ S z v).2.1 := fun z v => by
    rw [((hdiff z).snd.fst).fderiv]; rfl
  have a12 : ∀ z v, fderiv ℝ (fun x => (S x).1.2) z v = (fderiv ℝ S z v).1.2 := fun z v => by
    rw [((hdiff z).fst.snd).fderiv]; rfl
  have a22 : ∀ z v, fderiv ℝ (fun x => (S x).2.2) z v = (fderiv ℝ S z v).2.2 := fun z v => by
    rw [((hdiff z).snd.snd).fderiv]; rfl
  have hrow : ∀ z : Plane, rowDivergence S z =
      ((UnforcedLeray.Sob.iterD [((1 : ℝ), (0 : ℝ))] S z).1.1 +
          (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ))] S z).2.1,
        (UnforcedLeray.Sob.iterD [((1 : ℝ), (0 : ℝ))] S z).1.2 +
          (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ))] S z).2.2) := fun z => by
    simp only [rowDivergence, a11, a21, a12, a22]
    rfl
  have hper : ∀ v : Plane, ∀ z : Plane,
      UnforcedLeray.Sob.iterD [v] S (z + (c, 0)) = UnforcedLeray.Sob.iterD [v] S z :=
    fun v => (hS.iterD [v]).periodic
  have hcont : Continuous (rowDivergence S) := by
    have h1 := (hS.iterD [((1 : ℝ), (0 : ℝ))]).smooth.continuous
    have h2 := (hS.iterD [((0 : ℝ), (1 : ℝ))]).smooth.continuous
    have e : rowDivergence S = fun z => ((UnforcedLeray.Sob.iterD [((1 : ℝ), (0 : ℝ))] S z).1.1 +
          (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ))] S z).2.1,
        (UnforcedLeray.Sob.iterD [((1 : ℝ), (0 : ℝ))] S z).1.2 +
          (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ))] S z).2.2) := funext hrow
    rw [e]
    exact Continuous.prodMk (Continuous.add h1.fst.fst h2.snd.fst)
      (Continuous.add h1.fst.snd h2.snd.snd)
  have hQ : UnforcedLeray.B0284.IsQPeriodic c (rowDivergence S) := by
    intro z
    have hcoord : ((z.1 + c, z.2) : Plane) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    simp only [hrow, hper]
  have hM1 := UnforcedLeray.HeatCylinder.memLp_tensor_iterD_cylSmooth_normalized hc hS
    [((1 : ℝ), (0 : ℝ))]
  have hM2 := UnforcedLeray.HeatCylinder.memLp_tensor_iterD_cylSmooth_normalized hc hS
    [((0 : ℝ), (1 : ℝ))]
  have hMem : MemLp (rowDivergence S) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    refine memLp_prod_iff.2 ⟨?_, ?_⟩
    · exact ((hM1.fst.fst.add hM2.snd.fst).ae_eq (Eventually.of_forall fun z => by
        simp only [Pi.add_apply, hrow z]))
    · exact ((hM1.fst.snd.add hM2.snd.snd).ae_eq (Eventually.of_forall fun z => by
        simp only [Pi.add_apply, hrow z]))
  refine ⟨hQ, hcont, ?_⟩
  exact hMem.continuousLinearMap_comp (UnforcedLeray.Train.toVecL.toContinuousLinearMap)

end UnforcedLeray.Short.PartI
