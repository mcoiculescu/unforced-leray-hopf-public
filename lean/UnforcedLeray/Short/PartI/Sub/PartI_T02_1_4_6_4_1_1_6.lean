import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1

/-!
# `heatDivStressComposition` from three bridge facts

Source: `the November 2 reference manuscript`,
lines 261-288 (the Duhamel term of the mild solution is the heat flow of `div (u ⊗ u)`).

The composition `N1-N5 → HeatDivStressIdentity` is reduced to three bridge statements
(regularity of the row tensor, identification of the kernel input, identification of the heat of
the advection class).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Sub1** (source lines 261-288): for a smooth periodic field `w` with bounded derivatives that
lies in `L²` of the normalized cell (the mild solution is in `BUC ∩ L²` of the cylinder, lines
278-283), the two-row tensor `planeRowTensorValue w w` is smooth, bounded with bounded derivative,
`Q`-periodic and in `L²` of the normalized cell.  (Product rule; `fderiv_mul_apply_plane` in
`RowTensorDivergence.lean`; `‖w ⊗ w‖ ≤ M ‖w‖`.)  The cell `Ioc 0 c ×ˢ univ` has infinite measure,
so the `L²` hypothesis on `w` is needed: without it the statement fails for constant `w`. -/
def RowTensorRegular : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (w : Plane → Vec), ContDiff ℝ ∞ w → Cyl.IsPeriodic c w →
    (∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ M) →
    MemLp w 2 (UnforcedLeray.B0284.cellMeasure c) →
    ContDiff ℝ ∞ (planeRowTensorValue w w) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖planeRowTensorValue w w x‖ ≤ M) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (planeRowTensorValue w w) x‖ ≤ M) ∧
    UnforcedLeray.B0284.IsQPeriodic c (planeRowTensorValue w w) ∧
    MemLp (planeRowTensorValue w w) 2 (UnforcedLeray.B0284.cellMeasure c)

/-- **Sub2** (source lines 261-288): the kernel input `tensorH3KernelInput` of `x ⊗ x` is the
`L²` class of the row tensor `planeRowTensorValue w w` when the zero-order class of `x` is `w`.
Route: `tensorH3Bilinear_planeValue_ae`, `W.value x = vecH3CellDerivCLM zero x` a.e., and the a.e.
identification of `tensorH3KernelInput` with `tensorToPlaneCLE ∘ W.value` (the body of
`tensorH3KernelInput_coe_ae_ofCylSmooth`, `Lib/HeatCylinder/H3ActualLimit.lean:560`, whose private
helper `ae_tensorH3ValueRep_cell` must be made available or reproved). -/
def KernelInputRowTensor : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (x : VectorH3 c) (w : Plane → Vec),
    ContDiff ℝ ∞ w → Cyl.IsPeriodic c w →
    (∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ M) →
    ((vecH3CellDerivCLM Sob.Idx.zero x : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] w →
    ∀ hmem : MemLp (planeRowTensorValue w w) 2 (UnforcedLeray.B0284.cellMeasure c),
      tensorH3KernelInput hc (tensorH3Bilinear hc1 x x) = hmem.toLp (planeRowTensorValue w w)

/-- **Sub3** (source lines 261-288): the normalized vector heat of the transported advection class
`G` is the `L²` class of `toVec (heat θ (rowDivergence T))`, `T = planeRowTensorValue w w`.
Uses N3 (`rowDivergence T = advection w`), the a.e. transport
`centeredVecToNormalizedCLM hc G = advection w` and `heat` commuting with the coordinate map
`toVec` (integral linearity against `heatKernel2`), together with N4. -/
def HeatVecAdvectionClass : Prop :=
  NeedHeatPeriodicL2 → NeedRowTensorDivergence →
  ∀ (c : ℝ) (hc : 0 < c) (θ : ℝ) (hθ : 0 < θ) (w : Plane → Vec), ContDiff ℝ ∞ w →
    Cyl.IsPeriodic c w → (∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ M) →
    (∀ z, Cyl.divergence w z = 0) →
    ∀ G : Cyl.L2v c, ((G : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.advection w →
    ∀ hm : MemLp (fun z => toVec (UnforcedLeray.B0284.heat θ
        (rowDivergence (planeRowTensorValue w w)) z)) 2 (UnforcedLeray.B0284.cellMeasure c),
      heatVecL2CLM hc θ (centeredVecToNormalizedCLM hc G) =
        hm.toLp (fun z => toVec (UnforcedLeray.B0284.heat θ
          (rowDivergence (planeRowTensorValue w w)) z))

theorem heatDivStressComposition_of (s1 : RowTensorRegular) (s2 : KernelInputRowTensor)
    (s3 : HeatVecAdvectionClass) : HeatDivStressComposition := by
  intro n1 n2 n3 n4 n5 c hc hc1 θ hθ x w hw hper hbd hdiv hx G hG
  have hwcyl : MemLp w 2 (Cyl.cellμ c) := (Lp.memLp _).ae_eq hx
  have hwcell : MemLp w 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_cellMeasure_of_memLp_cyl hc hw.continuous.measurable hper hwcyl
  obtain ⟨hsm, hb0, hb1, hqper, hmem⟩ := s1 c hc w hw hper hbd hwcell
  have hmeas : AEStronglyMeasurable (planeRowTensorValue w w) volume :=
    hsm.continuous.aestronglyMeasurable
  have hK := s2 c hc hc1 x w hw hper hbd hx hmem
  have hpt : ∀ z, toVec (UnforcedLeray.B0296.heatDiv θ (planeRowTensorValue w w) z) =
      toVec (UnforcedLeray.B0284.heat θ (rowDivergence (planeRowTensorValue w w)) z) := by
    intro z
    rw [n2 hθ _ hsm hb0 hb1 z]
  have hmemV := periodicHeatDivVecMemLp hc hθ (planeRowTensorValue w w) hqper hmeas hmem
  have hmemV' : MemLp (fun z => toVec (UnforcedLeray.B0284.heat θ
      (rowDivergence (planeRowTensorValue w w)) z)) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    have : (fun z => toVec (UnforcedLeray.B0284.heat θ
      (rowDivergence (planeRowTensorValue w w)) z)) =
      (fun z => toVec (UnforcedLeray.B0296.heatDiv θ (planeRowTensorValue w w) z)) :=
      funext fun z => (hpt z).symm
    rw [this]; exact hmemV
  have h3 := s3 n4 n3 c hc θ hθ w hw hper hbd hdiv G hG hmemV'
  have hL : vectorH3NormalizedValue hc (actualHeatDivH3 hc hθ (tensorH3Bilinear hc1 x x)) =
      heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (tensorH3Bilinear hc1 x x)) := by
    rw [vectorH3NormalizedValue_actualHeatDivH3]
    rfl
  rw [n5 hc, hL, hK, heatDivVecL2CLM_apply_to_periodic hc hθ hqper hmeas hmem]
  change _ = normalizedVecToCenteredCLM hc
    (heatVecL2CLM hc θ (centeredVecToNormalizedCLM hc G))
  rw [h3]
  congr 1
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun z => hpt z))

end UnforcedLeray.Short.PartI
