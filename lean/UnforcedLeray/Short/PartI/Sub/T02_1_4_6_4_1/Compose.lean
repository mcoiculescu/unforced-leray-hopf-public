import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6

/-!
# `HeatDivStressIdentity` from the analytic facts, without `RowTensorRegular`

Source: `the November 2 reference manuscript`,
lines 261-288 (the Duhamel term of the mild solution is the heat flow of `div (u ⊗ u)`; the mild
solution lies in `BUC ∩ L²` of the cylinder `(ℝ/cℤ) × ℝ`, lines 271-283).

`RowTensorRegular` (`Sub/PartI_T02_1_4_6_4_1_1_6.lean`) is false (refuted in
`Sub/PartI_T02_1_4_6_4_1_1_6_1.lean`): its `L²` conjunct ignores that the cell `Ioc 0 c ×ˢ univ`
has infinite measure.  Here the `L²` membership of the row tensor `T = w ⊗ w` is obtained from
the `L²` membership of `w` itself, which the hypothesis "the zero-order class of `x` is `w`"
supplies, and the other regularity facts are proved directly, except the derivative bound
`RowTensorFDerivBound`, which is the one new leaf.

`heatDivStressIdentity_of` takes N2-N5 (`StressOrbitIsHeat/Needed.lean`), the kernel-input
identification `KernelInputRowTensor` and the heat identification `HeatVecAdvectionClass`
(`Sub/PartI_T02_1_4_6_4_1_1_6.lean`), and `RowTensorFDerivBound`.
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

/-- **Leaf** (source lines 261-288; product rule for the stress `w ⊗ w`).  For a smooth field `w`
with `‖w‖ ≤ M` and `‖Dw‖ ≤ M'`, the two-row tensor `planeRowTensorValue w w` has bounded
derivative.  (`(w ⊗ w)' = w' ⊗ w + w ⊗ w'`, so `B = 2 M M'` works.) -/
def RowTensorFDerivBound : Prop :=
  ∀ (w : Plane → Vec) (M M' : ℝ), ContDiff ℝ ∞ w → (∀ z, ‖w z‖ ≤ M) →
    (∀ z, ‖fderiv ℝ w z‖ ≤ M') →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (planeRowTensorValue w w) z‖ ≤ B

theorem norm_planeOfVec_le_hdsi (v : Vec) : ‖planeOfVec v‖ ≤ ‖v‖ := by
  rw [planeOfVec, Prod.norm_mk]
  exact max_le (PiLp.norm_apply_le v 0) (PiLp.norm_apply_le v 1)

theorem norm_planeRowTensorValue_le_hdsi (u v : Plane → Vec) (z : Plane) :
    ‖planeRowTensorValue u v z‖ ≤ ‖u z‖ * ‖v z‖ := by
  rw [planeRowTensorValue, Prod.norm_mk]
  refine max_le ?_ ?_
  · rw [norm_smul]
    exact mul_le_mul (PiLp.norm_apply_le _ 0) (norm_planeOfVec_le_hdsi _) (norm_nonneg _)
      (norm_nonneg _)
  · rw [norm_smul]
    exact mul_le_mul (PiLp.norm_apply_le _ 1) (norm_planeOfVec_le_hdsi _) (norm_nonneg _)
      (norm_nonneg _)

theorem contDiff_planeRowTensorValue_hdsi {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (planeRowTensorValue w w) := by
  have h0 : ContDiff ℝ ∞ (fun x => w x 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have h1 : ContDiff ℝ ∞ (fun x => w x 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have hp : ContDiff ℝ ∞ (fun x => planeOfVec (w x)) := h0.prodMk h1
  exact (h0.smul hp).prodMk (h1.smul hp)

theorem isQPeriodic_planeRowTensorValue_hdsi {c : ℝ} {w : Plane → Vec}
    (hper : Cyl.IsPeriodic c w) :
    UnforcedLeray.B0284.IsQPeriodic c (planeRowTensorValue w w) := by
  intro z
  simp only [planeRowTensorValue, hper z]

/-- The stress of a bounded smooth `L²` field is in `L²` of the centered cell. -/
theorem memLp_planeRowTensorValue_cellμ_hdsi {c M : ℝ} {w : Plane → Vec}
    (hw : ContDiff ℝ ∞ w) (hM : ∀ z, ‖w z‖ ≤ M) (hw2 : MemLp w 2 (Cyl.cellμ c)) :
    MemLp (planeRowTensorValue w w) 2 (Cyl.cellμ c) := by
  refine (hw2.const_smul M).of_le
    (contDiff_planeRowTensorValue_hdsi hw).continuous.aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  calc ‖planeRowTensorValue w w z‖ ≤ ‖w z‖ * ‖w z‖ := norm_planeRowTensorValue_le_hdsi w w z
    _ ≤ |M| * ‖w z‖ :=
      mul_le_mul_of_nonneg_right ((hM z).trans (le_abs_self M)) (norm_nonneg _)

/-- **Composition** (source lines 261-288). -/
theorem heatDivStressIdentity_of (n2 : NeedRowDivHeat) (n3 : NeedRowTensorDivergence)
    (n4 : NeedHeatPeriodicL2) (n5 : NeedZeroClassNormalized) (s2 : KernelInputRowTensor)
    (s3 : HeatVecAdvectionClass) (r : RowTensorFDerivBound) : HeatDivStressIdentity := by
  intro c hc hc1 θ hθ x w hw hper hbd hdiv hx G hG
  obtain ⟨M0, hM0⟩ := hbd 0
  obtain ⟨M1, hM1⟩ := hbd 1
  have hw0 : ∀ z, ‖w z‖ ≤ M0 := fun z => by simpa only [norm_iteratedFDeriv_zero] using hM0 z
  have hw1 : ∀ z, ‖fderiv ℝ w z‖ ≤ M1 := fun z => by
    simpa only [norm_iteratedFDeriv_one] using hM1 z
  have hM0nn : 0 ≤ M0 := (norm_nonneg _).trans (hw0 0)
  have hsm := contDiff_planeRowTensorValue_hdsi hw
  have hb0 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖planeRowTensorValue w w x‖ ≤ M :=
    ⟨M0 * M0, mul_nonneg hM0nn hM0nn, fun z => (norm_planeRowTensorValue_le_hdsi w w z).trans
      (mul_le_mul (hw0 z) (hw0 z) (norm_nonneg _) hM0nn)⟩
  have hb1 := r w M0 M1 hw hw0 hw1
  have hqper := isQPeriodic_planeRowTensorValue_hdsi hper
  have hw2 : MemLp w 2 (Cyl.cellμ c) := (Lp.memLp _).ae_eq hx
  have hmem : MemLp (planeRowTensorValue w w) 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_cellMeasure_of_memLp_cyl hc hsm.continuous.measurable hqper
      (memLp_planeRowTensorValue_cellμ_hdsi hw hw0 hw2)
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

/-- The composition `HeatDivStressComposition` of `Sub/PartI_T02_1_4_6_4_1_1_6.lean` without the
refuted `RowTensorRegular`. -/
theorem heatDivStressComposition_of_fderivBound (s2 : KernelInputRowTensor)
    (s3 : HeatVecAdvectionClass) (r : RowTensorFDerivBound) : HeatDivStressComposition :=
  fun _ n2 n3 n4 n5 => heatDivStressIdentity_of n2 n3 n4 n5 s2 s3 r

end UnforcedLeray.Short.PartI
