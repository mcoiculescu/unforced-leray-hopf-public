import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4

/-!
# Statements still needed by `stressOrbitIsHeat` (typecheck probe)

Every declaration here is a `def` of a `Prop` (or an auxiliary `def`), not a theorem, so this
file carries no proof obligation. It only checks that the sub-statements of the reduction of

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

/-- Row divergence of a two-row tensor field `T = (T.1, T.2)` (rows indexed by the derivative
direction): `(div T)^l = ∂_q T.1^l + ∂_η T.2^l`. -/
def rowDivergence (T : Plane → Plane × Plane) (z : Plane) : Plane :=
  (fderiv ℝ (fun x => (T x).1.1) z (1, 0) + fderiv ℝ (fun x => (T x).2.1) z (0, 1),
    fderiv ℝ (fun x => (T x).1.2) z (1, 0) + fderiv ℝ (fun x => (T x).2.2) z (0, 1))

/-- **N1** (smooth Gaussian integration by parts for one scalar pair). The library lemma
`UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv` takes `ContDiff ℝ ⊤`
(analytic), so it does not apply to the smooth fields `w s`; the smooth version must be proved. -/
def NeedSmoothRowIBP : Prop :=
  ∀ {θ : ℝ}, 0 < θ → ∀ {f g : Plane → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ g x‖ ≤ M) →
    ∀ z : Plane,
      ∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * f (z - w) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * g (z - w) =
        ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
          (fderiv ℝ f (z - w) (1, 0) + fderiv ℝ g (z - w) (0, 1))

/-- **N2** (heat of the divergence, for a smooth bounded two-row tensor). Two applications of
N1, one per output coordinate. -/
def NeedRowDivHeat : Prop :=
  ∀ {θ : ℝ}, 0 < θ → ∀ T : Plane → Plane × Plane, ContDiff ℝ ∞ T →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖T x‖ ≤ M) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ T x‖ ≤ M) →
    ∀ z : Plane,
      UnforcedLeray.B0296.heatDiv θ T z =
        UnforcedLeray.B0284.heat θ (rowDivergence T) z

/-- **N3** (pointwise divergence of the stress `w ⊗ w` is the advection, when `div w = 0`).
Calculus: `∂_q(w₀²) + ∂_η(w₁ w₀) = (w·∇)w₀ + w₀ div w`, and similarly in the second
component. -/
def NeedRowTensorDivergence : Prop :=
  ∀ w : Plane → Vec, ContDiff ℝ ∞ w → (∀ z, Cyl.divergence w z = 0) → ∀ z : Plane,
    toVec (rowDivergence (planeRowTensorValue w w) z) = Train.advection w z

/-- **N4** (periodic heat on the normalized cell, scalar Plane carrier). The analogue of
`UnforcedLeray.HeatCylinder.heatDivL2CLM_apply_to_periodic`
(`Lib/HeatCylinder/H3ActualLimit.lean:474`) without the divergence. Not in the library. -/
def NeedHeatPeriodicL2 : Prop :=
  ∀ {c : ℝ} (hc : 0 < c) (θ : ℝ) (T : Plane → Plane),
    UnforcedLeray.B0284.IsQPeriodic c T → AEStronglyMeasurable T volume →
    ∀ hmem : MemLp T 2 (UnforcedLeray.B0284.cellMeasure c),
      ∃ hh : MemLp (UnforcedLeray.B0284.heat θ T) 2 (UnforcedLeray.B0284.cellMeasure c),
        UnforcedLeray.HeatCylinder.heatL2CLM hc θ (hmem.toLp T) =
          hh.toLp (UnforcedLeray.B0284.heat θ T)

/-- **N5** (zero-order centered class of the H³ value equals the normalized class, transported
back by the centered/normalized inverse). Needed to pass from `vecH3CellDerivCLM` to the
normalized `vectorH3NormalizedValue`, where `actualHeatDivH3`'s L² value is stated. -/
def NeedZeroClassNormalized : Prop :=
  ∀ {c : ℝ} (hc : 0 < c) (y : UnforcedLeray.TrainB.VectorH3 c),
    UnforcedLeray.TrainB.vecH3CellDerivCLM UnforcedLeray.Sob.Idx.zero y =
      UnforcedLeray.HeatCylinder.normalizedVecToCenteredCLM hc
        (UnforcedLeray.HeatCylinder.vectorH3NormalizedValue hc y)

/-- **N6** (positive-age reduction of the stress orbit; the bookkeeping that `compactMildStressOrbit`
uses `actualHeatDivH3CLM` at positive age and `compactMildStressPath` at `r ∈ [0,T]`). Proof:
`dif_pos`, `actualHeatDivH3CLM_apply`, and `extendCompactPath_apply_of_mem`. -/
def NeedStressPathAtAge : Prop :=
  ∀ {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 ≤ T) (hν : 0 < ν)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (t r : ℝ) (hr : r ∈ Icc (0 : ℝ) T)
    (ht : 0 < t - r),
    compactMildStressOrbit (ν := ν) hc hc1 hT u t r =
      vecH3CellDerivCLM Sob.Idx.zero
        (actualHeatDivH3 hc (mul_pos hν ht) (tensorH3Bilinear hc1 (u ⟨r, hr⟩) (u ⟨r, hr⟩)))

end UnforcedLeray.Short.PartI
