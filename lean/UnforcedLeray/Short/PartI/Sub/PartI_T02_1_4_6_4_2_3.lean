import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/3` (`LeafShiftLapCH`), decomposition

Source of record: `the November 2 reference manuscript` (centered heat semigroup,
age derivative of the shift pairing).

`leafShiftLapCH_of` proves `LeafShiftLapCH` from three leaves:
* `LeafShiftRepCH`: the shift pairing is the literal cell integral `∫_cell ⟪ψ(z - v), G z⟫`
  (library: `HeatCylinder.inner_planeShiftL2_smooth_eq_integral`; the translation is by `z - v`);
* `LeafParamIntCH`: that parameter integral is `C^∞` with bounded derivatives up to order two, and
  its planar Laplacian is the integral against `Δψ` (differentiation under the integral);
* `LeafLapCellTestCH`: `Δψ` is again a cell test.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **Leaf (representation)**: for a cell test `ψ` with `L²` class `ψL`, the shift pairing equals
the literal cell integral. -/
def LeafShiftRepCH : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (ψ : Plane → Vec) (ψL G : Cyl.L2v c),
    IsCellTest c ψ → ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ →
    ∀ v : Plane, shiftPairCH hc ψL G v =
      ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)

/-- **Leaf (parameter integral)**: `v ↦ ∫_cell ⟪ψ(z - v), G z⟫` is `C^∞` with bounded
derivatives up to order two, with Laplacian `∫_cell ⟪(Δψ)(z - w), G z⟫`. -/
def LeafParamIntCH : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (ψ : Plane → Vec) (G : Cyl.L2v c), IsCellTest c ψ →
    ContDiff ℝ ∞ (fun v : Plane => ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)) ∧
    (∃ M : ℝ, ∀ x, ‖∫ z in Cyl.cell c, inner ℝ (ψ (z - x)) (((G : Cyl.L2v c) : Plane → Vec) z)‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun v : Plane =>
      ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (fun v : Plane =>
      ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)) y (1, 0)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (fun v : Plane =>
      ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)) y (0, 1)) x‖ ≤ M) ∧
    ∀ w : Plane, Train.lapS (fun v : Plane =>
        ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)) w =
      ∫ z in Cyl.cell c, inner ℝ (Train.vecLaplacian ψ (z - w)) (((G : Cyl.L2v c) : Plane → Vec) z)

/-- **Leaf**: the vector Laplacian of a cell test is a cell test. -/
def LeafLapCellTestCH : Prop :=
  ∀ (c : ℝ) (ψ : Plane → Vec), IsCellTest c ψ → IsCellTest c (Train.vecLaplacian ψ)

theorem leafShiftLapCH_of (h1 : LeafShiftRepCH) (h2 : LeafParamIntCH)
    (h3 : LeafLapCellTestCH) : LeafShiftLapCH := by
  intro c hc ψ ψL ψ'L G hψ hψL hψ'L
  have hfun : shiftPairCH hc ψL G = fun v : Plane =>
      ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z) :=
    funext (h1 c hc ψ ψL G hψ hψL)
  obtain ⟨a, b, d, e, f, g⟩ := h2 c hc ψ G hψ
  rw [hfun]
  refine ⟨a, b, d, e, f, fun w => ?_⟩
  rw [g w]
  exact (h1 c hc (Train.vecLaplacian ψ) ψ'L G (h3 c ψ hψ) hψ'L w).symm
