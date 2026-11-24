import UnforcedLeray.Short.PartI.Sub.T02_3_11

/-!
# Part I, task `PartI:T02/3/11` (leaf): the cell energy of the difference is bounded

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
finite-energy solutions of the classical problem). Target: `ccDiffEnergyBound : CcDiffEnergyBound`
(`Short/PartI/Sub/T02_3_11.lean`, auxiliary statement at line 158). Template: the proved train
analogue `diffEnergyBound` in `Tasks/TrainCutoffEnergyProof/DiffEnergy.lean`.

Route. Fix `s ∈ [0, T]` and put `w = ccDiffV v v' s = v s - v' s`.

1. The slices `v s`, `v' s` are `C^∞` by the hypothesis `hS : CcSliceSmooth`, hence continuous.
   So `w` is continuous, and `z ↦ ‖w z‖²` is strongly measurable.
2. Each solution has finite cell energy at age `s` (`IsClassicalOn.finite_energy`). The pointwise
   bound `‖w‖² ≤ 2‖v s‖² + 2‖v' s‖²` (`ccDE_sq_norm_sub_le`) gives integrability of `‖w‖²` on the
   cell by `Integrable.mono'`.
3. `ClassicalBoundedBy` gives `∫_cell ‖v s‖² ≤ M` and `∫_cell ‖v' s‖² ≤ M`. Integrating the
   pointwise bound (`integral_mono`, `integral_add`, `integral_const_mul`) gives
   `∫_cell ‖w‖² ≤ 2M + 2M = 4M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Elementary inequality -/

/-- `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem ccDE_sq_norm_sub_le (a b : Vec) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-! ### The target -/

/-- **`PartI:T02/3/11` leaf, target `CcDiffEnergyBound`.** For two classical solutions bounded by
`M` on `[0, T]`, the difference `ccDiffV v v' s` has finite cell energy at every `s ∈ [0, T]`, and
that energy is at most `4M`. -/
theorem ccDiffEnergyBound (hS : CcSliceSmooth) : CcDiffEnergyBound := by
  intro ν c T M v v' p p' h s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  -- (1) continuity of the two slices, hence of their difference, at age `s`
  have hv := (hS ν c T v p h.cl s hs).1
  have hv' := (hS ν c T v' p' h.cl' s hs).1
  have hcont : Continuous (ccDiffV v v' s) := by
    unfold ccDiffV
    exact hv.continuous.sub hv'.continuous
  -- (2) finite cell energy of each solution at age `s`
  have hE : Integrable (fun z : Plane => ‖v s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    h.cl.finite_energy s hs
  have hE' : Integrable (fun z : Plane => ‖v' s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    h.cl'.finite_energy s hs
  -- pointwise: `‖w‖² ≤ 2‖v‖² + 2‖v'‖²`
  have hle : ∀ z : Plane, ‖ccDiffV v v' s z‖ ^ 2 ≤ 2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2 := by
    intro z
    unfold ccDiffV
    exact ccDE_sq_norm_sub_le (v s z) (v' s z)
  have hpt : ∀ z : Plane,
      ‖‖ccDiffV v v' s z‖ ^ 2‖ ≤ 2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2 := by
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle z
  -- integrability of the dominating function and of `‖w‖²` on the cell
  have hsum : Integrable (fun z : Plane => 2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    (hE.const_mul 2).add (hE'.const_mul 2)
  have hi : Integrable (fun z : Plane => ‖ccDiffV v v' s z‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    Integrable.mono' hsum (hcont.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  -- (3) the integral bound from the two `ClassicalBoundedBy` energies
  have hM1 : ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 ≤ M := (h.bb s hs).2.2
  have hM2 : ∫ z in Cyl.cell c, ‖v' s z‖ ^ 2 ≤ M := (h.bb' s hs).2.2
  have hmono : ∫ z in Cyl.cell c, ‖ccDiffV v v' s z‖ ^ 2 ≤
      ∫ z in Cyl.cell c, (2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2) :=
    integral_mono hi hsum hle
  have hsplit : ∫ z in Cyl.cell c, (2 * ‖v s z‖ ^ 2 + 2 * ‖v' s z‖ ^ 2)
      = 2 * (∫ z in Cyl.cell c, ‖v s z‖ ^ 2) + 2 * (∫ z in Cyl.cell c, ‖v' s z‖ ^ 2) := by
    rw [integral_add (hE.const_mul 2) (hE'.const_mul 2), integral_const_mul, integral_const_mul]
  linarith

end UnforcedLeray.Short.PartI
