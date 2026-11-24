import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T05b/2` (leaf): the cell energy of the difference is bounded

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
finite-energy solutions of the train problem). Target: `diffEnergyBound : DiffEnergyBound`
(`Short/PartI/Sub/T05b_2.lean`).

Route. Fix an age `s ∈ [0, S]`, so `s ≥ 0`, and put `w = diffV tr tr' s = tr.v s - tr'.v s`.

1. `w` is continuous on the plane (`smooth_v` restricted to `{s} × ℝ²`, which lies in
   `Ici 0 ×ˢ univ`), so `z ↦ ‖w z‖²` is strongly measurable.
2. Each train has finite cell energy at age `s` (`IsTrain.finite_energy`), and the pointwise bound
   `‖w‖² ≤ 2‖tr.v s‖² + 2‖tr'.v s‖²` (from `‖a - b‖ ≤ ‖a‖ + ‖b‖`) gives integrability of `‖w‖²`
   on the cell by `Integrable.mono'`.
3. `TrainBoundedBy` gives `∫_cell ‖tr.v s‖² ≤ M` and `∫_cell ‖tr'.v s‖² ≤ M`. Integrating the
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
theorem diffEnergy_sq_norm_sub_le (a b : Vec) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-! ### Continuity of a train at a fixed age -/

/-- The velocity of a train is continuous in space at every age `s ≥ 0`. -/
theorem diffEnergy_continuous_v {ν c : ℝ} (t : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (fun z : Plane => t.v s z) := by
  have hcont : ContinuousOn (fun x : ℝ × Plane => t.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    t.isTrain.smooth_v.continuousOn
  have hmap : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    continuous_const.prodMk continuous_id
  exact hcont.comp_continuous hmap (fun z => mk_mem_prod (mem_Ici.2 hs) (mem_univ z))

/-! ### The target -/

/-- **`PartI:T05b/2` leaf, target `DiffEnergyBound`.** For trains bounded by `M` on `[0, S]`, the
difference `diffV tr tr' s` has finite cell energy at every `s ∈ [0, S]`, and that energy is at
most `4M`. -/
theorem diffEnergyBound : DiffEnergyBound := by
  intro ν c _hc tr tr' S M hbt hbt' s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  -- (1) continuity of the two velocities, hence of their difference, at age `s`
  have hv : Continuous (fun z : Plane => tr.v s z) := diffEnergy_continuous_v tr hs0
  have hv' : Continuous (fun z : Plane => tr'.v s z) := diffEnergy_continuous_v tr' hs0
  have hw : Continuous (fun z : Plane => diffV tr tr' s z) := by
    unfold diffV
    exact hv.sub hv'
  -- (2) finite cell energy of each train at age `s`
  have hE : Integrable (fun z : Plane => ‖tr.v s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    tr.isTrain.finite_energy s hs0
  have hE' : Integrable (fun z : Plane => ‖tr'.v s z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    tr'.isTrain.finite_energy s hs0
  -- pointwise: `‖w‖² ≤ 2‖v‖² + 2‖v'‖²`
  have hle : ∀ z : Plane,
      ‖diffV tr tr' s z‖ ^ 2 ≤ 2 * ‖tr.v s z‖ ^ 2 + 2 * ‖tr'.v s z‖ ^ 2 :=
    fun z => diffEnergy_sq_norm_sub_le (tr.v s z) (tr'.v s z)
  have hpt : ∀ z : Plane,
      ‖‖diffV tr tr' s z‖ ^ 2‖ ≤ 2 * ‖tr.v s z‖ ^ 2 + 2 * ‖tr'.v s z‖ ^ 2 := by
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle z
  -- integrability of `‖w‖²` on the cell
  have hsum : Integrable (fun z : Plane => 2 * ‖tr.v s z‖ ^ 2 + 2 * ‖tr'.v s z‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    (hE.const_mul 2).add (hE'.const_mul 2)
  have hi : Integrable (fun z : Plane => ‖diffV tr tr' s z‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    Integrable.mono' hsum (hw.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  -- (3) the integral bound from the two `TrainBoundedBy` energies
  have hM1 : ∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2 ≤ M := (hbt s hs).2.2
  have hM2 : ∫ z in Cyl.cell c, ‖tr'.v s z‖ ^ 2 ≤ M := (hbt' s hs).2.2
  have hmono : ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 ≤
      ∫ z in Cyl.cell c, (2 * ‖tr.v s z‖ ^ 2 + 2 * ‖tr'.v s z‖ ^ 2) :=
    integral_mono hi hsum hle
  have hsplit : ∫ z in Cyl.cell c, (2 * ‖tr.v s z‖ ^ 2 + 2 * ‖tr'.v s z‖ ^ 2)
      = 2 * (∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2) + 2 * (∫ z in Cyl.cell c, ‖tr'.v s z‖ ^ 2) := by
    rw [integral_add (hE.const_mul 2) (hE'.const_mul 2), integral_const_mul, integral_const_mul]
  linarith

end UnforcedLeray.Short.PartI
