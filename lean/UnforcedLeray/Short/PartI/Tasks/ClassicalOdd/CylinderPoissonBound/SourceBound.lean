import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/SourceBound`: the Poisson source bound (source part of `CylinderPoissonBound`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (bounded
periodic pressure) and line 447 (the Poisson source `tr((grad v)^2)`).

Target: `CylPoisSourceBound` (`Short/PartI/Sub/T02_3_8.lean`): if `‖D u z‖ ≤ B` for every `z`, then the
Poisson source `∂_i u_j ∂_j u_i = (∂_q u_0)² + 2 ∂_q u_1 ∂_η u_0 + (∂_η u_1)²` (`poissonSource`,
`Short/PartI/Sub/T02_3.lean`) satisfies `|poissonSource u z| ≤ 4 B²`.

Proof.  Each of the four partial derivatives is a coordinate of `fderiv ℝ u z` applied to the unit
vector `(1,0)` or `(0,1)`.  A coordinate is bounded by the norm of the vector, which is bounded by
`‖fderiv ℝ u z‖ · ‖v‖ ≤ B`.  The bound `4 B²` then follows from `a² + 2 b c + d²` with
`|a|, |b|, |c|, |d| ≤ B`.

All auxiliary names start with `cpS` (the final file imports every leaf file).
-/

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- A coordinate of `fderiv ℝ u z v` is bounded by `B` when `‖fderiv ℝ u z‖ ≤ B` and `‖v‖ ≤ 1`. -/
theorem cpS_coord_le {B : ℝ} {u : Plane → Vec} {z v : Plane} (hB : ‖fderiv ℝ u z‖ ≤ B)
    (hv : ‖v‖ ≤ 1) (i : Fin 2) : |fderiv ℝ u z v i| ≤ B := by
  have h1 : ‖fderiv ℝ u z v‖ ≤ ‖fderiv ℝ u z‖ * ‖v‖ := (fderiv ℝ u z).le_opNorm v
  have h2 : ‖fderiv ℝ u z v i‖ ≤ ‖fderiv ℝ u z v‖ := PiLp.norm_apply_le _ i
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  calc |fderiv ℝ u z v i| = ‖fderiv ℝ u z v i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ u z v‖ := h2
    _ ≤ ‖fderiv ℝ u z‖ * ‖v‖ := h1
    _ ≤ B * 1 := mul_le_mul hB hv (norm_nonneg _) hB0
    _ = B := mul_one B

/-- The unit vector `(1,0)` of the plane has norm at most `1`. -/
theorem cpS_norm_e0 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
  simp [Prod.norm_def]

/-- The unit vector `(0,1)` of the plane has norm at most `1`. -/
theorem cpS_norm_e1 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
  simp [Prod.norm_def]

/-- The `q`-partial of the `i`-th component is the `i`-th coordinate of `fderiv ℝ u z (1,0)`. -/
theorem cpS_partialQ_coord {u : Plane → Vec} (hu : Differentiable ℝ u) (i : Fin 2) (z : Plane) :
    UnforcedLeray.Cyl.partialQ (fun w => u w i) z = fderiv ℝ u z (1, 0) i := by
  have hc : Differentiable ℝ (fun w => u w i) := UnforcedLeray.Cyl.differentiable_component hu i
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hc z]
  have hf : HasFDerivAt (fun w => u w i)
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ u z)) z :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hu z).hasFDerivAt
  rw [hf.fderiv]
  rfl

/-- The `η`-partial of the `i`-th component is the `i`-th coordinate of `fderiv ℝ u z (0,1)`. -/
theorem cpS_partialEta_coord {u : Plane → Vec} (hu : Differentiable ℝ u) (i : Fin 2) (z : Plane) :
    UnforcedLeray.Cyl.partialEta (fun w => u w i) z = fderiv ℝ u z (0, 1) i := by
  have hc : Differentiable ℝ (fun w => u w i) := UnforcedLeray.Cyl.differentiable_component hu i
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hc z]
  have hf : HasFDerivAt (fun w => u w i)
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ u z)) z :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hu z).hasFDerivAt
  rw [hf.fderiv]
  rfl

/-- Algebra: `|a² + 2 b c + d²| ≤ 4 B²` when `|a|, |b|, |c|, |d| ≤ B` (and `0 ≤ B`). -/
theorem cpS_quad_bound {B a b c d : ℝ} (hB0 : 0 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hc : |c| ≤ B) (hd : |d| ≤ B) : |a ^ 2 + 2 * (b * c) + d ^ 2| ≤ 4 * B ^ 2 := by
  have ha2 : a ^ 2 ≤ B ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg a) ha 2
    rwa [sq_abs] at h
  have hd2 : d ^ 2 ≤ B ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg d) hd 2
    rwa [sq_abs] at h
  have hbc : |b * c| ≤ B ^ 2 := by
    rw [abs_mul]
    calc |b| * |c| ≤ B * B := mul_le_mul hb hc (abs_nonneg _) hB0
      _ = B ^ 2 := by ring
  have hbc' := abs_le.mp hbc
  have hsq : 0 ≤ B ^ 2 := sq_nonneg B
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg a, sq_nonneg d, hbc'.1]
  · nlinarith [hbc'.2]

/-- **Source bound** (`CylPoisSourceBound`): `|∂_i u_j ∂_j u_i| ≤ 4 B²` when `‖D u‖ ≤ B`. -/
theorem cylPoisSourceBound : CylPoisSourceBound := by
  unfold CylPoisSourceBound
  intro B u hu hB z
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hB' : ‖fderiv ℝ u z‖ ≤ B := by
    have h := hB z
    rwa [norm_iteratedFDeriv_one] at h
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB'
  have ha : |UnforcedLeray.Cyl.partialQ (fun w => u w 0) z| ≤ B := by
    rw [cpS_partialQ_coord hd 0 z]
    exact cpS_coord_le hB' cpS_norm_e0 0
  have hb : |UnforcedLeray.Cyl.partialQ (fun w => u w 1) z| ≤ B := by
    rw [cpS_partialQ_coord hd 1 z]
    exact cpS_coord_le hB' cpS_norm_e0 1
  have hc : |UnforcedLeray.Cyl.partialEta (fun w => u w 0) z| ≤ B := by
    rw [cpS_partialEta_coord hd 0 z]
    exact cpS_coord_le hB' cpS_norm_e1 0
  have he : |UnforcedLeray.Cyl.partialEta (fun w => u w 1) z| ≤ B := by
    rw [cpS_partialEta_coord hd 1 z]
    exact cpS_coord_le hB' cpS_norm_e1 1
  have key := cpS_quad_bound hB0 ha hb hc he
  unfold poissonSource
  exact key

end UnforcedLeray.Short.PartI
