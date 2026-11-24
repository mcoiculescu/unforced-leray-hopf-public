import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.SourceBound

/-!
# Part I, task `PartI:T02/3/11`, leaf `CcStretchPointwise`

Source of record: `the November 2 reference manuscript`, lines 276-288 (the stretching
term `(w·∇)v'` is bounded by the sup of `∇v'`; this is the one place where the classical class uses
`HasBoundedDerivsOn` at order `1`).

Target: `ccStretchPointwise (hS : CcSliceSmooth) : CcStretchPointwise`
(`CcStretchPointwise` is defined in `Short/PartI/Sub/T02_3_11.lean`).

Proof.  Let `B` bound `‖D v'(s) z‖` (order `1` of `HasBoundedDerivsOn T v'`), and take
`K = 4 max(B, 0)`.  For a field `a` and `b = v'(s)`, each component of `(a·∇)b` at `z` is
`a_0 ∂_q b_i + a_1 ∂_η b_i`, and each of the four partials is a coordinate of `Db(z)` on a unit
vector, hence at most `B` in absolute value (`cpS_coord_le`).  Since `|a_j| ≤ ‖a‖`, each component is at
most `2 B ‖a‖`.  The norm of a vector in `ℝ²` is at most the sum of the absolute values of its
coordinates, which gives `‖(a·∇)b‖ ≤ 4 B ‖a‖`.

All auxiliary names start with `ccSP`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The norm of a vector of `ℝ²` is at most the sum of the absolute values of its coordinates. -/
theorem ccSP_norm_le_abs_add (x : Vec) : ‖x‖ ≤ |x 0| + |x 1| := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

/-- The transport `(a·∇)b` of a vector field `b` by `a`, bounded by `4 B ‖a(z)‖` whenever
`‖D b(z)‖ ≤ B`, `B ≥ 0`. -/
theorem ccSP_bilin_bound {B' : ℝ} {a b : Plane → Vec} {z : Plane}
    (hd : Differentiable ℝ b) (hB : ‖fderiv ℝ b z‖ ≤ B') :
    ‖bilinAdv a b z‖ ≤ 4 * B' * ‖a z‖ := by
  have hq0 : |UnforcedLeray.Cyl.partialQ (fun w => b w 0) z| ≤ B' := by
    rw [cpS_partialQ_coord hd 0 z]
    exact cpS_coord_le hB cpS_norm_e0 0
  have hq1 : |UnforcedLeray.Cyl.partialQ (fun w => b w 1) z| ≤ B' := by
    rw [cpS_partialQ_coord hd 1 z]
    exact cpS_coord_le hB cpS_norm_e0 1
  have he0 : |UnforcedLeray.Cyl.partialEta (fun w => b w 0) z| ≤ B' := by
    rw [cpS_partialEta_coord hd 0 z]
    exact cpS_coord_le hB cpS_norm_e1 0
  have he1 : |UnforcedLeray.Cyl.partialEta (fun w => b w 1) z| ≤ B' := by
    rw [cpS_partialEta_coord hd 1 z]
    exact cpS_coord_le hB cpS_norm_e1 1
  have ha0 : |a z 0| ≤ ‖a z‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (a z) 0
  have ha1 : |a z 1| ≤ ‖a z‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (a z) 1
  have hN : 0 ≤ ‖a z‖ := norm_nonneg _
  have hX : |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 0) z +
      a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 0) z| ≤ 2 * B' * ‖a z‖ := by
    calc |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 0) z +
          a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 0) z|
        ≤ |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 0) z| +
          |a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 0) z| := abs_add_le _ _
      _ = |a z 0| * |UnforcedLeray.Cyl.partialQ (fun w => b w 0) z| +
          |a z 1| * |UnforcedLeray.Cyl.partialEta (fun w => b w 0) z| := by
          rw [abs_mul, abs_mul]
      _ ≤ ‖a z‖ * B' + ‖a z‖ * B' :=
          add_le_add (mul_le_mul ha0 hq0 (abs_nonneg _) hN)
            (mul_le_mul ha1 he0 (abs_nonneg _) hN)
      _ = 2 * B' * ‖a z‖ := by ring
  have hY : |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 1) z +
      a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 1) z| ≤ 2 * B' * ‖a z‖ := by
    calc |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 1) z +
          a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 1) z|
        ≤ |a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 1) z| +
          |a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 1) z| := abs_add_le _ _
      _ = |a z 0| * |UnforcedLeray.Cyl.partialQ (fun w => b w 1) z| +
          |a z 1| * |UnforcedLeray.Cyl.partialEta (fun w => b w 1) z| := by
          rw [abs_mul, abs_mul]
      _ ≤ ‖a z‖ * B' + ‖a z‖ * B' :=
          add_le_add (mul_le_mul ha0 hq1 (abs_nonneg _) hN)
            (mul_le_mul ha1 he1 (abs_nonneg _) hN)
      _ = 2 * B' * ‖a z‖ := by ring
  have hbil0 : bilinAdv a b z 0 = a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 0) z +
      a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 0) z := rfl
  have hbil1 : bilinAdv a b z 1 = a z 0 * UnforcedLeray.Cyl.partialQ (fun w => b w 1) z +
      a z 1 * UnforcedLeray.Cyl.partialEta (fun w => b w 1) z := rfl
  have h0 : |bilinAdv a b z 0| ≤ 2 * B' * ‖a z‖ := by
    rw [hbil0]
    exact hX
  have h1 : |bilinAdv a b z 1| ≤ 2 * B' * ‖a z‖ := by
    rw [hbil1]
    exact hY
  have hnorm := ccSP_norm_le_abs_add (bilinAdv a b z)
  linarith [hnorm, h0, h1]

/-- **Leaf `CcStretchPointwise`** (`ccStretchPointwise`): the stretching field of a classical pair
satisfies `‖(w·∇)v'‖ ≤ K ‖w‖` on `[0, T] × ℝ²` with `K = 4 max(B, 0)`, where `B` bounds the first
derivatives of the slices of `v'`.  The slices are `C^∞` by `hS`, so `Db` exists at each point. -/
theorem ccStretchPointwise (hS : CcSliceSmooth) : CcStretchPointwise := by
  unfold CcStretchPointwise
  intro ν c T M v v' p p' h
  obtain ⟨B, hB⟩ := h.bd' 1
  refine ⟨4 * max B 0, mul_nonneg (by norm_num) (le_max_right B 0), ?_⟩
  intro s hs z
  have hd : Differentiable ℝ (v' s) :=
    ((hS ν c T v' p' h.cl' s hs).1).differentiable (by simp)
  have hB' : ‖fderiv ℝ (v' s) z‖ ≤ max B 0 := by
    have h1 := hB s hs z
    rw [norm_iteratedFDeriv_one] at h1
    exact le_trans h1 (le_max_left _ _)
  exact ccSP_bilin_bound (B' := max B 0) hd hB'

end UnforcedLeray.Short.PartI
