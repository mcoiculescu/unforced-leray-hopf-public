import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Circulation

/-!
# Multipliers bounded on the physical cell

The train curl is periodic in the horizontal coordinate, so its radially weighted size must only
be bounded on the centered cell. This constructs the corresponding continuous multiplier on the
actual weighted pivot without imposing an impossible global radial bound.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579

/-- The product with a cell-bounded continuous multiplier remains in the weighted pivot. -/
theorem memLp_mulR_cell {c m : ℝ} {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ cell c, |r x| ≤ C) (f : X c m) :
    MemLp (fun x => r x * f x) 2 (cellMeasure c m) := by
  refine ((Lp.memLp f).const_mul C).of_le
    (hr.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    ((cellMeasure_ac c m).ae_le
      (ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)))

/-- Multiplication by a continuous scalar coefficient bounded on the centered cell. -/
def mulRCell (c m : ℝ) (r : Plane → ℝ) (hr : Continuous r) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ cell c, |r x| ≤ C) : X c m →L[ℝ] X c m := by
  let L : X c m →ₗ[ℝ] X c m := {
    toFun := fun f => (memLp_mulR_cell hr hC hbound f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound (f + g)),
        Lp.coeFn_add ((memLp_mulR_cell hr hC hbound f).toLp _)
          ((memLp_mulR_cell hr hC hbound g).toLp _),
        MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound f),
        MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound g), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
      rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      ring
    map_smul' := by
      intro a f
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound (a • f)),
        Lp.coeFn_smul a ((memLp_mulR_cell hr hC hbound f).toLp _),
        MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound f), Lp.coeFn_smul a f] with x h1 h2 h3 h4
      rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul]
      ring
  }
  refine L.mkContinuous C ?_
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound f),
    (cellMeasure_ac c m).ae_le
      (ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => hbound x hx)] with x hcoe hx
  change ‖((memLp_mulR_cell hr hC hbound f).toLp _ : Plane → ℝ) x‖ ≤ C * ‖f x‖
  rw [hcoe, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- Application norm bound for the actual centered-cell multiplier. -/
theorem norm_mulRCell_le {c m : ℝ} {r : Plane → ℝ} (hr : Continuous r) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ cell c, |r x| ≤ C) (f : X c m) :
    ‖mulRCell c m r hr hC hbound f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_mulR_cell hr hC hbound f),
    (cellMeasure_ac c m).ae_le
      (ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => hbound x hx)] with x hcoe hx
  change ‖((memLp_mulR_cell hr hC hbound f).toLp _ : Plane → ℝ) x‖ ≤ C * ‖f x‖
  rw [hcoe, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
