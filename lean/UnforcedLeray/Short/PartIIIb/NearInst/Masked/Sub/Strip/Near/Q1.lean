import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2

/-!
# `PartIII-b:C/near/masked/22/2/1`: the pointwise bound `‖fullOut g x‖ₑ ≤ (√s)⁻¹ |W|₂` (source 4000)

`fullOut = (√s)⁻¹ • merRe(-sepW …)`. The meridional real part of a complex vector is bounded in
Euclidean norm by the full vector, `|Re w_i| ≤ ‖w_i‖`, and `‖-w‖ = ‖w‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem q1_merRe_neg_norm_le (w : Fin 3 → ℂ) :
    ‖merRe (-w)‖ ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ := by
  have key : ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [mul_self_nonneg z.im]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [merRe, Fin.sum_univ_three, Fin.sum_univ_two, PiLp.toLp_apply, Pi.neg_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs,
    Complex.neg_re]
  have h0 := key (w 0)
  have h2 := key (w 2)
  have h1 : 0 ≤ ‖w 1‖ ^ 2 := sq_nonneg _
  nlinarith [h0, h2, h1]

theorem q1_enorm_le_ofReal (v : Merid) (r : ℝ) (h : ‖v‖ ≤ r) : ‖v‖ₑ ≤ ENNReal.ofReal r := by
  have h1 : ‖v‖ₑ = ENNReal.ofReal ‖v‖ := by
    exact (ofReal_norm v).symm
  rw [h1]
  exact ENNReal.ofReal_le_ofReal h

theorem nearPointwise_holds : NearPointwise := by
  intro R c ν μ g x
  unfold fullOut nearEN
  have hs : 0 ≤ (Real.sqrt x.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [enorm_smul, Real.enorm_eq_ofReal hs]
  gcongr
  exact q1_enorm_le_ofReal _ _ (q1_merRe_neg_norm_le _)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
