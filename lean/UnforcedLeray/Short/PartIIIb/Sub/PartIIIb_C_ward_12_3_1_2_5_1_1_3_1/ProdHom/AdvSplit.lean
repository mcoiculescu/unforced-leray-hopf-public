import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.Calc
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# Far product rule, advection part (helper for `ProdHom`)

Source `the November 2 reference manuscript`
lines 2542-2549, 2563-2569: `∂_j (u·∇E) = ∑ₖ (∂_j uₖ) ∂ₖE + ∑ₖ uₖ ∂_j∂ₖE` pointwise, where `u` is
differentiable at the point and `E` is smooth.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

/-- `∂_j` of a `C^∞` field is differentiable everywhere. -/
theorem diff_dy_of_contDiff (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (hE : ContDiff ℝ ∞ E) (k : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    DifferentiableAt ℝ (dy k E) x := by
  have hc : ContDiff ℝ ∞ (dy k E) := by
    unfold dy
    exact (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hc.differentiable (by simp)) x

/-- Pointwise `∂_j` of a finite sum, when each summand is differentiable at the point. -/
theorem dy_finset_sum_pt {ι : Type} (s : Finset ι)
    (A : ι → ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (x : ℝ × UnforcedLeray.Space) (j : Fin 3)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) x) :
    dy j (fun z => ∑ i ∈ s, A i z) x = ∑ i ∈ s, dy j (A i) x := by
  simp only [dy]
  rw [fderiv_fun_sum h]
  simp

/-- The advection term: `∂_j (u·∇E)` at a point. -/
theorem dy_advT_pt (j : Fin 3)
    (u E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (x : ℝ × UnforcedLeray.Space)
    (hu : ∀ k : Fin 3, DifferentiableAt ℝ (fun z => u z k) x)
    (hE : ContDiff ℝ ∞ E) :
    dy j (UnforcedLeray.Cons.C03.Concrete.advT u E) x =
      ∑ k : Fin 3, u x k • dy j (dy k E) x +
        ∑ k : Fin 3, dy j (fun z => u z k) x • dy k E x := by
  have hfun : UnforcedLeray.Cons.C03.Concrete.advT u E =
      fun z => ∑ k : Fin 3, u z k • dy k E z := rfl
  rw [hfun, dy_finset_sum_pt Finset.univ
    (fun k z => u z k • dy k E z) x j
    (fun k _ => (hu k).smul (diff_dy_of_contDiff E hE k x))]
  have key : ∀ k : Fin 3, dy j (fun z => u z k • dy k E z) x =
      u x k • dy j (dy k E) x + dy j (fun z => u z k) x • dy k E x := fun k =>
    dy_cmul_pt j (fun z => u z k) (dy k E) x (hu k) (diff_dy_of_contDiff E hE k x)
  simp only [key]
  rw [Finset.sum_add_distrib]

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
