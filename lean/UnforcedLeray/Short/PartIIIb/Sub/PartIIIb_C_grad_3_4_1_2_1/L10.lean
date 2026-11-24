import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L3

/-!
# `PartIII-b:C/grad/3/4/1/2/1/10`: the `∂_q` leaf `GDqProp`

Source `the November 2 reference manuscript`
4963-4980, 5063-5079.

Proof.  If `F` is a `GCombo` of `e` at `s`, then `F s` equals `GSum e` as a function of `x`
(`gCombo_self`).  `GSum` is a finite sum of constants times kernel expressions, each of which has
a `∂_q` image given by `gKerDqProp` (leaf of `L3`).  For `e r a b = []` the kernel is `0` and its
image is `[]`; otherwise the image is the chosen `K (e r a b)`.  The `∂_q` of the finite sum is the
sum of the `∂_q` images (`HasFDerivAt.sum`, `HasFDerivAt.const_mul`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gDqProp : GDqProp := by
  unfold GDqProp
  intro L e he
  choose K hK using gKerDqProp
  refine ⟨fun r a b => if e r a b = [] then [] else K (e r a b), ?_, ?_⟩
  · intro r hr a b
    show (if e r a b = [] then [] else K (e r a b)) = []
    rw [he r hr a b, if_pos rfl]
  · intro ν j Ay s F hν hs hF x
    have hF' : F s = GSum e ν j Ay s := funext fun y => gCombo_self hF y
    have hpt : ∀ r a b, fderiv ℝ (gEval (e r a b) ν j s) x (ei 0) =
        gEval (if e r a b = [] then [] else K (e r a b)) ν j s x := by
      intro r a b
      by_cases h : e r a b = []
      · rw [if_pos h, h]
        have hz : gEval [] ν j s = fun _ => (0 : ℝ) := funext fun y => by simp [gEval]
        rw [hz]
        simp
      · rw [if_neg h]
        exact (hK (e r a b) ν j s x hν hs).2
    have hdiff : ∀ r a b, HasFDerivAt (gEval (e r a b) ν j s)
        (fderiv ℝ (gEval (e r a b) ν j s) x) x := by
      intro r a b
      by_cases h : e r a b = []
      · have hz : gEval (e r a b) ν j s = fun _ => (0 : ℝ) := by
          rw [h]
          exact funext fun y => by simp [gEval]
        rw [hz]
        exact hasFDerivAt_const _ _ |>.congr_fderiv (by simp)
      · exact (hK (e r a b) ν j s x hν hs).1.hasFDerivAt
    unfold dQ
    rw [hF']
    have hH : HasFDerivAt (fun y => ∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
        gCoef Ay r s (mi a) (mi b) * gEval (e r a b) ν j s y)
        (∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
          gCoef Ay r s (mi a) (mi b) • fderiv ℝ (gEval (e r a b) ν j s) x) x := by
      apply HasFDerivAt.fun_sum
      intro r _
      apply HasFDerivAt.fun_sum
      intro a _
      apply HasFDerivAt.fun_sum
      intro b _
      exact (hdiff r a b).const_mul (gCoef Ay r s (mi a) (mi b))
    have hG : GSum e ν j Ay s = fun y => ∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
        gCoef Ay r s (mi a) (mi b) * gEval (e r a b) ν j s y := rfl
    rw [hG, hH.fderiv]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hpt]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
