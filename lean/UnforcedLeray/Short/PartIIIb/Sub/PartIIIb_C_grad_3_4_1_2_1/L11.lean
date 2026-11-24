import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L4
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# `PartIII-b:C/grad/3/4/1/2/1/11`: the `∂_η` leaf `GDetaProp`

Source `the November 2 reference manuscript`
4963-4980 (`ψ^p_A`), 5063-5079 (termwise Gaussian bounds).

Proof.  `GCombo` gives `F s = GSum e ν j Ay s` as functions of `y`, so `dEta F s` is the
`η`-derivative of the finite sum `GSum e ν j Ay s`.  Each term is `gCoef · gEval (e r a b)`,
and `gKerDetaProp`'s kernel leaf (`detaMon`, file `L4`) differentiates `gEval` in `η`
termwise.  The new coefficients are `e' r a b = (e r a b).flatMap detaMon`, which keeps the
level: `e r a b = []` implies `e' r a b = []`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `η`-derivative of a `GSum`, computed termwise via `detaMon`. -/
lemma gDeta_GSum_hasDerivAt (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ)
    (Ay : ℝ → Mat3) (s : ℝ) (x1 x2 : ℝ) :
    HasDerivAt (fun η => GSum e ν j Ay s (x1, η))
      (GSum (fun r a b => (e r a b).flatMap detaMon) ν j Ay s (x1, x2)) x2 := by
  unfold GSum
  apply HasDerivAt.fun_sum
  intro r _
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  exact (kE_list_hasDerivAt ν j s x1 (e r a b) x2).const_mul _

/-- A `GSum` is differentiable in `x`. -/
lemma gDeta_GSum_diffAt (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ)
    (Ay : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (GSum e ν j Ay s) x := by
  unfold GSum
  apply DifferentiableAt.fun_sum
  intro r _
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (kD_gEval_diffAt ν j s (e r a b) x).const_mul _

theorem gDetaProp : GDetaProp := by
  unfold GDetaProp
  intro L e hL
  unfold GLevel at hL
  refine ⟨fun r a b => (e r a b).flatMap detaMon, ?_, ?_⟩
  · unfold GLevel
    intro r hr a b
    simp [hL r hr a b]
  · intro ν j Ay s F _ _ hF x
    obtain ⟨x1, x2⟩ := x
    have hFs : F s = GSum e ν j Ay s := funext fun y => gCombo_self hF y
    have h1 : dEta F s (x1, x2) = deriv (fun η => GSum e ν j Ay s (x1, η)) x2 := by
      unfold dEta
      rw [hFs]
      exact kE_fderiv_ei1 _ x1 x2 (gDeta_GSum_diffAt e ν j Ay s (x1, x2))
    rw [h1, (gDeta_GSum_hasDerivAt e ν j Ay s x1 x2).deriv]

end UnforcedLeray.Short.PartIIIb.Concrete
