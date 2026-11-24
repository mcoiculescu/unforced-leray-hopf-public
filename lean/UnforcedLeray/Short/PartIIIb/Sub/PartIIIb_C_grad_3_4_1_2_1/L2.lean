import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L1
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `PartIII-b:C/grad/3/4/1/2/1/2`: the bound of a `GSum` (leaf `GBoundProp`)

Source `the November 2 reference manuscript`
4963-4980 (`ψ^p_A`), 5063-5079 (termwise Gaussian bounds).

Proof.  Each coefficient `gCoef (Ay ν χf A) r s (mi a) (mi b)` is an entry of `A^y`,
`s∂_sA^y` or `(s∂_s)²A^y`, hence bounded by the Frobenius norm of that matrix, which is a
summand of `gradF`.  Each kernel expression is bounded by `gDomProp` times `latticeW`, which is
`gradW` by definition.  The constant is the sum of the twelve kernel constants.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A matrix entry is bounded by the Frobenius norm. -/
lemma entry_le_frob_gb (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  have h1 : M i j ^ 2 ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, M i' j' ^ 2 := by
    calc M i j ^ 2 ≤ ∑ j' : Fin 3, M i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' : Fin 3 => M i j' ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, M i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j' : Fin 3, M i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  unfold frob
  calc |M i j| = Real.sqrt (M i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i' : Fin 3, ∑ j' : Fin 3, M i' j' ^ 2) := Real.sqrt_le_sqrt h1

/-- The Frobenius norm is nonnegative. -/
lemma frob_nonneg_gb (M : Mat3) : 0 ≤ frob M := by
  unfold frob; positivity

/-- Each coefficient of a `GSum` is bounded by `gradF`. -/
lemma gb_coef_le (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (r : Fin 3) (a b : Fin 2) :
    |gCoef (Ay ν χf A) r s (mi a) (mi b)| ≤ gradF ν χf A s := by
  have h0 := frob_nonneg_gb (Ay ν χf A s)
  have h1 := frob_nonneg_gb (sDeriv (Ay ν χf A) s)
  have h2 := frob_nonneg_gb (sDeriv (sDeriv (Ay ν χf A)) s)
  have e0 : gCoef (Ay ν χf A) 0 s = Ay ν χf A s := rfl
  have e1 : gCoef (Ay ν χf A) 1 s = sDeriv (Ay ν χf A) s := rfl
  have e2 : gCoef (Ay ν χf A) 2 s = sDeriv (sDeriv (Ay ν χf A)) s := rfl
  unfold gradF
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
  · rw [e0]; exact (entry_le_frob_gb _ (mi a) (mi b)).trans (by linarith)
  · rw [e1]; exact (entry_le_frob_gb _ (mi a) (mi b)).trans (by linarith)
  · rw [e2]; exact (entry_le_frob_gb _ (mi a) (mi b)).trans (by linarith)

theorem gBoundProp : GBoundProp := by
  have hD := gDomProp
  unfold GDomProp at hD
  choose Cf hCf0 hCf using hD
  unfold GBoundProp
  intro e
  refine ⟨∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2, Cf (e r a b), ?_, ?_⟩
  · exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hCf0 (e r a b)
  · intro ν χf A j s x hν hν1 hs hνs
    have hG := gradF_nonneg ν χf A s
    have key : ∀ (r : Fin 3) (a b : Fin 2),
        |gCoef (Ay ν χf A) r s (mi a) (mi b) * gEval (e r a b) ν j s x| ≤
          gradF ν χf A s * (Cf (e r a b) * gradW ν x j) := by
      intro r a b
      rw [abs_mul]
      exact mul_le_mul (gb_coef_le ν χf A s r a b)
        (hCf (e r a b) ν j s x hν hν1 hs hνs) (abs_nonneg _) hG
    have hsum : |GSum e ν j (Ay ν χf A) s x| ≤ ∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
        gradF ν χf A s * (Cf (e r a b) * gradW ν x j) := by
      unfold GSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact key r a b
    refine hsum.trans (le_of_eq ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
