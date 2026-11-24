import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `ei 1` (`∂_η`) image of one monomial `c a^{-m} u^p η^q E`, `∂_η E = -(1/2) a^{-1} η E`:
`∂_η = (c q) a^{-m} u^p η^{q-1} E + (-(1/2) c) a^{-(m+1)} u^p η^{q+1} E`. -/
def detaMon (t : ℝ × ℕ × ℕ × ℕ) : GExpr :=
  [(t.1 * (t.2.2.2 : ℝ), t.2.1, t.2.2.1, t.2.2.2 - 1),
   (-(1 / 2 : ℝ) * t.1, t.2.1 + 1, t.2.2.1, t.2.2.2 + 1)]

lemma kD_gEval_nil (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) : gEval [] ν j s x = 0 := by
  simp [gEval]

lemma kD_gEval_cons (t : ℝ × ℕ × ℕ × ℕ) (e : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) :
    gEval (t :: e) ν j s x = gMon ν j t s x + gEval e ν j s x := by
  simp [gEval]

lemma kD_gEval_append (e₁ e₂ : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) :
    gEval (e₁ ++ e₂) ν j s x = gEval e₁ ν j s x + gEval e₂ ν j s x := by
  simp [gEval, List.map_append, List.sum_append]

lemma kD_gMon_diffAt (ν : ℝ) (j : ℤ) (t : ℝ × ℕ × ℕ × ℕ) (s : ℝ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y : ℝ × ℝ => gMon ν j t s y) x := by
  unfold gMon
  fun_prop

lemma kD_gEval_diffAt (ν : ℝ) (j : ℤ) (s : ℝ) (e : GExpr) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (gEval e ν j s) x := by
  induction e with
  | nil =>
    have h : gEval [] ν j s = fun _ => (0 : ℝ) := by
      funext y; exact kD_gEval_nil ν j s y
    rw [h]; exact differentiableAt_const _
  | cons t r ih =>
    have h : gEval (t :: r) ν j s = fun y => gMon ν j t s y + gEval r ν j s y := by
      funext y; exact kD_gEval_cons t r ν j s y
    rw [h]; exact (kD_gMon_diffAt ν j t s x).add ih

lemma kE_fderiv_ei1 (f : ℝ × ℝ → ℝ) (x1 x2 : ℝ) (hf : DifferentiableAt ℝ f (x1, x2)) :
    fderiv ℝ f (x1, x2) (ei 1) = deriv (fun η : ℝ => f (x1, η)) x2 := by
  have hp : HasDerivAt (fun η : ℝ => ((x1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x2 :=
    (hasDerivAt_const x2 x1).prodMk (hasDerivAt_id' x2)
  have hc := hf.hasFDerivAt.comp_hasDerivAt x2 hp
  have hei : ei 1 = ((0 : ℝ), (1 : ℝ)) := by simp [ei]
  rw [hei]
  exact hc.deriv.symm

lemma kE_mon_hasDerivAt (ν : ℝ) (j : ℤ) (s : ℝ)
    (t : ℝ × ℕ × ℕ × ℕ) (x1 x2 : ℝ) :
    HasDerivAt (fun η => gMon ν j t s (x1, η)) (gEval (detaMon t) ν j s (x1, x2)) x2 := by
  have hE := ((((hasDerivAt_const x2 ((x1 - (j : ℝ) * cOf ν) ^ 2)).add
    ((hasDerivAt_id' x2).pow 2)).neg.div_const (4 * ageA ν s)).exp)
  have H := ((((hasDerivAt_id' x2).pow t.2.2.2).const_mul
    (t.1 * (ageA ν s)⁻¹ ^ t.2.1 * (x1 - (j : ℝ) * cOf ν) ^ t.2.2.1)).mul hE)
  refine H.congr_deriv ?_
  simp only [gEval, detaMon, gMon, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, zero_add, Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.neg_apply, Pi.pow_apply,
    Pi.add_apply]
  set u := x1 - (j : ℝ) * cOf ν with hu_def
  ring

lemma kE_list_hasDerivAt (ν : ℝ) (j : ℤ) (s : ℝ) (x1 : ℝ) :
    ∀ e : GExpr, ∀ x2 : ℝ, HasDerivAt (fun η => gEval e ν j s (x1, η))
      (gEval (e.flatMap detaMon) ν j s (x1, x2)) x2
  | [], x2 => by
      simp only [List.flatMap_nil, kD_gEval_nil]
      exact hasDerivAt_const x2 0
  | t :: r, x2 => by
      have h1 := kE_mon_hasDerivAt ν j s t x1 x2
      have h2 := kE_list_hasDerivAt ν j s x1 r x2
      have hf : (fun η => gEval (t :: r) ν j s (x1, η))
          = fun η => gMon ν j t s (x1, η) + gEval r ν j s (x1, η) := by
        funext η; exact kD_gEval_cons t r ν j s (x1, η)
      rw [hf, List.flatMap_cons, kD_gEval_append]
      exact h1.add h2

theorem gKerDetaProp : GKerDetaProp := by
  intro e
  refine ⟨e.flatMap detaMon, fun ν j s x hν hs => ?_⟩
  obtain ⟨x1, x2⟩ := x
  have hdiff : DifferentiableAt ℝ (gEval e ν j s) (x1, x2) := kD_gEval_diffAt ν j s e (x1, x2)
  refine ⟨hdiff, ?_⟩
  rw [kE_fderiv_ei1 _ x1 x2 hdiff]
  exact (kE_list_hasDerivAt ν j s x1 e x2).deriv

end UnforcedLeray.Short.PartIIIb.Concrete
