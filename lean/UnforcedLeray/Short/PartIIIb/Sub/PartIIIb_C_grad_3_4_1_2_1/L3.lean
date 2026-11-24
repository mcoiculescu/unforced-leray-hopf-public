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

/-- The `ei 0` (`∂_u`) image of one monomial `c a^{-m} u^p η^q E`, `∂_u E = -(1/2) a^{-1} u E`:
`∂_u = (c p) a^{-m} u^{p-1} η^q E + (-(1/2) c) a^{-(m+1)} u^{p+1} η^q E`. -/
def dqMon (t : ℝ × ℕ × ℕ × ℕ) : GExpr :=
  [(t.1 * (t.2.2.1 : ℝ), t.2.1, t.2.2.1 - 1, t.2.2.2),
   (-(1 / 2 : ℝ) * t.1, t.2.1 + 1, t.2.2.1 + 1, t.2.2.2)]

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

lemma kD_fderiv_ei0 (f : ℝ × ℝ → ℝ) (x1 x2 : ℝ) (hf : DifferentiableAt ℝ f (x1, x2)) :
    fderiv ℝ f (x1, x2) (ei 0) = deriv (fun τ : ℝ => f (τ, x2)) x1 := by
  have hp : HasDerivAt (fun τ : ℝ => ((τ, x2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x1 :=
    (hasDerivAt_id' x1).prodMk (hasDerivAt_const x1 x2)
  have hc := hf.hasFDerivAt.comp_hasDerivAt x1 hp
  have hei : ei 0 = ((1 : ℝ), (0 : ℝ)) := by simp [ei]
  rw [hei]
  exact hc.deriv.symm

lemma kD_mon_hasDerivAt (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s)
    (t : ℝ × ℕ × ℕ × ℕ) (x1 x2 : ℝ) :
    HasDerivAt (fun τ => gMon ν j t s (τ, x2)) (gEval (dqMon t) ν j s (x1, x2)) x1 := by
  have hu : HasDerivAt (fun τ : ℝ => τ - (j : ℝ) * cOf ν) 1 x1 :=
    (hasDerivAt_id' x1).sub_const _
  have hE := (((hu.pow 2).add_const (x2 ^ 2)).neg.div_const (4 * ageA ν s)).exp
  have H := ((((hu.pow t.2.2.1).const_mul (t.1 * (ageA ν s)⁻¹ ^ t.2.1)).mul_const
    (x2 ^ t.2.2.2)).mul hE)
  refine H.congr_deriv ?_
  simp only [gEval, dqMon, gMon, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.neg_apply, Pi.pow_apply]
  set u := x1 - (j : ℝ) * cOf ν with hu_def
  ring

lemma kD_list_hasDerivAt (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s) (x2 x1 : ℝ) :
    ∀ e : GExpr, HasDerivAt (fun τ => gEval e ν j s (τ, x2))
      (gEval (e.flatMap dqMon) ν j s (x1, x2)) x1
  | [] => by
      simp only [List.flatMap_nil, kD_gEval_nil]
      exact hasDerivAt_const x1 0
  | t :: r => by
      have h1 := kD_mon_hasDerivAt ν j s hA t x1 x2
      have h2 := kD_list_hasDerivAt ν j s hA x2 x1 r
      have hf : (fun τ => gEval (t :: r) ν j s (τ, x2))
          = fun τ => gMon ν j t s (τ, x2) + gEval r ν j s (τ, x2) := by
        funext τ; exact kD_gEval_cons t r ν j s (τ, x2)
      rw [hf, List.flatMap_cons, kD_gEval_append]
      exact h1.add h2

theorem gKerDqProp : GKerDqProp := by
  intro e
  refine ⟨e.flatMap dqMon, fun ν j s x hν hs => ?_⟩
  have hA : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  obtain ⟨x1, x2⟩ := x
  have hdiff : DifferentiableAt ℝ (gEval e ν j s) (x1, x2) := kD_gEval_diffAt ν j s e (x1, x2)
  refine ⟨hdiff, ?_⟩
  rw [kD_fderiv_ei0 _ x1 x2 hdiff]
  exact (kD_list_hasDerivAt ν j s hA x2 x1 e).deriv

end UnforcedLeray.Short.PartIIIb.Concrete
