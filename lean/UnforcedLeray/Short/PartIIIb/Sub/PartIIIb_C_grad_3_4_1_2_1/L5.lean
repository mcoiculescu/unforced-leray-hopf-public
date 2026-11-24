import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `s ∂_s` image of one monomial `c a^{-m} u^p η^q E`, with `a = 1 + νs`, `r² = u² + η²`:
`s∂_s = -m c a^{-m} + m c a^{-(m+1)}` on the power, and `s∂_s E = (1/4) r² (a^{-1} - a^{-2}) E`. -/
def sdMon (t : ℝ × ℕ × ℕ × ℕ) : GExpr :=
  [(-(t.2.1 : ℝ) * t.1, t.2.1, t.2.2.1, t.2.2.2),
   ((t.2.1 : ℝ) * t.1, t.2.1 + 1, t.2.2.1, t.2.2.2),
   (t.1 / 4, t.2.1 + 1, t.2.2.1 + 2, t.2.2.2),
   (t.1 / 4, t.2.1 + 1, t.2.2.1, t.2.2.2 + 2),
   (-(t.1 / 4), t.2.1 + 2, t.2.2.1 + 2, t.2.2.2),
   (-(t.1 / 4), t.2.1 + 2, t.2.2.1, t.2.2.2 + 2)]

lemma kS_gEval_nil (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) : gEval [] ν j s x = 0 := by
  simp [gEval]

lemma kS_gEval_cons (t : ℝ × ℕ × ℕ × ℕ) (e : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) :
    gEval (t :: e) ν j s x = gMon ν j t s x + gEval e ν j s x := by
  simp [gEval]

lemma kS_gEval_append (e₁ e₂ : GExpr) (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) :
    gEval (e₁ ++ e₂) ν j s x = gEval e₁ ν j s x + gEval e₂ ν j s x := by
  simp [gEval, List.map_append, List.sum_append]

lemma kS_ageA_hasDerivAt (ν s : ℝ) : HasDerivAt (fun τ => ageA ν τ) ν s := by
  unfold ageA
  simpa using ((hasDerivAt_id' s).const_mul ν).const_add 1

lemma kS_pow_hasDerivAt (ν s : ℝ) (hA : ageA ν s ≠ 0) (m : ℕ) :
    HasDerivAt (fun τ => (ageA ν τ)⁻¹ ^ m) (-(m : ℝ) * ν * (ageA ν s)⁻¹ ^ (m + 1)) s := by
  cases m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, neg_zero, zero_mul]
    exact hasDerivAt_const s 1
  | succ k =>
    have hinv := (kS_ageA_hasDerivAt ν s).inv hA
    have hp := hinv.pow (k + 1)
    refine hp.congr_deriv ?_
    simp only [Nat.add_sub_cancel, Pi.inv_apply]
    push_cast
    ring

lemma kS_mon_hasDerivAt (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (s : ℝ) (hν : 0 < ν) (hs : 0 < s)
    (t : ℝ × ℕ × ℕ × ℕ) :
    HasDerivAt (fun τ => gMon ν j t τ x) (gEval (sdMon t) ν j s x / s) s := by
  have hA : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hA0 : ageA ν s ≠ 0 := hA.ne'
  have hs0 : s ≠ 0 := hs.ne'
  have hR : HasDerivAt (fun _ : ℝ => -((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2)) 0 s :=
    hasDerivAt_const s _
  have hdiv := hR.div ((kS_ageA_hasDerivAt ν s).const_mul 4) (mul_ne_zero (by norm_num) hA0)
  have hE := hdiv.exp
  have H := ((((kS_pow_hasDerivAt ν s hA0 t.2.1).const_mul t.1).mul_const
    ((x.1 - (j : ℝ) * cOf ν) ^ t.2.2.1)).mul_const (x.2 ^ t.2.2.2)).mul hE
  have hsnu : ν * s * (ageA ν s)⁻¹ = 1 - (ageA ν s)⁻¹ := by
    have hνs : ν * s = ageA ν s - 1 := by unfold ageA; ring
    have hinv : ageA ν s * (ageA ν s)⁻¹ = 1 := mul_inv_cancel₀ hA0
    rw [hνs]
    linear_combination hinv
  refine H.congr_deriv ?_
  rw [eq_div_iff hs0]
  simp only [gEval, sdMon, gMon, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  set u := x.1 - (j : ℝ) * cOf ν with hu_def
  linear_combination (t.1 * (u ^ t.2.2.1 * x.2 ^ t.2.2.2) *
      Real.exp (-(u ^ 2 + x.2 ^ 2) / (4 * ageA ν s)) * ((ageA ν s)⁻¹ ^ t.2.1) *
      (-(t.2.1 : ℝ) + (u ^ 2 + x.2 ^ 2) * (ageA ν s)⁻¹ / 4)) * hsnu

lemma kS_list_hasDerivAt (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (s : ℝ) (hν : 0 < ν) (hs : 0 < s) :
    ∀ e : GExpr, HasDerivAt (fun τ => gEval e ν j τ x) (gEval (e.flatMap sdMon) ν j s x / s) s
  | [] => by
      simp only [List.flatMap_nil, kS_gEval_nil, zero_div]
      exact hasDerivAt_const s 0
  | t :: r => by
      have h1 := kS_mon_hasDerivAt ν j x s hν hs t
      have h2 := kS_list_hasDerivAt ν j x s hν hs r
      have hf : (fun τ => gEval (t :: r) ν j τ x)
          = fun τ => gMon ν j t τ x + gEval r ν j τ x := by
        funext τ; exact kS_gEval_cons t r ν j τ x
      rw [hf, List.flatMap_cons, kS_gEval_append, add_div]
      exact h1.add h2

theorem gKerSProp : GKerSProp := by
  intro e
  exact ⟨e.flatMap sdMon, fun ν j s x hν hs => kS_list_hasDerivAt ν j x s hν hs e⟩

end UnforcedLeray.Short.PartIIIb.Concrete
