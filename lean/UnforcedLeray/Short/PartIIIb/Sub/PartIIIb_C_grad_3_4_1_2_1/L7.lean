import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L6

/-!
# `PartIII-b:C/grad/3/4/1/2/1/7`: the kernel leaf `GKerKopProp` (`𝒦 = η∂_η + 2s∂_s`)

Source `the November 2 reference manuscript`
4963-4980 (`ψ^p_A`, `𝒦` at line 4979), 5036-5039 (`𝒦 = η∂_η + 2s∂_s`), 5063-5079.

Proof.  `Kop ψ s x = x₂ ∂_η ψ(s,x) + 2 s ∂_s ψ(s,x)`.  By `gKerDetaProp` the `η`-derivative is a
kernel expression `eE`; by `gKerMulProp` multiplication by `x₂` is a kernel expression `eM`; by
`gKerSProp` the `s`-derivative `s ∂_s` is a kernel expression `eS`.  The new expression is
`eM ++ scale2 eS`, where `scale2` doubles the leading coefficient of each monomial.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Double the coefficient of every monomial. -/
def kK_scale2 (e : GExpr) : GExpr := e.map fun t => (2 * t.1, t.2.1, t.2.2.1, t.2.2.2)

/-- `gEval (kK_scale2 e) = 2 · gEval e`. -/
lemma kK_scale2_eq (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) (e : GExpr) :
    gEval (kK_scale2 e) ν j s x = 2 * gEval e ν j s x := by
  induction e with
  | nil => simp [gEval, kK_scale2]
  | cons t r ih =>
    have hc : kK_scale2 (t :: r) = (2 * t.1, t.2.1, t.2.2.1, t.2.2.2) :: kK_scale2 r := by
      simp [kK_scale2]
    rw [hc, kD_gEval_cons, kD_gEval_cons, ih]
    simp only [gMon]
    ring

theorem gKerKopProp : GKerKopProp := by
  intro e
  obtain ⟨eE, hE⟩ := gKerDetaProp e
  obtain ⟨eS, hS⟩ := gKerSProp e
  obtain ⟨eM, hM⟩ := (gKerMulProp eE).2
  refine ⟨eM ++ kK_scale2 eS, fun ν j s x hν hs => ?_⟩
  unfold Kop
  obtain ⟨_, hfd⟩ := hE ν j s x hν hs
  have hD : deriv (fun s' => gEval e ν j s' x) s = gEval eS ν j s x / s := (hS ν j s x hν hs).deriv
  have hs0 : s ≠ 0 := hs.ne'
  rw [hfd, hM ν j s x, hD, kD_gEval_append, kK_scale2_eq]
  field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
