import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Multiplication by `u = x₁ - jc` raises the `p`-exponent by one in every monomial. -/
def kM_u (e : GExpr) : GExpr := e.map fun t => (t.1, t.2.1, t.2.2.1 + 1, t.2.2.2)

/-- Multiplication by `η = x₂` raises the `q`-exponent by one in every monomial. -/
def kM_eta (e : GExpr) : GExpr := e.map fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2 + 1)

lemma kM_gMon_u (ν : ℝ) (j : ℤ) (t : ℝ × ℕ × ℕ × ℕ) (s : ℝ) (x : ℝ × ℝ) :
    gMon ν j (t.1, t.2.1, t.2.2.1 + 1, t.2.2.2) s x
      = (x.1 - (j : ℝ) * cOf ν) * gMon ν j t s x := by
  simp only [gMon]
  ring

lemma kM_gMon_eta (ν : ℝ) (j : ℤ) (t : ℝ × ℕ × ℕ × ℕ) (s : ℝ) (x : ℝ × ℝ) :
    gMon ν j (t.1, t.2.1, t.2.2.1, t.2.2.2 + 1) s x = x.2 * gMon ν j t s x := by
  simp only [gMon]
  ring

lemma kM_u_eq (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) (e : GExpr) :
    (x.1 - (j : ℝ) * cOf ν) * gEval e ν j s x = gEval (kM_u e) ν j s x := by
  induction e with
  | nil => simp [gEval, kM_u]
  | cons t r ih =>
    have hc : kM_u (t :: r) = (t.1, t.2.1, t.2.2.1 + 1, t.2.2.2) :: kM_u r := by
      simp [kM_u]
    rw [hc]
    simp only [gEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [mul_add, ih, kM_gMon_u]

lemma kM_eta_eq (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) (e : GExpr) :
    x.2 * gEval e ν j s x = gEval (kM_eta e) ν j s x := by
  induction e with
  | nil => simp [gEval, kM_eta]
  | cons t r ih =>
    have hc : kM_eta (t :: r) = (t.1, t.2.1, t.2.2.1, t.2.2.2 + 1) :: kM_eta r := by
      simp [kM_eta]
    rw [hc]
    simp only [gEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [mul_add, ih, kM_gMon_eta]

theorem gKerMulProp : GKerMulProp := by
  intro e
  exact ⟨⟨kM_u e, fun ν j s x => kM_u_eq ν j s x e⟩, ⟨kM_eta e, fun ν j s x => kM_eta_eq ν j s x e⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
