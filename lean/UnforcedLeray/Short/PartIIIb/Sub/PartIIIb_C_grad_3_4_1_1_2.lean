import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp

/-!
# `PartIII-b:C/grad/3/4/1/1/2`: termwise envelope of `h^p_A` from value / first-derivative /
`𝒦` leaves

Source `the November 2 reference manuscript`
4963-4980 (`V_j`, `h^p_A`), 5036-5039, 5063-5079.  Proved: `gradHpTermEnv_of`.
-/

set_option autoImplicit false

noncomputable section

open Set UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Value envelope of the `j`-th lattice term of `h^p_A` (source 4973, 5063-5079). -/
def GradHpValEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |gradHpTm i ν χf A j s x| ≤ C * gradF ν χf A s * gradW ν x j

/-- `∂_q, ∂_η` envelope of the `j`-th lattice term of `h^p_A` (source 4973, 5063-5079). -/
def GradHpDerEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |dQ (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j ∧
      |dEta (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j

/-- `𝒦` envelope of the `j`-th lattice term of `h^p_A` (source 4973, 5063-5079). -/
def GradHpKEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |Kop (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j

theorem gradW_nonneg (ν : ℝ) (x : ℝ × ℝ) (j : ℤ) : 0 ≤ gradW ν x j := by
  unfold gradW latticeW; positivity

theorem gradHpTermEnv_of (h1 : GradHpValEnv) (h2 : GradHpDerEnv) (h3 : GradHpKEnv) :
    GradHpTermEnv := by
  obtain ⟨C1, hC1, e1⟩ := h1
  obtain ⟨C2, hC2, e2⟩ := h2
  obtain ⟨C3, hC3, e3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro ν s χf A hd x i j
  have hp : 0 ≤ gradF ν χf A s * gradW ν x j :=
    mul_nonneg (gradF_nonneg _ _ _ _) (gradW_nonneg _ _ _)
  have key : ∀ C : ℝ, ∀ B : ℝ, 0 ≤ C → C ≤ C1 + C2 + C3 → |B| ≤ C * gradF ν χf A s * gradW ν x j →
      |B| ≤ (C1 + C2 + C3) * gradF ν χf A s * gradW ν x j := by
    intro C B _ hle hB
    refine hB.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hle hp
  obtain ⟨d1, d2⟩ := e2 ν s χf A hd x i j
  exact ⟨key C1 _ hC1 (by linarith) (e1 ν s χf A hd x i j),
    key C2 _ hC2 (by linarith) d1, key C2 _ hC2 (by linarith) d2,
    key C3 _ hC3 (by linarith) (e3 ν s χf A hd x i j)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
