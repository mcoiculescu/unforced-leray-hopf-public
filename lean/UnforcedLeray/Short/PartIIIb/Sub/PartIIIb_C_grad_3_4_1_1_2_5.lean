import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2

/-!
# `PartIII-b:C/grad/3/4/1/1/2/5`: `𝒦` envelope of `h^p_A` from its two halves

Source `the November 2 reference manuscript`
4963-4980 (`V_j`, `h^p_A`), 5036-5039, 5063-5079.  `𝒦ψ = η ∂_η ψ + 2 s ∂_s ψ`, so the envelope
splits into the `x`-part `η ∂_η` and the `s`-part `s ∂_s` (each term carries one more
polynomial factor, i.e. needs the weight-2 Gaussian bounds).  Proved: `gradHpKEnv_of`.
-/

set_option autoImplicit false

noncomputable section

open Set UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `x`-part of the `𝒦` envelope: `|η ∂_η (h^p_A)_i-term|` (source 5063-5079). -/
def GradKopXEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |x.2 * fderiv ℝ (gradHpTm i ν χf A j s) x (ei 1)| ≤ C * gradF ν χf A s * gradW ν x j

/-- `s`-part of the `𝒦` envelope: `|s ∂_s (h^p_A)_i-term|` (source 5063-5079). -/
def GradKopSEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |s * deriv (fun s' => gradHpTm i ν χf A j s' x) s| ≤ C * gradF ν χf A s * gradW ν x j

theorem gradHpKEnv_of (h1 : GradKopXEnv) (h2 : GradKopSEnv) : GradHpKEnv := by
  obtain ⟨C1, hC1, e1⟩ := h1
  obtain ⟨C2, hC2, e2⟩ := h2
  refine ⟨C1 + 2 * C2, by positivity, ?_⟩
  intro ν s χf A hd x i j
  have hp : 0 ≤ gradF ν χf A s * gradW ν x j :=
    mul_nonneg (gradF_nonneg _ _ _ _) (gradW_nonneg _ _ _)
  have a1 := e1 ν s χf A hd x i j
  have a2 := e2 ν s χf A hd x i j
  unfold Kop
  have h3 : |2 * s * deriv (fun s' => gradHpTm i ν χf A j s' x) s| =
      2 * |s * deriv (fun s' => gradHpTm i ν χf A j s' x) s| := by
    rw [mul_assoc, abs_mul]; norm_num
  calc _ ≤ |x.2 * fderiv ℝ (gradHpTm i ν χf A j s) x (ei 1)| +
        |2 * s * deriv (fun s' => gradHpTm i ν χf A j s' x) s| := abs_add_le _ _
    _ ≤ C1 * gradF ν χf A s * gradW ν x j + 2 * (C2 * gradF ν χf A s * gradW ν x j) := by
        rw [h3]; linarith
    _ = (C1 + 2 * C2) * gradF ν χf A s * gradW ν x j := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
