import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `CB0Bound`: pointwise bound of the planar chart bracket `cB0` (source 5040-5044)

`cAdv F G = DG·F`, `|cDiv F| ≤ 2‖DF‖` (since `‖ei i‖ ≤ 1`), hence
`‖cB0 F G‖ ≤ 3(‖DG‖‖F‖ + ‖DF‖‖G‖)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem cb0Bound : CB0Bound := by
  intro F G s x
  have hei : ∀ i : Fin 2, ‖ei i‖ ≤ 1 := by
    intro i
    fin_cases i <;> simp [ei, Prod.norm_def]
  have hd : ∀ (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (i : Fin 2), ‖L (ei i)‖ ≤ ‖L‖ := fun L i =>
    (L.le_opNorm (ei i)).trans (mul_le_of_le_one_right (norm_nonneg _) (hei i))
  have hdiv : ∀ (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)),
      ‖(L (ei 0)).1 + (L (ei 1)).2‖ ≤ 2 * ‖L‖ := by
    intro L
    have h0 : ‖(L (ei 0)).1‖ ≤ ‖L‖ := (norm_fst_le _).trans (hd L 0)
    have h1 : ‖(L (ei 1)).2‖ ≤ ‖L‖ := (norm_snd_le _).trans (hd L 1)
    have := norm_add_le (L (ei 0)).1 (L (ei 1)).2
    linarith
  have hcD : ∀ (H : ℝ → ℝ × ℝ → ℝ × ℝ), ‖cDiv H s x‖ ≤ 2 * ‖fderiv ℝ (H s) x‖ := by
    intro H
    have := hdiv (fderiv ℝ (H s) x)
    unfold cDiv
    simpa only [Real.norm_eq_abs] using this
  have hA1 : ‖cAdv F G s x‖ ≤ ‖fderiv ℝ (G s) x‖ * ‖F s x‖ :=
    (fderiv ℝ (G s) x).le_opNorm (F s x)
  have hA2 : ‖cAdv G F s x‖ ≤ ‖fderiv ℝ (F s) x‖ * ‖G s x‖ :=
    (fderiv ℝ (F s) x).le_opNorm (G s x)
  have hB1 : ‖cDiv F s x • G s x‖ ≤ 2 * ‖fderiv ℝ (F s) x‖ * ‖G s x‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hcD F) (norm_nonneg _)).trans (le_of_eq (by ring))
  have hB2 : ‖cDiv G s x • F s x‖ ≤ 2 * ‖fderiv ℝ (G s) x‖ * ‖F s x‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hcD G) (norm_nonneg _)).trans (le_of_eq (by ring))
  have q1 := norm_add_le (cAdv F G s x + cAdv G F s x + cDiv F s x • G s x) (cDiv G s x • F s x)
  have q2 := norm_add_le (cAdv F G s x + cAdv G F s x) (cDiv F s x • G s x)
  have q3 := norm_add_le (cAdv F G s x) (cAdv G F s x)
  unfold cB0
  nlinarith [q1, q2, q3, hA1, hA2, hB1, hB2]

end UnforcedLeray.Short.PartIIIb.Concrete
