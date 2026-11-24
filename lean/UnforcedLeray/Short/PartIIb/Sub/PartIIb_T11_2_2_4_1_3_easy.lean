import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1_3

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/3`: the two short lemmas `CutoffDerivBound`, `CommJetBound`.

Source: `the November 2 reference manuscript`
lines 1923-1927.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem commIterDeriv_compact (φ : ℝ → ℝ) (hc : HasCompactSupport φ) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k φ) := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem cutoffDerivBound : CutoffDerivBound := by
  intro φ hφ hc
  have key : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |iteratedDeriv k φ t| ≤ B := by
    intro k
    have hcont : Continuous (iteratedDeriv k φ) :=
      hφ.continuous_iteratedDeriv k (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (commIterDeriv_compact φ hc k)
    exact ⟨max C 0, le_max_right _ _, fun t => by
      have := hC t
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩
  obtain ⟨B1, h10, h1⟩ := key 1
  obtain ⟨B2, h20, h2⟩ := key 2
  obtain ⟨B3, h30, h3⟩ := key 3
  refine ⟨B1 + B2 + B3, by linarith, ?_⟩
  intro k hk1 hk3 t
  have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl
  · have := h1 t; linarith
  · have := h2 t; linarith
  · have := h3 t; linarith

theorem cdir_norm_le (j : Fin 3) : ‖cdir j‖ ≤ 1 := by
  fin_cases j <;> simp [cdir, Prod.norm_def]

theorem cpdC_cpdC_eq (Ψ : Coord → ℂ) (hΨ : ContDiff ℝ ∞ Ψ) (j k : Fin 3) (x : Coord) :
    cpdC j (cpdC k Ψ) x = iteratedFDeriv ℝ 2 Ψ x ![cdir j, cdir k] := by
  have hd : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  rw [iteratedFDeriv_two_apply]
  have h := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ Ψ) (u := fun _ : Coord => cdir k) (x := x)
    (hd x) (differentiableAt_const _)
  unfold cpdC
  rw [h]
  simp

theorem commJetBound : CommJetBound := by
  intro Ψ hΨ x
  refine ⟨fun j => ?_, fun j k => ?_⟩
  · unfold cpdC
    have h := (fderiv ℝ Ψ x).le_opNorm (cdir j)
    have h2 : ‖fderiv ℝ Ψ x‖ * ‖cdir j‖ ≤ ‖fderiv ℝ Ψ x‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (cdir_norm_le j)
    rw [norm_iteratedFDeriv_one]
    exact h.trans h2
  · rw [cpdC_cpdC_eq Ψ hΨ j k x]
    have h := (iteratedFDeriv ℝ 2 Ψ x).le_opNorm ![cdir j, cdir k]
    have e0 : (![cdir j, cdir k] : Fin 2 → Coord) 0 = cdir j := rfl
    have e1 : (![cdir j, cdir k] : Fin 2 → Coord) 1 = cdir k := rfl
    have hp : ∏ i : Fin 2, ‖(![cdir j, cdir k] : Fin 2 → Coord) i‖ ≤ 1 := by
      rw [Fin.prod_univ_two, e0, e1]
      exact mul_le_one₀ (cdir_norm_le j) (norm_nonneg _) (cdir_norm_le k)
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hp)

end UnforcedLeray.Short.IIb
