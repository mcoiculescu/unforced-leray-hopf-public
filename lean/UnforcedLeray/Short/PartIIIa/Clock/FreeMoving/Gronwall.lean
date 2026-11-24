import UnforcedLeray.Short.PartIIIa.Sub.T21_c2

/-!
# Part III-a, task `PartIII-a:T21/c2/3` (`fmeGronwall`): Gronwall for a right derivative

Source of record: `the November 2 reference manuscript`, lines 2937-2958.
Proof: `h σ = 𝓔 σ * exp (-K σ)` with `K σ = ∫ τ in t..σ, κ τ`; `K` is differentiated with the
clamped rate `κ ∘ clamp` (continuous on ℝ, equal to `κ` on `[t, s]`), `h` has right derivative
`(𝓔' - κ 𝓔) exp(-K) ≤ 0` on `[t, s)`, and the monotone-boundary lemma gives `h s ≤ h t`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem fmeGronwall : FmeGronwall := by
  intro t s E E' κ hts hE hκ hd
  -- clamped rate, continuous on ℝ and equal to κ on [t, s]
  set cl : ℝ → ℝ := fun τ => max t (min τ s) with hcl
  have hclc : Continuous cl := by
    simp only [hcl]; fun_prop
  have hclmem : ∀ τ, cl τ ∈ Icc t s := fun τ => by
    refine ⟨le_max_left _ _, max_le hts (min_le_right _ _)⟩
  have hκc : Continuous (fun τ => κ (cl τ)) := hκ.comp_continuous hclc hclmem
  have hκeq : ∀ τ ∈ Icc t s, κ (cl τ) = κ τ := by
    intro τ hτ
    have : cl τ = τ := by
      simp only [hcl]
      rw [min_eq_left hτ.2, max_eq_right hτ.1]
    rw [this]
  set K : ℝ → ℝ := fun σ => ∫ τ in t..σ, κ (cl τ) with hK
  have hKd : ∀ σ, HasDerivAt K (κ (cl σ)) σ := by
    intro σ
    exact (hκc.integral_hasStrictDerivAt t σ).hasDerivAt
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun σ => (hKd σ).continuousAt
  have hK0 : K t = 0 := by
    simp only [hK]
    exact intervalIntegral.integral_same
  have hKs : K s = ∫ τ in t..s, κ τ := by
    simp only [hK]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hts] at hτ
    exact hκeq τ hτ
  -- h σ = E σ * exp (-K σ)
  set h : ℝ → ℝ := fun σ => E σ * Real.exp (-K σ) with hh
  have hhc : ContinuousOn h (Icc t s) := by
    refine hE.mul ?_
    exact (Real.continuous_exp.comp hKc.neg).continuousOn
  have hhd : ∀ σ ∈ Ico t s, HasDerivWithinAt h
      (E' σ * Real.exp (-K σ) + E σ * (Real.exp (-K σ) * (-κ (cl σ)))) (Ici σ) σ := by
    intro σ hσ
    have hexp : HasDerivAt (fun σ => Real.exp (-K σ)) (Real.exp (-K σ) * (-κ (cl σ))) σ :=
      ((hKd σ).neg).exp
    have := (hd σ hσ).1.mul hexp.hasDerivWithinAt
    exact this
  have hbound : ∀ σ ∈ Ico t s,
      E' σ * Real.exp (-K σ) + E σ * (Real.exp (-K σ) * (-κ (cl σ))) ≤ 0 := by
    intro σ hσ
    have hle : E' σ ≤ κ σ * E σ := (hd σ hσ).2
    rw [hκeq σ (Ico_subset_Icc_self hσ)]
    have hpos : 0 < Real.exp (-K σ) := Real.exp_pos _
    have hfac : E' σ * Real.exp (-K σ) + E σ * (Real.exp (-K σ) * (-κ σ))
        = (E' σ - κ σ * E σ) * Real.exp (-K σ) := by ring
    rw [hfac]
    have hsub : E' σ - κ σ * E σ ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hsub hpos.le
  have hmono := image_le_of_deriv_right_le_deriv_boundary (f := h)
    (f' := fun σ => E' σ * Real.exp (-K σ) + E σ * (Real.exp (-K σ) * (-κ (cl σ))))
    (B := fun _ => h t) (B' := fun _ => 0) hhc
    (fun σ hσ => by
      have := hhd σ hσ
      exact this)
    le_rfl continuousOn_const (fun σ _ => hasDerivWithinAt_const σ _ _)
    (fun σ hσ => hbound σ hσ)
  have hst : h s ≤ h t := hmono ⟨hts, le_rfl⟩
  have h0 : h t = E t := by
    simp only [hh, hK0, neg_zero, Real.exp_zero, mul_one]
  rw [h0] at hst
  have hst2 : E s * Real.exp (-K s) ≤ E t := hst
  rw [hKs] at hst2
  have hexpK : Real.exp (-(∫ τ in t..s, κ τ)) * Real.exp (∫ τ in t..s, κ τ) = 1 := by
    rw [← Real.exp_add]; simp
  calc E s = E s * Real.exp (-(∫ τ in t..s, κ τ)) * Real.exp (∫ τ in t..s, κ τ) := by
        rw [mul_assoc, hexpK, mul_one]
    _ ≤ E t * Real.exp (∫ τ in t..s, κ τ) :=
        mul_le_mul_of_nonneg_right hst2 (Real.exp_pos _).le

end UnforcedLeray.Short.IIIa
