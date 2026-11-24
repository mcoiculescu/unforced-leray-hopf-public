import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2

/-!
# `PartIII-b:C/grad/3/5/2/2` task 1a: uniform lower bound of the Gaussian exponent

Source `the November 2 reference manuscript`
5063-5079, 4974-4980.  On a set `U` whose closure lies in `{s > 0}` and is bounded, the
exponent `|x_j|² / (4a)` with `a = 1 + ν s` is bounded below by `c j² - K`, uniformly in `j`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psijArgLower (ν : ℝ) (hν : 0 < ν) (U : Set Chart) (hcl : closure U ⊆ {p : Chart | 0 < p.1}) (hbd : Bornology.IsBounded (closure U)) : ∃ c K : ℝ, 0 < c ∧ ∀ j : ℤ, ∀ p ∈ U, c * (j : ℝ) ^ 2 - K ≤ sq2 (xj ν j p.2) / (4 * ageA ν p.1) := by
  obtain ⟨r, hr⟩ := hbd.subset_closedBall 0
  obtain ⟨R, hR0, hRb⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ U, ‖p‖ ≤ R :=
    ⟨|r|, abs_nonneg r, fun p hp =>
      (mem_closedBall_zero_iff.mp (hr (subset_closure hp))).trans (le_abs_self r)⟩
  have hbound : ∀ p ∈ U, |p.1| ≤ R ∧ |p.2.1| ≤ R := by
    intro p hp
    have hn : ‖p‖ ≤ R := hRb p hp
    have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    have h3 : ‖p.2.1‖ ≤ ‖p.2‖ := norm_fst_le p.2
    refine ⟨?_, ?_⟩
    · have := h1.trans hn
      simpa [Real.norm_eq_abs] using this
    · have := (h3.trans h2).trans hn
      simpa [Real.norm_eq_abs] using this
  have ha1pos : 0 < 1 + ν * R := by
    have := mul_nonneg hν.le hR0
    linarith
  have hne : (1 + ν * R) ≠ 0 := ha1pos.ne'
  have hcOf : 0 < cOf ν := by
    unfold cOf
    positivity
  refine ⟨(cOf ν) ^ 2 / (8 * (1 + ν * R)), R ^ 2 / (4 * (1 + ν * R)), ?_, ?_⟩
  · exact div_pos (pow_pos hcOf 2) (by linarith)
  intro j p hp
  have hs0 : 0 < p.1 := hcl (subset_closure hp)
  obtain ⟨hsR, hxR⟩ := hbound p hp
  have hsR' : p.1 ≤ R := (le_abs_self _).trans hsR
  have hxR2 : p.2.1 ^ 2 ≤ R ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg p.2.1) hxR 2
    rwa [sq_abs] at this
  have hA0 : 0 < ageA ν p.1 := by
    unfold ageA
    have := mul_pos hν hs0
    linarith
  have hA1 : ageA ν p.1 ≤ 1 + ν * R := by
    unfold ageA
    have := mul_le_mul_of_nonneg_left hsR' hν.le
    linarith
  have hsq0 : 0 ≤ sq2 (xj ν j p.2) := by
    unfold sq2 xj
    positivity
  have hlow : (cOf ν) ^ 2 * (j : ℝ) ^ 2 / 2 - R ^ 2 ≤ sq2 (xj ν j p.2) := by
    unfold sq2 xj
    simp only
    nlinarith [sq_nonneg (2 * p.2.1 - (j : ℝ) * cOf ν), sq_nonneg p.2.2]
  calc (cOf ν) ^ 2 / (8 * (1 + ν * R)) * (j : ℝ) ^ 2 - R ^ 2 / (4 * (1 + ν * R))
      = ((cOf ν) ^ 2 * (j : ℝ) ^ 2 / 2 - R ^ 2) / (4 * (1 + ν * R)) := by
        field_simp
        ring
    _ ≤ sq2 (xj ν j p.2) / (4 * (1 + ν * R)) :=
        div_le_div_of_nonneg_right hlow (by linarith)
    _ ≤ sq2 (xj ν j p.2) / (4 * ageA ν p.1) :=
        div_le_div_of_nonneg_left hsq0 (by linarith) (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
