import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1_3
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

noncomputable section

open Set

theorem psi_azimuth : UnforcedLeray.Short.IIb.PsiAzimuth := by
  intro R z θ hR hs hθ
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R / Real.sqrt z.1 := ⟨_, rfl⟩
  have hsqrt : 0 < Real.sqrt z.1 := Real.sqrt_pos.mpr hs
  have hρ : 0 < ρ := by rw [hρdef]; exact div_pos hR hsqrt
  have hy0 : (UnforcedLeray.Short.IIb.psiSpace R z θ) 0 = ρ * Real.cos θ := by
    simp [UnforcedLeray.Short.IIb.psiSpace, hρdef]
  have hy1 : (UnforcedLeray.Short.IIb.psiSpace R z θ) 1 = ρ * Real.sin θ := by
    simp [UnforcedLeray.Short.IIb.psiSpace, hρdef]
  have hc : -(⟨ρ * Real.cos θ, ρ * Real.sin θ⟩ : ℂ)
      = (ρ : ℂ) * (((Real.cos (θ - Real.pi) : ℝ) : ℂ)
          + ((Real.sin (θ - Real.pi) : ℝ) : ℂ) * Complex.I) := by
    rw [Real.cos_sub_pi, Real.sin_sub_pi]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  have hazi : UnforcedLeray.Short.IIb.psiAz (UnforcedLeray.Short.IIb.psiSpace R z θ) = θ := by
    unfold UnforcedLeray.Short.IIb.psiAz
    rw [hy0, hy1, hc, Complex.arg_real_mul _ hρ, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]
    ring
  refine ⟨hazi, ?_⟩
  simp only [UnforcedLeray.Short.IIb.psiW, Set.mem_setOf_eq]
  constructor
  · intro h
    simp only [UnforcedLeray.Axi.axis, Set.mem_setOf_eq] at h
    obtain ⟨h0, h1⟩ := h
    rw [hy0] at h0
    rw [hy1] at h1
    have hc0 : Real.cos θ = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hρ.ne'
      · exact h
    have hs0 : Real.sin θ = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hρ.ne'
      · exact h
    have := Real.sin_sq_add_cos_sq θ
    rw [hc0, hs0] at this
    norm_num at this
  · rintro ⟨h0, h1⟩
    rw [hy0] at h0
    rw [hy1] at h1
    have hs0 : Real.sin θ = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hρ.ne'
      · exact h
    have hcpos : 0 < Real.cos θ := by
      by_contra hneg
      push_neg at hneg
      have : ρ * Real.cos θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hneg
      linarith
    have hc1 : Real.cos θ = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [hs0] at this
      nlinarith
    have := (Real.cos_eq_one_iff_of_lt_of_lt (x := θ) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp hc1
    linarith
