import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpVanish

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/12`: the flux and its age derivative are bounded

Target (`VtvFluxLemmas.lean`): `VtvFluxFBound`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

`F = vtvFluxF Φ R₀` is smooth (`VtvZpSmooth` composed with `s ↦ (s, (0, R₀+1))`), so `F` and `F'`
are continuous. Both vanish off `[s₁, s₂]` (`VtvZpVanish`), so they are bounded by their maxima on
the compact interval `[s₁, s₂]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvFluxFBound`. The flux `F(s) = vtvFluxF Φ R₀ s` and `F'(s)` are bounded in `s`. -/
theorem vtvFluxFBound : VtvFluxFBound := by
  intro c Φ s₁ s₂ R₀ hS
  have hΦ : IsFlatTest c Φ := hS.1
  have hZ := vtvZpSmooth c Φ hΦ R₀
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (s, ((0:ℝ), R₀ + 1))) := by
    fun_prop
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvFluxF Φ R₀) := hZ.comp hg
  have hDF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (vtvFluxF Φ R₀)) :=
    (contDiff_infty_iff_deriv.1 hF).2
  have hV := vtvZpVanish c Φ s₁ s₂ R₀ hS
  -- vanishing of the flux off the age band
  have hvan : ∀ t, (t < s₁ ∨ s₂ < t) → vtvFluxF Φ R₀ t = 0 := fun t ht =>
    hV.2.1 t (0, R₀ + 1) ht
  -- vanishing of the derivative of the flux off the age band
  have hvan' : ∀ t, (t < s₁ ∨ s₂ < t) → deriv (vtvFluxF Φ R₀) t = 0 := by
    intro t ht
    have hev : vtvFluxF Φ R₀ =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      rcases ht with h | h
      · filter_upwards [Iio_mem_nhds h] with u hu
        exact hvan u (Or.inl (Set.mem_Iio.1 hu))
      · filter_upwards [Ioi_mem_nhds h] with u hu
        exact hvan u (Or.inr (Set.mem_Ioi.1 hu))
    rw [hev.deriv_eq]
    simp
  -- bounds on the compact age band
  obtain ⟨C1, hC1⟩ := isCompact_Icc (a := s₁) (b := s₂) |>.exists_bound_of_continuousOn
    hF.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := isCompact_Icc (a := s₁) (b := s₂) |>.exists_bound_of_continuousOn
    hDF.continuous.continuousOn
  refine ⟨max C1 (max C2 0), fun s => ?_⟩
  by_cases hs : s ∈ Icc s₁ s₂
  · have h1 := hC1 s hs
    have h2 := hC2 s hs
    rw [Real.norm_eq_abs] at h1 h2
    refine ⟨h1.trans (le_max_left _ _), ?_⟩
    exact h2.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hout : s < s₁ ∨ s₂ < s := by
      by_contra hc
      have hc' : s₁ ≤ s ∧ s ≤ s₂ := by
        constructor
        · by_contra h1
          exact hc (Or.inl (lt_of_not_ge h1))
        · by_contra h2
          exact hc (Or.inr (lt_of_not_ge h2))
      exact hs hc'
    rw [hvan s hout, hvan' s hout]
    have h0 : (0:ℝ) ≤ max C1 (max C2 0) := le_trans (le_max_right _ _) (le_max_right _ _)
    simp only [abs_zero]
    exact ⟨h0, h0⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
