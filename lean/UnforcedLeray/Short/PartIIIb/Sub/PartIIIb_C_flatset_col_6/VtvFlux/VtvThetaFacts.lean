import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/1`: facts about the cutoff profile `θ`

Target (`VtvFluxLemmas.lean`): `VtvThetaFacts`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 (flux cutoff) and 3426-3440.

`vtvTheta t = Real.smoothTransition (2 - t)` is smooth, equal to `1` for `t ≤ 1` and `0` for `t ≥ 2`.
Its derivatives vanish off `[1,2]` (locally constant on `t < 1` and `t > 2`, and at the endpoints by
continuity of the derivatives), so the first three derivatives are continuous with compact support
in `[1,2]` and hence bounded.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A continuous function vanishing to the left of `a` vanishes at `a`. -/
theorem vtv_endpoint_left {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ t, t < a → g t = 0) : g a = 0 := by
  have h1 : Tendsto g (𝓝[<] a) (𝓝 (g a)) :=
    (hg.tendsto a).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[<] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h t ht).symm
  exact tendsto_nhds_unique h1 h2

/-- A continuous function vanishing to the right of `a` vanishes at `a`. -/
theorem vtv_endpoint_right {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ t, a < t → g t = 0) : g a = 0 := by
  have h1 : Tendsto g (𝓝[>] a) (𝓝 (g a)) :=
    (hg.tendsto a).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[>] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h t ht).symm
  exact tendsto_nhds_unique h1 h2

/-- A derivative of a function that is eventually constant at `t` vanishes at `t`. -/
theorem vtv_deriv_eq_zero_of_eventually {f : ℝ → ℝ} {t c : ℝ} (h : ∀ᶠ s in 𝓝 t, f s = c) :
    deriv f t = 0 := by
  have hev : f =ᶠ[𝓝 t] fun _ => c := h
  rw [hev.deriv_eq]
  simp

/-- A continuous function vanishing off `[1,2]` on both open sides vanishes on `t ≤ 1 ∨ 2 ≤ t`. -/
theorem vtv_zero_of_outside {g : ℝ → ℝ} (hg : Continuous g) (hl : ∀ t, t < 1 → g t = 0)
    (hr : ∀ t, 2 < t → g t = 0) : ∀ t, t ≤ 1 ∨ 2 ≤ t → g t = 0 := by
  intro t ht
  rcases ht with ht | ht
  · rcases lt_or_eq_of_le ht with h | h
    · exact hl t h
    · rw [h]
      exact vtv_endpoint_left hg hl
  · rcases lt_or_eq_of_le ht with h | h
    · exact hr t h
    · rw [← h]
      exact vtv_endpoint_right hg hr

/-- A continuous function vanishing off `[1,2]` is bounded. -/
theorem vtv_bounded_of_outside {g : ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ t, t ≤ 1 ∨ 2 ≤ t → g t = 0) : ∃ C : ℝ, ∀ t, |g t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Icc (1:ℝ) 2
  · have := hC t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have h' : t ≤ 1 ∨ 2 ≤ t := by
      rcases lt_or_ge t 1 with h | h
      · exact Or.inl h.le
      · rcases lt_or_ge 2 t with h2 | h2
        · exact Or.inr h2.le
        · exact (ht ⟨h, h2⟩).elim
    rw [h0 t h', abs_zero]
    exact le_max_right _ _

/-- **Facts about the cutoff profile** (source 3511-3514): smoothness, values, vanishing of the
derivatives off `[1,2]`, and boundedness of `θ', θ'', θ'''`. -/
theorem vtvThetaFacts : VtvThetaFacts := by
  unfold VtvThetaFacts
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (2:ℝ) - t) := by
    fun_prop
  have hθ0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => Real.smoothTransition (2 - t)) :=
    Real.smoothTransition.contDiff.comp h1
  have hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vtvTheta := hθ0
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv vtvTheta) :=
    (contDiff_infty_iff_deriv.1 hθ).2
  have hDD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv vtvTheta)) :=
    (contDiff_infty_iff_deriv.1 hD).2
  have hDDD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv (deriv vtvTheta))) :=
    (contDiff_infty_iff_deriv.1 hDD).2
  have hval1 : ∀ t, t ≤ 1 → vtvTheta t = 1 := by
    intro t ht
    unfold vtvTheta
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hval2 : ∀ t, 2 ≤ t → vtvTheta t = 0 := by
    intro t ht
    unfold vtvTheta
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  -- first derivative
  have hL1 : ∀ t, t < 1 → deriv vtvTheta t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 1) (by
      filter_upwards [Iio_mem_nhds ht] with s hs using hval1 s (Set.mem_Iio.1 hs).le)
  have hR2 : ∀ t, 2 < t → deriv vtvTheta t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 0) (by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hval2 s (Set.mem_Ioi.1 hs).le)
  have hD1 : ∀ t, t ≤ 1 ∨ 2 ≤ t → deriv vtvTheta t = 0 :=
    vtv_zero_of_outside hD.continuous hL1 hR2
  -- second derivative
  have hL2 : ∀ t, t < 1 → deriv (deriv vtvTheta) t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 0) (by
      filter_upwards [Iio_mem_nhds ht] with s hs using hL1 s (Set.mem_Iio.1 hs))
  have hR2' : ∀ t, 2 < t → deriv (deriv vtvTheta) t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 0) (by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hR2 s (Set.mem_Ioi.1 hs))
  have hD2 : ∀ t, t ≤ 1 ∨ 2 ≤ t → deriv (deriv vtvTheta) t = 0 :=
    vtv_zero_of_outside hDD.continuous hL2 hR2'
  -- third derivative
  have hL3 : ∀ t, t < 1 → deriv (deriv (deriv vtvTheta)) t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 0) (by
      filter_upwards [Iio_mem_nhds ht] with s hs using hL2 s (Set.mem_Iio.1 hs))
  have hR3 : ∀ t, 2 < t → deriv (deriv (deriv vtvTheta)) t = 0 := fun t ht =>
    vtv_deriv_eq_zero_of_eventually (c := 0) (by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hR2' s (Set.mem_Ioi.1 hs))
  have hD3 : ∀ t, t ≤ 1 ∨ 2 ≤ t → deriv (deriv (deriv vtvTheta)) t = 0 :=
    vtv_zero_of_outside hDDD.continuous hL3 hR3
  -- boundedness
  obtain ⟨C1, hC1⟩ := vtv_bounded_of_outside hD.continuous hD1
  obtain ⟨C2, hC2⟩ := vtv_bounded_of_outside hDD.continuous hD2
  obtain ⟨C3, hC3⟩ := vtv_bounded_of_outside hDDD.continuous hD3
  refine ⟨hθ, fun t ht => hval1 t ht, fun t ht => hval2 t ht, hD1, ?_⟩
  refine ⟨max C1 (max C2 C3), fun t => ⟨?_, ?_, ?_⟩⟩
  · exact (hC1 t).trans (le_max_left _ _)
  · exact (hC2 t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hC3 t).trans ((le_max_right _ _).trans (le_max_right _ _))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
