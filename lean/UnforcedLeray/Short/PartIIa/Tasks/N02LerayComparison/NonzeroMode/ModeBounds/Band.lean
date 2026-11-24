import UnforcedLeray.Short.PartIIa.Sub.N02_4_7

/-!
# Part II-a, task `PartII-a:N02/4/7/1`, helper for `NzmbBand`: band preservation of `S = s ∂_s`

Source of record: `the November 2 reference manuscript`, lines 1722-1727.
Proves the Prop `NzmbBand` from `Sub/N02_4_7.lean`. Idea: if a function vanishes on an open set `U`
then `fderiv` vanishes on `U`, hence `nzS2` vanishes on `U`; outside a closed band the function is zero
on an open neighbourhood, so `nzS2` keeps the same band (same constants).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- If `g` vanishes on an open set `U` and `x ∈ U`, then `nzS2 g x = 0`. -/
lemma nzS2_eq_zero_of_open_zero (g : ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hg : ∀ y ∈ U, g y = 0) (x : ℝ × ℝ) (hx : x ∈ U) : nzS2 g x = 0 := by
  have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hg y hy)
  have hfd : fderiv ℝ g x = 0 := by
    rw [hev.fderiv_eq]
    simp
  unfold nzS2
  simp [hfd]

theorem nzmbBand : NzmbBand := by
  refine ⟨?_, ?_⟩
  · intro a _ha hband
    obtain ⟨s0, s1, L, hs0, hsupp⟩ := hband
    refine ⟨s0, s1, L, hs0, fun x hx => ?_⟩
    have hx' : x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L := by
      by_contra hcon
      -- `x` lies in one of two open sets on which `a` vanishes
      by_cases h1 : x.1 ∈ Icc s0 s1
      · have h2 : ¬ |x.2| ≤ L := fun h => hcon ⟨h1, h⟩
        have hopen : IsOpen {y : ℝ × ℝ | L < |y.2|} :=
          isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
        have hzero : ∀ y ∈ {y : ℝ × ℝ | L < |y.2|}, a y = 0 := by
          intro y hy
          by_contra hay
          have := (hsupp y hay).2
          exact absurd this (not_le.mpr hy)
        exact hx (nzS2_eq_zero_of_open_zero a _ hopen hzero x (not_le.mp h2))
      · have hopen : IsOpen {y : ℝ × ℝ | y.1 ∉ Icc s0 s1} :=
          (isClosed_Icc.isOpen_compl).preimage continuous_fst
        have hzero : ∀ y ∈ {y : ℝ × ℝ | y.1 ∉ Icc s0 s1}, a y = 0 := by
          intro y hy
          by_contra hay
          exact hy (hsupp y hay).1
        exact hx (nzS2_eq_zero_of_open_zero a _ hopen hzero x h1)
    exact hx'
  · intro φ _hφ hband
    obtain ⟨s0, s1, hs0, hsupp⟩ := hband
    refine ⟨s0, s1, hs0, fun x hx => ?_⟩
    by_contra h1
    have hopen : IsOpen {y : ℝ × ℝ | y.1 ∉ Icc s0 s1} :=
      (isClosed_Icc.isOpen_compl).preimage continuous_fst
    have hzero : ∀ y ∈ {y : ℝ × ℝ | y.1 ∉ Icc s0 s1}, φ y = 0 := by
      intro y hy
      by_contra hφy
      exact hy (hsupp y hφy)
    exact hx (nzS2_eq_zero_of_open_zero φ _ hopen hzero x h1)

end UnforcedLeray.Short.PartIIa

end
