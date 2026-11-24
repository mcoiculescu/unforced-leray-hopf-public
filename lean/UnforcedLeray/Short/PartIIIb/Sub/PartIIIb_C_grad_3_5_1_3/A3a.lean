import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

/-!
# `PartIII-b:C/grad/3/5/1/3` A3a: `Ay` and its `s`-derivative are bounded on `[s0, s1]`

Source `shorter-proof-2026-11-02.tex` 4963-4980, 5063-5079. `A^y = χ(ν s) • A(s)` with `A` of class
`C^6` on `(0,∞)` (`IsAffElem`) and `χ` smooth (`IsSourceCutoffC`). On a compact interval inside
`(0,∞)` both the value and the derivative are continuous, hence bounded.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpAyBound (as : ℝ) : ∀ (χ : ℝ → ℝ), IsSourceCutoffC χ → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 → ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc s0 s1, ‖Ay ν χ A s‖ ≤ B ∧ ‖deriv (Ay ν χ A) s‖ ≤ B := by
  intro χ hχ ν hν A hA s0 s1 hs0 hs01
  have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hχc : ContDiff ℝ 1 (fun s : ℝ => χ (ν * s)) :=
    (hχ.smooth.of_le (by exact_mod_cast le_top)).comp (contDiff_const.mul contDiff_id)
  have hAc : ContDiffOn ℝ 1 A (Ioi 0) := hA.smooth.of_le (by norm_num)
  have hAy : ContDiffOn ℝ 1 (Ay ν χ A) (Ioi 0) := by
    unfold Ay
    exact (hχc.contDiffOn).smul hAc
  have hcompact : IsCompact (Icc s0 s1) := isCompact_Icc
  have hsub : Icc s0 s1 ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hs0 hs.1
  have hcont : ContinuousOn (Ay ν χ A) (Icc s0 s1) := hAy.continuousOn.mono hsub
  have hdcont : ContinuousOn (deriv (Ay ν χ A)) (Icc s0 s1) :=
    (hAy.continuousOn_deriv_of_isOpen hopen le_rfl).mono hsub
  obtain ⟨C1, hC1⟩ := hcompact.exists_bound_of_continuousOn hcont
  obtain ⟨C2, hC2⟩ := hcompact.exists_bound_of_continuousOn hdcont
  refine ⟨max 0 (max C1 C2), le_max_left _ _, ?_⟩
  intro s hs
  exact ⟨(hC1 s hs).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hC2 s hs).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
