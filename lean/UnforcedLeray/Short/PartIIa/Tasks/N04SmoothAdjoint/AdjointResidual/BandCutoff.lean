import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_Org
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!


Source: `the November 2 reference manuscript`,
lines 1464-1466 (cutoffs) and 1800-1806 (`v = T_0^* z` vanishes for `s > H_1`).
The cutoff `χ(s) = st(2Rs - 1) · st(S + 1 - s)` (`st` the smooth transition) multiplies the profile.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.B0220 UnforcedLeray.B0223

namespace UnforcedLeray.Short.PartIIa

/-- Smooth cutoff in the age variable: zero for `s ≤ R⁻¹/2` and for `s ≥ S + 1`, one on
`[R⁻¹, S]`. -/
theorem profileBandCutoff_cutoff (R S : ℝ) (hR : 0 < R) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ s, s ≤ R⁻¹ / 2 → χ s = 0) ∧
      (∀ s, R⁻¹ ≤ s → s ≤ S → χ s = 1) ∧ (∀ s, S + 1 ≤ s → χ s = 0) := by
  have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  refine ⟨fun s => Real.smoothTransition (2 * R * s - 1) * Real.smoothTransition (S + 1 - s),
    ?_, ?_, ?_, ?_⟩
  · have hA : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * R * s - 1)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    have hB : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (S + 1 - s)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact hA.mul hB
  · intro s hs
    have h1 : 2 * R * s - 1 ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hs hR.le, hRR]
    simp only [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · intro s hs hs'
    have h1 : 1 ≤ 2 * R * s - 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hs hR.le, hRR]
    have h2 : 1 ≤ S + 1 - s := by linarith
    simp only [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
      mul_one]
  · intro s hs
    have h1 : S + 1 - s ≤ 0 := by linarith
    simp only [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

/-- **Band cutoff below a level (`ProfileBandCutoff`)**. -/
theorem profileBandCutoff : ProfileBandCutoff := by
  intro c R hR u hsmooth hper hsupp S
  obtain ⟨χ, hχC, hχ0, hχ1, hχS⟩ := profileBandCutoff_cutoff R S hR
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  -- the cutoff vanishes only strictly above `R⁻¹/2`
  have hχpos : ∀ s, χ s ≠ 0 → R⁻¹ / 2 < s := by
    intro s hs
    by_contra h
    exact hs (hχ0 s (not_lt.mp h))
  refine ⟨fun p => χ p.1 • u p, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- smoothness
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · have hu' : ContDiffAt ℝ ∞ u p :=
        hsmooth.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
      have hχ' : ContDiffAt ℝ ∞ (fun q : Profile => χ q.1) p :=
        ContDiffAt.comp p hχC.contDiffAt contDiffAt_fst
      exact hχ'.smul hu'
    · have hlt : p.1 < R⁻¹ / 2 := by linarith
      have hz : ∀ᶠ q in 𝓝 p, q.1 < R⁻¹ / 2 :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
      have hEv : (fun q : Profile => χ q.1 • u q) =ᶠ[𝓝 p] fun _ => (0 : MeridC) := by
        filter_upwards [hz] with q hq
        simp only [hχ0 q.1 hq.le, zero_smul]
      exact (contDiffAt_const (c := (0 : MeridC))).congr_of_eventuallyEq hEv
  · -- periodicity
    intro p
    show χ p.1 • u (p.1, p.2.1 + c, p.2.2) = χ p.1 • u p
    rw [hper p]
  · -- band
    refine ⟨R⁻¹ / 2, S + 1, R * Real.sqrt (|S| + 1), by linarith, ?_⟩
    intro p hp
    have hχne : χ p.1 ≠ 0 := by
      intro h
      apply hp
      simp only [h, zero_smul]
    have hu0 : u p ≠ 0 := by
      intro h
      apply hp
      simp only [h, smul_zero]
    have hpos : R⁻¹ / 2 < p.1 := hχpos p.1 hχne
    have hlt : p.1 < S + 1 := by
      by_contra h
      exact hχne (hχS p.1 (not_lt.mp h))
    have hp0 : 0 < p.1 := lt_trans (by linarith) hpos
    refine ⟨⟨hpos.le, hlt.le⟩, ?_⟩
    have hb := (hsupp p hp0 hu0).2
    have hsq : R * Real.sqrt p.1 ≤ R * Real.sqrt (|S| + 1) := by
      apply mul_le_mul_of_nonneg_left _ hR.le
      apply Real.sqrt_le_sqrt
      have := le_abs_self S
      have := abs_nonneg S
      linarith
    exact le_trans hb hsq
  · -- agreement with `u` below `S`
    intro p hp0 hpS
    show χ p.1 • u p = u p
    by_cases h : R⁻¹ ≤ p.1
    · rw [hχ1 p.1 h hpS.le, one_smul]
    · have hu0 : u p = 0 := by
        by_contra hne
        exact h (hsupp p hp0 hne).1
      show χ p.1 • u p = u p
      rw [hu0, smul_zero]

end UnforcedLeray.Short.PartIIa
