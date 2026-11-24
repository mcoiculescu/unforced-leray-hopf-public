import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_8

/-!
# Part II-a, task `PartII-a:N02/4/4/8/1`: `NzFpBand2Decay1`

Source of record: `the November 2 reference manuscript`, lines 1713-1727, 1744-1745.
A smooth `s`-band, compactly `η`-supported scalar function satisfies `NzDecay1` with `κ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem nzFpBand2Decay1 : UnforcedLeray.Short.PartIIa.NzFpBand2Decay1 := by
  unfold UnforcedLeray.Short.PartIIa.NzFpBand2Decay1
  intro g hg hB
  obtain ⟨s0, s1, L, hs0, hsupp⟩ := hB
  have hK : IsCompact (Icc s0 s1 ×ˢ Icc (-L) L) := isCompact_Icc.prod isCompact_Icc
  have hgc : Continuous g := hg.continuous
  have hfd : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by simp)
  have hD : Continuous (fun x => fderiv ℝ g x (1, 0)) := hfd.clm_apply continuous_const
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨D0, hD0⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  have hzero : ∀ x : ℝ × ℝ, x ∉ Icc s0 s1 ×ˢ Icc (-L) L → g x = 0 := by
    intro x hx
    by_contra h
    apply hx
    obtain ⟨h1, h2⟩ := hsupp x h
    exact Set.mk_mem_prod h1 (abs_le.mp h2)
  have hKc : IsOpen (Icc s0 s1 ×ˢ Icc (-L) L)ᶜ := hK.isClosed.isOpen_compl
  have hfzero : ∀ x : ℝ × ℝ, x ∉ Icc s0 s1 ×ˢ Icc (-L) L → fderiv ℝ g x = 0 := by
    intro x hx
    have hev : ∀ᶠ y in nhds x, g y = 0 :=
      Filter.mem_of_superset (hKc.mem_nhds hx) (fun y hy => hzero y hy)
    have heq : g =ᶠ[nhds x] (fun _ => (0 : ℂ)) := hev
    rw [heq.fderiv_eq]
    simp
  set A : ℝ := |C0| + |D0| with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  set C : ℝ := A * Real.exp L + 1 with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  have hbound : ∀ x : ℝ × ℝ, ‖g x‖ ≤ C * Real.exp (-1 * |x.2|) ∧
      ‖fderiv ℝ g x (1, 0)‖ ≤ C * Real.exp (-1 * |x.2|) := by
    intro x
    have hE0 : 0 ≤ Real.exp (-1 * |x.2|) := (Real.exp_pos _).le
    by_cases hx : x ∈ Icc s0 s1 ×ˢ Icc (-L) L
    · have hx2 : |x.2| ≤ L := abs_le.mpr hx.2
      have hFE : 1 ≤ Real.exp L * Real.exp (-1 * |x.2|) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      have e : C * Real.exp (-1 * |x.2|)
          = A * (Real.exp L * Real.exp (-1 * |x.2|)) + Real.exp (-1 * |x.2|) := by
        rw [hCdef]; ring
      have m : A * 1 ≤ A * (Real.exp L * Real.exp (-1 * |x.2|)) :=
        mul_le_mul_of_nonneg_left hFE hA
      have hg1 : ‖g x‖ ≤ A := by
        have h1 := hC0 x hx
        linarith [le_abs_self C0, abs_nonneg D0]
      have hd1 : ‖fderiv ℝ g x (1, 0)‖ ≤ A := by
        have h1 := hD0 x hx
        linarith [le_abs_self D0, abs_nonneg C0]
      refine ⟨?_, ?_⟩
      · rw [e]; linarith
      · rw [e]; linarith
    · have hg0 := hzero x hx
      have hf0 := hfzero x hx
      have hnn : 0 ≤ C * Real.exp (-1 * |x.2|) := mul_nonneg hC hE0
      rw [hg0, hf0]
      exact ⟨by simpa using hnn, by simpa using hnn⟩
  unfold NzDecay1
  exact ⟨hg, ⟨s0, s1, hs0, fun x hx => (hsupp x hx).1⟩, 1, C, one_pos, fun x => hbound x⟩

end UnforcedLeray.Short.PartIIa
