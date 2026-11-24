import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2

/-!
# Helper for `PartIII-a:T21/3/2/1/2/5`: the Laplacian of a cylinder test is a bounded cylinder test

The literal target `LapTestBounded` quantifies over all `c : ℝ`. At `c = 0` the periodicity
condition is vacuous, so `φ (q, η) = q · χ(η)` (with `χ` a smooth bump supported in `|η| ≤ R`)
is a cylinder test that is unbounded. Hence the literal target is false. The Prop `LapTestBounded` was corrected (audit sb1) to carry `0 < c`; this file proves it.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology Metric

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa

theorem lapTestBounded : LapTestBounded := by
  intro c hc φ hφ
  have h1 := (hφ.pd 0).pd 0
  have h2 := (hφ.pd 1).pd 1
  obtain ⟨R1, hR1⟩ := h1.band
  obtain ⟨R2, hR2⟩ := h2.band
  have hlap : UnforcedLeray.B0579.IsCylTest c (lapP φ) :=
    { smooth := h1.smooth.add h2.smooth
      periodic := fun x => by
        unfold lapP
        rw [h1.periodic x, h2.periodic x]
      band := ⟨max R1 R2, fun x hx => by
        unfold lapP
        rw [hR1 x (lt_of_le_of_lt (le_max_left _ _) hx),
          hR2 x (lt_of_le_of_lt (le_max_right _ _) hx)]
        simp⟩ }
  have bdd : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ → ∃ K : ℝ, ∀ z, |ψ z| ≤ K := by
    intro ψ hψ
    obtain ⟨R, hR⟩ := hψ.band
    have hcont : ContinuousOn ψ (Icc 0 c ×ˢ Icc (-R) R) := hψ.continuous.continuousOn
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
    refine ⟨|C|, fun z => ?_⟩
    by_cases hz : R < |z.2|
    · rw [hR z hz, abs_zero]
      exact abs_nonneg _
    · push_neg at hz
      have hper : Function.Periodic (fun q : ℝ => ψ (q, z.2)) c :=
        fun q => hψ.periodic (q, z.2)
      obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico₀ hc z.1
      have hmem : (y, z.2) ∈ Icc 0 c ×ˢ Icc (-R) R :=
        ⟨⟨hy.1, hy.2.le⟩, abs_le.1 hz⟩
      have h2' : ψ z = ψ (y, z.2) := hyeq
      rw [h2']
      have hb := hC (y, z.2) hmem
      rw [Real.norm_eq_abs] at hb
      exact hb.trans (le_abs_self C)
  exact ⟨hlap, bdd φ hφ, bdd _ hlap⟩

end UnforcedLeray.Short.IIIa.Exist
