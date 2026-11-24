import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem mollWinApprox_proof : UnforcedLeray.Short.IIb.MollWinApprox := by
  intro c r M hc hr F hF hzero δ hδ
  have hp : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨ε, hε0, hεδ⟩ := exists_between hδ
  obtain ⟨h0, -, hh0e, hh0c, -⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le hp hε0.ne'
  have hKc : IsCompact (Icc (-M) M ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M) M)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hUo : IsOpen (Ioo (-M - 1) (M + 1) ×ˢ (Ioo (-c) c ×ˢ Ioo (-M - 1) (M + 1))) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hUsub : Ioo (-M - 1) (M + 1) ×ˢ (Ioo (-c) c ×ˢ Ioo (-M - 1) (M + 1)) ⊆ moWin c M :=
    Set.prod_mono Ioo_subset_Icc_self (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hKsub : ∀ x ∈ moBox M ∩ moStrip c,
      x ∈ Icc (-M) M ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M) M) := by
    rintro x ⟨hb, hs⟩
    rw [mem_moBox] at hb
    simp only [moStrip, UnforcedLeray.Cyl.cell, mem_prod, mem_univ, true_and, mem_Ico] at hs
    exact ⟨abs_le.mp hb.1, ⟨hs.1.1, hs.1.2.le⟩, abs_le.mp hb.2⟩
  have hdisj : Disjoint (Icc (-M) M ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-M) M))
      (Ioo (-M - 1) (M + 1) ×ˢ (Ioo (-c) c ×ˢ Ioo (-M - 1) (M + 1)))ᶜ := by
    refine Set.disjoint_left.mpr fun x hxK hxUc => hxUc ?_
    obtain ⟨⟨a1, a2⟩, ⟨⟨b1, b2⟩, ⟨d1, d2⟩⟩⟩ := hxK
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨χ0, hχ0K, hχ0U, hχ0r⟩ := exists_continuous_zero_one_of_isCompact hKc hUo.isClosed_compl hdisj
  refine ⟨fun x => ((1 - χ0 x : ℝ) : ℂ) * h0 x, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (continuous_const.sub χ0.continuous)).mul hh0c
  · intro x hx
    have hxU : x ∈ (Ioo (-M - 1) (M + 1) ×ˢ (Ioo (-c) c ×ˢ Ioo (-M - 1) (M + 1)))ᶜ :=
      fun hxU => hx (hUsub hxU)
    simp [hχ0U hxU]
  · have hpt : ∀ x, ‖F x - ((1 - χ0 x : ℝ) : ℂ) * h0 x‖ ≤ ‖F x - h0 x‖ := by
      intro x
      by_cases hA : x ∈ moBox M ∩ moStrip c
      · have h1 : χ0 x = 0 := hχ0K (hKsub x hA)
        rw [h1, sub_zero]
        simp
      · rw [hzero x hA]
        have h1 : 0 ≤ 1 - χ0 x := by linarith [(hχ0r x).2]
        have h2 : 1 - χ0 x ≤ 1 := by linarith [(hχ0r x).1]
        rw [zero_sub, zero_sub, norm_neg, norm_neg, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg h1]
        exact mul_le_of_le_one_left (norm_nonneg _) h2
    calc eLpNorm (fun x => F x - ((1 - χ0 x : ℝ) : ℂ) * h0 x) (ENNReal.ofReal r) volume
        ≤ eLpNorm (fun x => F x - h0 x) (ENNReal.ofReal r) volume := eLpNorm_mono hpt
      _ ≤ ε := hh0e
      _ < δ := hεδ

end UnforcedLeray.Short.IIb

end
