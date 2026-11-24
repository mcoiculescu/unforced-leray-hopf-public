import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

/-- **Leaf K5**: a band-integrable field is integrable against every cylinder test on the cell. -/
theorem bandMulTest : UnforcedLeray.Short.IIIa.AdjE1.BandMulTest := by
  intro d f ψ _hd hf hψ
  obtain ⟨R0, hR0⟩ := hψ.band
  have hK : IsCompact (Icc (-(d / 2)) (d / 2) ×ˢ Icc (-R0) R0 : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ × ℝ => (ψ x : ℂ))
      (Icc (-(d / 2)) (d / 2) ×ˢ Icc (-R0) R0) :=
    (Complex.continuous_ofReal.comp hψ.continuous).continuousOn
  have hsub : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R0 ⊆
      Icc (-(d / 2)) (d / 2) ×ˢ Icc (-R0) R0 := by
    rintro ⟨a, b⟩ ⟨⟨⟨h1, h2⟩, _⟩, h3⟩
    exact ⟨⟨h1, h2.le⟩, abs_le.1 h3⟩
  have hmeas : MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R0) :=
    (UnforcedLeray.B0579.measurableSet_cell d).inter (measurableSet_le (by fun_prop) (by fun_prop))
  have hband : IntegrableOn (fun x => f x * (ψ x : ℂ))
      (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R0) :=
    (hf R0).mul_continuousOn_of_subset hcont hmeas hK hsub
  refine IntegrableOn.of_forall_sdiff_eq_zero hband
    (UnforcedLeray.B0579.measurableSet_cell d) ?_
  intro x hx
  have hx2 : R0 < |x.2| := by
    by_contra h
    exact hx.2 ⟨hx.1, not_lt.1 h⟩
  simp [hR0 x hx2]
