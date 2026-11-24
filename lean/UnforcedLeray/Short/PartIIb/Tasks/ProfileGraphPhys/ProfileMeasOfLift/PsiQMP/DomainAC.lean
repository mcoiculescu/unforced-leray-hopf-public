import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1_3

/-!
# `PartII-b:T10/2/1/3/4` (`PsiQMP`): domain measure

Source of record: `the November 2 reference manuscript` lines 1902-1906.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

theorem psi_domain_ac : UnforcedLeray.Short.IIb.PsiDomainAC := by
  intro c r
  have h1 : hMeas c r ≪ (volume : Measure Coord) := ageμ_ac_volume c (r / 2 - 5 / 2)
  have h2 : (volume.restrict (Ioo 0 (2 * Real.pi)) : Measure ℝ) ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine ⟨Measure.AbsolutelyContinuous.prod h1 h2, ?_⟩
  have hpos : ∀ᵐ p : Coord × ℝ ∂((hMeas c r).prod (volume.restrict (Ioo 0 (2 * Real.pi)))),
      0 < p.1.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := hMeas c r)
      (ν := volume.restrict (Ioo 0 (2 * Real.pi)))).ae
      (ageμ_ae_pos c (r / 2 - 5 / 2))
  have htheta : ∀ᵐ p : Coord × ℝ ∂((hMeas c r).prod (volume.restrict (Ioo 0 (2 * Real.pi)))),
      p.2 ∈ Ioo 0 (2 * Real.pi) :=
    (Measure.quasiMeasurePreserving_snd (μ := hMeas c r)
      (ν := volume.restrict (Ioo 0 (2 * Real.pi)))).ae
      (ae_restrict_mem measurableSet_Ioo)
  exact hpos.and htheta

end UnforcedLeray.Short.IIb
