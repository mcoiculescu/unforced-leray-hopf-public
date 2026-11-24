import UnforcedLeray.Short.PartIIb.Sub.T12_1_5

/-!
# Part II-b, task `PartII-b:T12/1/5/3` (`CylPairingIntegrableOn`)

Source of record: `the November 2 reference manuscript`, line 1670 (the ordinary
planar cylinder projection `P_0`). Leaf statement `CylPairingIntegrableOn` of `Sub/T12_1_5.lean`.

Proof. Let `S = Ico (-c/2) (c/2) ×ˢ Icc (-L) L` (a subset of the cell with finite measure) and
`K = Icc (-c/2) (c/2) ×ˢ Icc (-L) L` (compact, containing `S`). `F ∈ L^r(avgμ c)` gives
`F ∈ L^r(volume.restrict S)`, hence `F ∈ L^1(volume.restrict S)`, hence each component is
integrable there. `w` is bounded on `K`, so the product is integrable on `S`. Off `S` inside the
cell, `|z.2| > L` and `w z = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T12/1/5/3`** (Hoelder on the cell; SP 1670). -/
theorem cylPairingIntegrableOn : CylPairingIntegrableOn := by
  unfold CylPairingIntegrableOn
  intro c r F hc hr hF i w hw hsupp
  obtain ⟨hper, hFa⟩ := hF
  obtain ⟨L, hL⟩ := hsupp
  -- the cutoff box `S` inside the cell, and a compact box `K` containing `S`
  have hSsub_cell : Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L ⊆ UnforcedLeray.Cyl.cell c :=
    Set.prod_mono subset_rfl (Set.subset_univ _)
  have hSK : Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L ⊆ Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L :=
    Set.prod_mono Set.Ico_subset_Icc_self subset_rfl
  have hKc : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
    isCompact_Icc.prod isCompact_Icc
  have hSm : MeasurableSet (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hKlt : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) < ⊤ := hKc.measure_lt_top
  have hSfin : volume (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L) ≠ ⊤ :=
    ne_top_of_le_ne_top hKlt.ne (measure_mono hSK)
  have : IsFiniteMeasure (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    isFiniteMeasure_restrict.2 hSfin
  -- a bound for `w` on `K`
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hw.continuousOn
  -- `ofReal c • avgμ c` is the unnormalized cell measure
  have hcell_eq : ENNReal.ofReal c • UnforcedLeray.Cyl.avgμ c =
      volume.restrict (UnforcedLeray.Cyl.cell c) := by
    rw [UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, smul_smul,
      ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
  -- `F ∈ L^r` on the finite-measure piece `S`
  have hFS : MemLp F (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) := by
    refine MemLp.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top ?_ hFa
    rw [hcell_eq]
    exact Measure.restrict_mono hSsub_cell le_rfl
  -- `F ∈ L^1` on `S`
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr
  have hF1S : MemLp F 1 (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    hFS.mono_exponent hq1
  have hFI : Integrable F (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    memLp_one_iff_integrable.1 hF1S
  -- the `i`-th component is integrable on `S`
  have hFi_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => F z i)
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).comp_aestronglyMeasurable
      hFS.aestronglyMeasurable
  have hFi_int : Integrable (fun z : ℝ × ℝ => F z i)
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    Integrable.mono' hFI.norm hFi_aesm (ae_of_all _ (fun z => PiLp.norm_apply_le (F z) i))
  -- the product on `S`
  have hprod_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => F z i * (w z : ℂ))
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)) :=
    hFi_aesm.mul (Complex.continuous_ofReal.comp hw).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L)),
      ‖F z i * (w z : ℂ)‖ ≤ C * ‖F z i‖ := by
    filter_upwards [ae_restrict_mem hSm] with z hz
    have hwz : ‖(w z : ℂ)‖ ≤ C := by
      rw [Complex.norm_real]
      exact hC z (hSK hz)
    calc ‖F z i * (w z : ℂ)‖ = ‖F z i‖ * ‖(w z : ℂ)‖ := norm_mul _ _
      _ ≤ ‖F z i‖ * C := mul_le_mul_of_nonneg_left hwz (norm_nonneg _)
      _ = C * ‖F z i‖ := mul_comm _ _
  have hint_S : IntegrableOn (fun z : ℝ × ℝ => F z i * (w z : ℂ))
      (Ico (-c / 2) (c / 2) ×ˢ Icc (-L) L) volume :=
    Integrable.mono' (hFi_int.norm.const_mul C) hprod_aesm hbound
  -- outside `S` inside the cell the integrand vanishes
  refine IntegrableOn.of_forall_sdiff_eq_zero hint_S
    (measurableSet_Ico.prod MeasurableSet.univ) ?_
  intro z hz
  have hz1 : z.1 ∈ Ico (-c / 2) (c / 2) := (Set.mem_prod.1 hz.1).1
  have hLz : L < |z.2| := by
    by_contra hcon
    have hle : |z.2| ≤ L := not_lt.1 hcon
    exact hz.2 (Set.mem_prod.2 ⟨hz1, abs_le.1 hle⟩)
  simp [hL z hLz]

end UnforcedLeray.Short.IIb
