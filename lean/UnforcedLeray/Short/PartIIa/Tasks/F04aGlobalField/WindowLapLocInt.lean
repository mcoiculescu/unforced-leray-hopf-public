import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/2`: local integrability on a window strip

Proves the Prop `WindowLapLocInt` (Sub B of `Sub/PartIIa_F04_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 1451-1480.

Route: Tonelli (`lintegral_prod`) turns the iterated finiteness hypothesis into
`∫⁻_{strip} ‖Λ‖^r < ∞`, so `Λ` is in `L^r` of the strip. On each compact subset `k` of the
strip (finite measure, `r ≥ 1`) this gives `Λ ∈ L^1(k)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

open UnforcedLeray UnforcedLeray.PhaseSpace

theorem windowLapLocInt : UnforcedLeray.Short.PartIIa.WindowLapLocInt := by
  intro r hr1 hr a b Λ hmeas hfin
  have hUopen : IsOpen (Ioo a b ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have hS : (volume : Measure (ℝ × Space)).restrict (Ioo a b ×ˢ (univ : Set Space)) =
      (volume.restrict (Ioo a b)).prod (volume : Measure Space) := by
    rw [Measure.volume_eq_prod, Measure.restrict_prod_eq_prod_univ]
  have hmeas' : AEStronglyMeasurable Λ ((volume.restrict (Ioo a b)).prod (volume : Measure Space)) := by
    rw [← hS]
    exact hmeas
  have hFm : AEMeasurable (fun p : ℝ × Space => ‖Λ p‖ₑ ^ r.toReal)
      ((volume.restrict (Ioo a b)).prod (volume : Measure Space)) :=
    (hmeas'.aemeasurable.enorm).pow_const _
  have hprod : ∫⁻ p in Ioo a b ×ˢ (univ : Set Space), ‖Λ p‖ₑ ^ r.toReal =
      ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal := by
    rw [hS]
    exact lintegral_prod _ hFm
  have hA : ∫⁻ p in Ioo a b ×ˢ (univ : Set Space), ‖Λ p‖ₑ ^ r.toReal < ⊤ := by
    rw [hprod]
    exact hfin
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr1.out).ne'
  have hMem : MemLp Λ r (volume.restrict (Ioo a b ×ˢ (univ : Set Space))) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr]
    exact ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one ENNReal.toReal_nonneg) hA.ne
  rw [locallyIntegrableOn_iff hUopen.isLocallyClosed]
  intro k hk hkc
  haveI : IsFiniteMeasure (volume.restrict k) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
  have hMk : MemLp Λ r (volume.restrict k) :=
    MemLp.mono_measure (Measure.restrict_mono hk le_rfl) hMem
  have hM1 : MemLp Λ 1 (volume.restrict k) := hMk.mono_exponent hr1.out
  exact hM1.integrable le_rfl
