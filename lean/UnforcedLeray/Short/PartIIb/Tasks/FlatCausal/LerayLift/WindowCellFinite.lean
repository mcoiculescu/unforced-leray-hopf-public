import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/3`: finite `L^r` mass on an age window

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926). Proves
the Prop `WindowCellFinite` of `Sub/T12_2_5.lean`: the age weight `c⁻¹ s^{r/2-5/2}` of `H_r` is bounded
below on a compact age window `[a, b]` with `0 < a`, so the `L^r` mass over `[a, b] × cell` is finite.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem windowCellFinite_proof : UnforcedLeray.Short.IIb.LerayLiftSub.WindowCellFinite := by
  intro c r G hc hr hG hN a b ha
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfm : Measurable (fun x : Coord => ‖G x‖ₑ ^ r) := hG.measurable.enorm.pow_const r
  have hL : ∫⁻ x, ‖G x‖ₑ ^ r ∂(hMeas c r) < ⊤ := by
    have h1 : eLpNorm G (ENNReal.ofReal r) (hMeas c r) < ⊤ := hN
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).1 h1
    simpa [ENNReal.toReal_ofReal hr.le] using h2
  have hL2 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (r / 2 - 5 / 2)) * ‖G p‖ₑ ^ r < ⊤ := by
    have e := UnforcedLeray.Axi.lintegral_ageμ hc (r / 2 - 5 / 2) hfm
    have e' : ∫⁻ p, ‖G p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (r / 2 - 5 / 2)) * ‖G p‖ₑ ^ r := e
    have hL' : ∫⁻ p, ‖G p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := hL
    rw [e'] at hL'
    exact hL'
  rcases le_or_gt a b with hab | hab
  · have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
    have hcont : ContinuousOn (fun s : ℝ => s ^ (r / 2 - 5 / 2)) (Icc a b) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun s hs => Or.inl (ne_of_gt (lt_of_lt_of_le ha hs.1)))
    obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc).exists_isMinOn hne hcont
    have hx0pos : 0 < x0 := lt_of_lt_of_le ha hx0.1
    set m : ℝ≥0∞ := ENNReal.ofReal (c⁻¹ * x0 ^ (r / 2 - 5 / 2)) with hm
    have hm0 : m ≠ 0 :=
      (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hx0pos _))).ne'
    have hS : Icc a b ×ˢ UnforcedLeray.Cyl.cell c ⊆ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c :=
      Set.prod_mono (fun s hs => Set.mem_Ioi.2 (lt_of_lt_of_le ha hs.1)) subset_rfl
    have hpt2 : ∀ x ∈ Icc a b ×ˢ UnforcedLeray.Cyl.cell c,
        m * ‖G x‖ₑ ^ r ≤ ENNReal.ofReal (c⁻¹ * x.1 ^ (r / 2 - 5 / 2)) * ‖G x‖ₑ ^ r := by
      intro x hx
      have h1 : ENNReal.ofReal (c⁻¹ * x0 ^ (r / 2 - 5 / 2)) ≤
          ENNReal.ofReal (c⁻¹ * x.1 ^ (r / 2 - 5 / 2)) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (isMinOn_iff.1 hmin x.1 hx.1) (inv_nonneg.2 hc.le))
      exact mul_le_mul_of_nonneg_right h1 zero_le
    have hms : MeasurableSet (Icc a b ×ˢ UnforcedLeray.Cyl.cell c) :=
      MeasurableSet.prod measurableSet_Icc
        (by unfold UnforcedLeray.Cyl.cell; exact measurableSet_Ico.prod MeasurableSet.univ)
    have hmeasG : Measurable (fun x : Coord => ‖G x‖ₑ ^ r) := hfm
    have hI : m * ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, ‖G x‖ₑ ^ r
        ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (r / 2 - 5 / 2)) * ‖G p‖ₑ ^ r := by
      rw [← lintegral_const_mul m hmeasG]
      calc ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, m * ‖G x‖ₑ ^ r
          ≤ ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c,
              ENNReal.ofReal (c⁻¹ * x.1 ^ (r / 2 - 5 / 2)) * ‖G x‖ₑ ^ r :=
            setLIntegral_mono' hms hpt2
        _ ≤ _ := lintegral_mono_set hS
    have hfin : m * ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, ‖G x‖ₑ ^ r ≠ ⊤ :=
      ne_top_of_le_ne_top hL2.ne hI
    exact ENNReal.lt_top_of_mul_ne_top_right hfin hm0
  · rw [Set.Icc_eq_empty (not_le.2 hab)]
    simp

end UnforcedLeray.Short.IIb.LerayLiftSub
