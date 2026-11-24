import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.PeriodicBoxBound

/-!
# `PartIII-a:T21/2/7/2/1/1/7/1`: the pairing bound `PairBound`

Source: `the November 2 reference manuscript` lines 3060-3061.
Cauchy-Schwarz on the box `sliceBox R` (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) and the periodic
box bound `periodicBoxBound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem pairBound : UnforcedLeray.Short.IIIa.PairBound := by
  intro c m R hc
  obtain ⟨M, hMtop, hM⟩ := periodicBoxBound c m R hc
  refine ⟨M.toReal * (volume (sliceBox R)).toReal ^ (1 / 2 : ℝ), ?_⟩
  intro h θ B hper hmemLp hθm hθsupp hθB
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hθB 0)
  have hXne : xNorm c (-m) h ≠ ⊤ := hmemLp.eLpNorm_lt_top.ne
  have hmeasH : AEStronglyMeasurable h (B0579.cellMeasure c (-m)) := hmemLp.aestronglyMeasurable
  obtain ⟨hmeas, hbound⟩ := hM h hper hmeasH
  have hcpt : IsCompact (sliceBox R) := isCompact_Icc.prod isCompact_Icc
  have hVtop : volume (sliceBox R) ≠ ⊤ := hcpt.measure_lt_top.ne
  -- Hölder on the box: L¹ norm bounded by the L² norm times the box volume to the power 1/2
  have hkey : eLpNorm h 1 (volume.restrict (sliceBox R)) ≤
      eLpNorm h 2 (volume.restrict (sliceBox R)) * volume (sliceBox R) ^ (1 / 2 : ℝ) := by
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (sliceBox R))
      (f := h) (p := 1) (q := 2) (by norm_num) hmeas
    rw [Measure.restrict_apply_univ] at h1
    have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [e] at h1
    exact h1
  have hbnd_ne : M * xNorm c (-m) h ≠ ⊤ := ENNReal.mul_ne_top hMtop hXne
  have hA_ne : eLpNorm h 2 (volume.restrict (sliceBox R)) ≠ ⊤ := ne_top_of_le_ne_top hbnd_ne hbound
  have hV_rpow : volume (sliceBox R) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop
  have hfin : eLpNorm h 2 (volume.restrict (sliceBox R)) * volume (sliceBox R) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hA_ne hV_rpow
  have hlt1 : eLpNorm h 1 (volume.restrict (sliceBox R)) < ⊤ :=
    lt_of_le_of_lt hkey (lt_top_iff_ne_top.2 hfin)
  have hint : Integrable h (volume.restrict (sliceBox R)) :=
    memLp_one_iff_integrable.1 (⟨hmeas, hlt1⟩ : MemLp h 1 (volume.restrict (sliceBox R)))
  -- integrability of θ * h
  have hθh_meas : AEStronglyMeasurable (fun x => θ x * h x) (volume.restrict (sliceBox R)) :=
    hθm.aestronglyMeasurable.mul hmeas
  have hI : Integrable (fun x => θ x * h x) (volume.restrict (sliceBox R)) := by
    refine Integrable.mono' (hint.norm.const_mul B) hθh_meas (Eventually.of_forall fun x => ?_)
    show ‖θ x * h x‖ ≤ B * ‖h x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hθB x) (norm_nonneg _)
  have hfull : Integrable (fun x => θ x * h x) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero hI (fun x hx => ?_)
    show θ x * h x = 0
    rw [hθsupp x hx, zero_mul]
  refine ⟨hfull, ?_⟩
  have hzero : ∀ x, x ∉ sliceBox R → θ x * h x = 0 := fun x hx => by
    rw [hθsupp x hx, zero_mul]
  have hEq : ∫ x, θ x * h x = ∫ x in sliceBox R, θ x * h x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [hEq]
  have h1 : ‖∫ x in sliceBox R, θ x * h x‖ ≤ ∫ x in sliceBox R, B * ‖h x‖ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      (hint.norm.const_mul B) (Eventually.of_forall fun x => ?_)
    show ‖θ x * h x‖ ≤ B * ‖h x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hθB x) (norm_nonneg _)
  have hnorm1 : ∫ x in sliceBox R, ‖h x‖ = (eLpNorm h 1 (volume.restrict (sliceBox R))).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
  have hkeyR : (eLpNorm h 1 (volume.restrict (sliceBox R))).toReal ≤
      (eLpNorm h 2 (volume.restrict (sliceBox R)) * volume (sliceBox R) ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_mono hfin hkey
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hkeyR
  have hA2 : (eLpNorm h 2 (volume.restrict (sliceBox R))).toReal ≤
      M.toReal * (xNorm c (-m) h).toReal := by
    have := ENNReal.toReal_mono hbnd_ne hbound
    rwa [ENNReal.toReal_mul] at this
  have hVr : 0 ≤ (volume (sliceBox R)).toReal ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hnormle : ∫ x in sliceBox R, ‖h x‖ ≤
      M.toReal * (xNorm c (-m) h).toReal * (volume (sliceBox R)).toReal ^ (1 / 2 : ℝ) := by
    rw [hnorm1]
    exact hkeyR.trans (mul_le_mul_of_nonneg_right hA2 hVr)
  calc ‖∫ x in sliceBox R, θ x * h x‖ ≤ ∫ x in sliceBox R, B * ‖h x‖ := h1
    _ = B * ∫ x in sliceBox R, ‖h x‖ := integral_const_mul _ _
    _ ≤ B * (M.toReal * (xNorm c (-m) h).toReal * (volume (sliceBox R)).toReal ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnormle hB0
    _ = M.toReal * (volume (sliceBox R)).toReal ^ (1 / 2 : ℝ) * B * (xNorm c (-m) h).toReal := by ring

end UnforcedLeray.Short.IIIa
