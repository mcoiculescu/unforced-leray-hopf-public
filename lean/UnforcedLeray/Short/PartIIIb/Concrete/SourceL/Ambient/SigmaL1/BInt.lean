import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_4

/-!
# `PhaseBInt` (source 4924-4927)

`phaseB = χ_o(ν·) ∫|M(·,x)|` vanishes for `u ≤ 6/(5ν)`, is bounded by the inner integral, and is
measurable by Fubini on `oldMeasure`.  The lintegral is bounded by `oldN0` through the integrability
given by `OldThinFinite`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `phaseB` is the indicator of the old region `u > 6/(5ν)` of the inner integral. -/
theorem phaseB_eq_ind_bint (c ν : ℝ) {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) :
    phaseB c ν χo M = (Ioi (6 / 5 / ν)).indicator
      (fun u => χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by
  funext u
  by_cases hu : u ∈ Ioi (6 / 5 / ν)
  · rw [Set.indicator_of_mem hu]
    rfl
  · rw [Set.indicator_of_notMem hu]
    have hu' : u ≤ 6 / 5 / ν := by
      simp only [Set.mem_Ioi, not_lt] at hu
      exact hu
    have h1 : ν * u ≤ 6 / 5 := by
      calc ν * u ≤ ν * (6 / 5 / ν) := mul_le_mul_of_nonneg_left hu' hν.le
        _ = 6 / 5 := by field_simp
    unfold phaseB
    rw [hχ.zero _ h1, zero_mul]

instance sfinite_avgμ_bint (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-- The inner integral is a.e. strongly measurable on the old region (Fubini on `oldMeasure`). -/
theorem gAESM_bint {c ν : ℝ} {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    AEStronglyMeasurable (fun u : ℝ => ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) := by
  have h : AEStronglyMeasurable (fun p : Chart => frob (M p))
      ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) :=
    continuous_frob.comp_aestronglyMeasurable hM.1
  exact h.integral_prod_right'

theorem phaseB_aesm_bint {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    AEStronglyMeasurable (phaseB c ν χo M) (volume.restrict (Ioi (0 : ℝ))) := by
  rw [phaseB_eq_ind_bint c ν hν hχ M, aestronglyMeasurable_indicator_iff measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  rw [Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
  have hcont : Continuous (fun u : ℝ => χo (ν * u)) :=
    hχ.smooth.continuous.comp (continuous_const.mul continuous_id)
  exact hcont.aestronglyMeasurable.mul (gAESM_bint hM)

theorem phaseB_lintegral_bint {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) ≤
      ENNReal.ofReal (oldN0 c ν M) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hpt : ∀ u : ℝ, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) ≤
      (Ioi (6 / 5 / ν)).indicator
        (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) u := by
    intro u
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [Set.indicator_of_mem hu]
      apply ENNReal.ofReal_le_ofReal
      have hu0 : 0 < u := ha.trans (Set.mem_Ioi.1 hu)
      have hg : 0 ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) :=
        integral_nonneg fun x => frob_nonneg' _
      have hr : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
      unfold phaseB
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hg (hχ.range _).2) hr
    · have h0 : phaseB c ν χo M u = 0 := by
        rw [phaseB_eq_ind_bint c ν hν hχ M, Set.indicator_of_notMem hu]
      rw [Set.indicator_of_notMem hu, h0, mul_zero, ENNReal.ofReal_zero]
  have hint : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) *
      ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) (volume.restrict (Ioi (6 / 5 / ν))) := by
    have h := hM.2.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [integral_const_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (6 / 5 / ν))] fun u : ℝ =>
      u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (ha.trans (Set.mem_Ioi.1 hu)).le _)
      (integral_nonneg fun x => frob_nonneg' _)
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u)
      ≤ ∫⁻ u in Ioi (0 : ℝ), (Ioi (6 / 5 / ν)).indicator
          (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
            ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) u :=
        lintegral_mono fun u => hpt u
    _ = ∫⁻ u in Ioi (6 / 5 / ν), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
    _ = ENNReal.ofReal (oldN0 c ν M) := by
        unfold oldN0
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- `PhaseBInt`: the old-region moment of `B = χ_o · ∫|M|` is finite and `B` is measurable. -/
theorem phaseBInt : PhaseBInt := by
  intro c ν χo hc hν hχ M hM
  exact ⟨(phaseB_aesm_bint hν hχ M hM).aemeasurable, phaseB_lintegral_bint hν hχ M hM⟩

end UnforcedLeray.Short.PartIIIb.Concrete
