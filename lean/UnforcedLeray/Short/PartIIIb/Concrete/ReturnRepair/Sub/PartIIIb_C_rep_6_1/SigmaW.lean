import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1

/-!
# Cut-moment `L¹` bound for `Σ_M` (`PartIII-b:C/rep/6/1`, source 4924-4927, 5400)

Copies of the audited `sigmaM_l1` chain (`SourceL/Ambient/SigmaL1.lean`,
`SourceL/Sub/PartIII-b_C_srcL_9_4.lean`, `SigmaL1/BInt.lean`) with `oldN0` replaced by the cut
moment `oldN0w` (`ReturnRepair/Sub/PartIII-b_C_rep_6.lean`).  The only change in the `L¹`
estimate is that `χ_o ≤ 1` is not dropped: `phaseB` already contains `χ_o(ν·)`, so
`∫ u^{-3/2} phaseB = oldN0w` exactly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Integrability of `u ↦ u^{-3/2} ∫|M(u,·)|` on the old region (from `OldThinFinite`). -/
theorem w_int_base {c ν : ℝ} (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) := by
  have h := hM.2.integral_prod_left
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [integral_const_mul]

/-- Integrability of the cut old moment integrand `u^{-3/2} χ_o(νu) ∫|M(u,·)|`. -/
theorem w_int {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (M : Chart → Mat3)
    (hM : OldThinFinite c ν M) :
    Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))
      (volume.restrict (Ioi (6 / 5 / ν))) := by
  have hcont : Continuous (fun u : ℝ => χo (ν * u)) :=
    hχ.smooth.continuous.comp (continuous_const.mul continuous_id)
  have hp : Measurable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) := measurable_id.pow_const _
  have hG : AEStronglyMeasurable (fun u : ℝ => ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))
      (volume.restrict (Ioi (6 / 5 / ν))) := gAESM_bint hM
  refine Integrable.mono' (w_int_base M hM)
    (hp.aestronglyMeasurable.mul (hcont.aestronglyMeasurable.mul hG)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := (div_pos (by norm_num : (0 : ℝ) < 6 / 5) hν).trans (Set.mem_Ioi.1 hu)
  have hGnn : 0 ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := integral_nonneg fun x => frob_nonneg' _
  have hr : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (mul_nonneg (hχ.range _).1 hGnn))]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hGnn (hχ.range _).2) hr

/-- The cut moment controls the `ENNReal` phase integral (equality up to the cutoff). -/
theorem phaseB_lintegral_W {c ν : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) ≤
      ENNReal.ofReal (oldN0w c ν χo M) := by
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hpt : ∀ u : ℝ, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) ≤
      (Ioi (6 / 5 / ν)).indicator
        (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))) u := by
    intro u
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [Set.indicator_of_mem hu]
      apply ENNReal.ofReal_le_ofReal
      unfold phaseB
      exact le_refl _
    · have h0 : phaseB c ν χo M u = 0 := by
        rw [phaseB_eq_ind_bint c ν hν hχ M, Set.indicator_of_notMem hu]
      rw [Set.indicator_of_notMem hu, h0, mul_zero, ENNReal.ofReal_zero]
  have hint := w_int hν hχ M hM
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (6 / 5 / ν))] fun u : ℝ =>
      u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (ha.trans (Set.mem_Ioi.1 hu)).le _)
      (mul_nonneg (hχ.range _).1 (integral_nonneg fun x => frob_nonneg' _))
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u)
      ≤ ∫⁻ u in Ioi (0 : ℝ), (Ioi (6 / 5 / ν)).indicator
          (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
            (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)))) u :=
        lintegral_mono fun u => hpt u
    _ = ∫⁻ u in Ioi (6 / 5 / ν), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
    _ = ENNReal.ofReal (oldN0w c ν χo M) := by
        unfold oldN0w
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- The cut `L¹` bound on the plane, `∫⁻|Σ_M| ≤ π oldN0w`. -/
theorem sigmaM_lintegral_leW {c ν : ℝ} {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x')) ≤
      ENNReal.ofReal (Real.pi * oldN0w c ν χo M) := by
  have hmeas : AEMeasurable (phaseB c ν χo M) (volume.restrict (Ioi (0 : ℝ))) :=
    (phaseBInt c ν χo hc hν hχ M hM).1
  calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))
      ≤ ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseB c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
        lintegral_mono_ae ((sigmaPointwise c ν χo hc hν hχ M hM).mono
          fun x' h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) :=
        planePolar _ (phaseB_nonneg c ν hχ M) hmeas
    _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal (oldN0w c ν χo M) :=
        by gcongr; exact phaseB_lintegral_W hν hχ M hM
    _ = ENNReal.ofReal (Real.pi * oldN0w c ν χo M) :=
        (ENNReal.ofReal_mul Real.pi_pos.le).symm

/-- **`sigmaM_l1` with the cut moment.** -/
theorem sigmaM_l1W (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    (∀ x' : ℝ × ℝ, ν * (5 / 6) < x'.1 ^ 2 + x'.2 ^ 2 → sigmaM c ν χo M x' = 0) ∧
    Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') ∧
    ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') ≤ Real.pi * oldN0w c ν χo M := by
  have hmeas := sigmaMeas c ν χo hc hν hχ M hM
  have hL := sigmaM_lintegral_leW hc hν hχ hM
  have hN0 := rj6_oldN0w_nonneg c ν hν hχ M
  have hfin : (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))) < ∞ :=
    lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hg : Integrable (fun x' : ℝ × ℝ => frob (sigmaM c ν χo M x')) :=
    ⟨continuous_frob.comp_aestronglyMeasurable hmeas,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => frob_nonneg' _)).2 hfin⟩
  refine ⟨fun x' hx => sigmaM_support hν hχ M x' hx, ?_, ?_⟩
  · exact hg.mono' hmeas (Filter.Eventually.of_forall fun x' => norm_le_frob _)
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => frob_nonneg' _)
      hg.aestronglyMeasurable]
    calc (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))).toReal
        ≤ (ENNReal.ofReal (Real.pi * oldN0w c ν χo M)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
      _ = Real.pi * oldN0w c ν χo M := ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hN0)

end UnforcedLeray.Short.PartIIIb.Concrete
