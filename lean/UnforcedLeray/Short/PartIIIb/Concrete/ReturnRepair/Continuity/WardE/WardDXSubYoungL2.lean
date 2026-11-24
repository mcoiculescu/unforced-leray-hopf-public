import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungL2.H2

/-!
# `PartIII-b:C/cont/WE/1`: `WardDXSubYoungL2`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`wardX` `μ`-difference in the young `L²` norm (value and first partials)**. -/
theorem wSub_wardXYoungL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => wardX ν μ R c χy g τ y - wardX ν μ' R c χy g τ y) g ∧
        ∀ j : Fin 3,
          YoungL2Le c ν R (C * |μ - μ'|)
            (fun τ y => physPd (wardX ν μ R c χy g τ) j y -
              physPd (wardX ν μ' R c χy g τ) j y) g := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ := wSub_wardX0YoungL2 ν R c hν hR hc
  obtain ⟨CB, hCB0, hCB⟩ := wSub_wardStreamCorrYoungL2 ν R c χy hχy hν hR hc
  obtain ⟨Kcut, hKcut0, hKcut⟩ := w3_cut_deriv_bound R ν hχy hR hν
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  refine ⟨(1 + Kcut) * CA + CB, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  obtain ⟨hX0, hX0'⟩ := hCA μ μ' hμ hμ' g hg
  obtain ⟨hCorr, hCorr'⟩ := hCB μ μ' hμ hμ' g hg
  have hCA_mu : 0 ≤ CA * |μ - μ'| := mul_nonneg hCA0 (abs_nonneg _)
  have hCB_mu : 0 ≤ CB * |μ - μ'| := mul_nonneg hCB0 (abs_nonneg _)
  have bX0 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y))
      (CA * |μ - μ'|) := by
    have := wyl_bd_of_young hX0
    rwa [max_eq_left hCA_mu] at this
  have bCorr : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y -
        wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y))
      (CB * |μ - μ'|) := by
    have := wyl_bd_of_young hCorr
    rwa [max_eq_left hCB_mu] at this
  have hXm1 := w3_wardX_measurable ν μ R c hχy hg
  have hXm2 := w3_wardX_measurable ν μ' R c hχy hg
  refine ⟨?_, fun j => ?_⟩
  · refine w10_young_of_sum
      (w10_read_meas (hXm1.sub hXm2)).aestronglyMeasurable bX0 bCorr hCA_mu hCB_mu
      (by nlinarith [mul_nonneg hKcut0 hCA_mu]) ?_
    refine w10_read_dom hν hR fun τ y _ => ?_
    rw [wardX_eq_cut_add_corr, wardX_eq_cut_add_corr]
    have heq : (χy (ν * age R y) • wardX0 ν μ R c g τ y +
          wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y) -
        (χy (ν * age R y) • wardX0 ν μ' R c g τ y +
          wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y) =
        χy (ν * age R y) • (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) +
          (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y -
            wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y) := by
      rw [smul_sub]
      abel
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχy.range (ν * age R y)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχy.range (ν * age R y)).2
  · have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    have hdX1 : ∀ τ y, y ∈ youngOpen ν R → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y :=
      fun τ y hy => (w3_wardX_diff_and_pd hχy hν hR hc hμ_gt hg τ hy).1
    have hdX2 : ∀ τ y, y ∈ youngOpen ν R → DifferentiableAt ℝ (wardX ν μ' R c χy g τ) y :=
      fun τ y hy => (w3_wardX_diff_and_pd hχy hν hR hc hμ'_gt hg τ hy).1
    have hPd1 := w10_meas_pd hXm1 hUo.measurableSet hdX1 j
    have hPd2 := w10_meas_pd hXm2 hUo.measurableSet hdX2 j
    have hread : wardYoungRead ν R
        (fun τ y => physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y) =
        wardYoungRead ν R (fun τ y =>
          (if y ∈ youngOpen ν R then physPd (wardX ν μ R c χy g τ) j y else 0) -
          (if y ∈ youngOpen ν R then physPd (wardX ν μ' R c χy g τ) j y else 0)) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
      simp [this]
    have hFm : AEStronglyMeasurable
        (wardYoungRead ν R
          (fun τ y => physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y))
        (ageμ c (-3 / 2)) := by
      rw [hread]
      exact (w10_read_meas (hPd1.sub hPd2)).aestronglyMeasurable
    have bX0j : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R
          (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y))
        (CA * |μ - μ'|) := by
      have := wyl_bd_of_young (hX0' j)
      rwa [max_eq_left hCA_mu] at this
    have bCorrj : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R (fun τ y =>
          physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
            physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y))
        (CB * |μ - μ'|) := by
      have := wyl_bd_of_young (hCorr' j)
      rwa [max_eq_left hCB_mu] at this
    have bCutX0 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (fun q => Kcut * wardYoungRead ν R
          (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q)
        (Kcut * (CA * |μ - μ'|)) := by
      simpa [abs_of_nonneg hKcut0] using bX0.const_mul Kcut
    have bSum1 := bX0j.add bCutX0 hCA_mu (mul_nonneg hKcut0 hCA_mu)
    have bSum2 := bSum1.add bCorrj (add_nonneg hCA_mu (mul_nonneg hKcut0 hCA_mu)) hCB_mu
    refine ⟨hFm, ?_⟩
    have hdom : ∀ q : Chart,
        wardYoungRead ν R
          (fun τ y => physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y) q ≤
          (wardYoungRead ν R
            (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q +
            Kcut * wardYoungRead ν R
              (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q) +
          wardYoungRead ν R (fun τ y =>
            physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
              physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) q := by
      intro q
      by_cases hq : ν * q.1 ≤ 1
      · rcases le_or_gt q.1 0 with hs | hs
        · rw [wyl_youngRead_zero_of_nonpos _ hs]
          exact add_nonneg (add_nonneg (wyl_youngRead_nonneg _ _ _ q)
            (mul_nonneg hKcut0 (wyl_youngRead_nonneg _ _ _ q)))
            (wyl_youngRead_nonneg _ _ _ q)
        · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
            wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq]
          set τ := NearInst.chartTau R q
          set y := NearInst.chartY R q
          have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
          have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
          have hpd1 := (w3_wardX_diff_and_pd hχy hν hR hc hμ_gt hg τ hyU).2 j
          have hpd2 := (w3_wardX_diff_and_pd hχy hν hR hc hμ'_gt hg τ hyU).2 j
          have hnorm : ‖physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y‖ ≤
              (‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
                Kcut * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) +
                ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
                  physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ := by
            rw [hpd1, hpd2]
            have heq : (χy (ν * age R y) • physPd (wardX0 ν μ R c g τ) j y +
                  (deriv χy (ν * age R y) • ν • ageD R y) (coordinateVector j) •
                    wardX0 ν μ R c g τ y +
                  physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y) -
                (χy (ν * age R y) • physPd (wardX0 ν μ' R c g τ) j y +
                  (deriv χy (ν * age R y) • ν • ageD R y) (coordinateVector j) •
                    wardX0 ν μ' R c g τ y +
                  physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) =
                (χy (ν * age R y) •
                    (physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) +
                  (deriv χy (ν * age R y) • ν • ageD R y) (coordinateVector j) •
                    (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)) +
                  (physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
                    physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) := by
              rw [smul_sub, smul_sub]
              abel
            rw [heq]
            refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχy.range (ν * age R y)).1]
              exact mul_le_of_le_one_left (norm_nonneg _) (hχy.range (ν * age R y)).2
            · rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hKcut y j hy) (norm_nonneg _)
          have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
          calc (Real.sqrt q.1)⁻¹ *
                ‖physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y‖
              ≤ (Real.sqrt q.1)⁻¹ *
                  ((‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
                    Kcut * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) +
                    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
                      physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖) :=
                mul_le_mul_of_nonneg_left hnorm hinv
            _ = ((Real.sqrt q.1)⁻¹ *
                  ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
                  Kcut * ((Real.sqrt q.1)⁻¹ *
                    ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖)) +
                  (Real.sqrt q.1)⁻¹ *
                    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
                      physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ := by ring
      · have hqS : q ∉ wardYoungSet ν := hq
        have h0 : wardYoungRead ν R
            (fun τ y => physPd (wardX ν μ R c χy g τ) j y -
              physPd (wardX ν μ' R c χy g τ) j y) q = 0 := by
          unfold wardYoungRead
          rw [indicator_of_notMem hqS]
        rw [h0]
        exact add_nonneg (add_nonneg (wyl_youngRead_nonneg _ _ _ q)
          (mul_nonneg hKcut0 (wyl_youngRead_nonneg _ _ _ q)))
          (wyl_youngRead_nonneg _ _ _ q)
    refine (eLpNorm_mono_real (fun q => ?_)).trans
      (bSum2.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))
    rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
    exact hdom q

theorem wardDXSubYoungL2_proved : WardDXSubYoungL2 := by
  intro a b ν R c χy ha _ hχy hν hR hc
  obtain ⟨C, _, hC⟩ := wSub_wardXYoungL2 ν R c χy hχy hν hR hc
  refine ⟨C, fun μ hμ μ' hμ' g hg j => ?_⟩
  exact (hC μ μ' (by linarith [hμ.1]) (by linarith [hμ'.1]) g hg).2 j

end UnforcedLeray.Short.PartIIIb.Concrete
end
