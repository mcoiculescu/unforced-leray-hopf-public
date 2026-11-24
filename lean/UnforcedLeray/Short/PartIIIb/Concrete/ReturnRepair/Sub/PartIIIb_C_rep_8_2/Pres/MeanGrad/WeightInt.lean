import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The young-jet weight integral (`PartIII-b:C/rep/8/2/pres/5/5`)

Source of record: `the November 2 reference manuscript`
lines 2681-2688, 5203-5217, 5282-5284.  The weight `youngJetWeight ν ε` has `L^{22/3}` norm
`≤ C ν⁻¹^3 ε^{57/22}` for the chart measure `ringPhysμ ε⁻¹ c`.

Proof: the pointwise identity `(ε³s^{5/2}u^{-1/2})^{22/3} = ε^{22}s^{55/3}u^{-11/3}` (`u = 1+(εη)²`)
on the young range, the density `s^{-5/2}` of `ageμ` against `s^{55/3}`, the `q`-cell of length `c`,
and the `η`-integral `∫(1+(εη)²)^{-1} dη = π/ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The rpow identity on the young range. -/
theorem yw_rpow_eq {s ε u : ℝ} (hs : 0 < s) (hε : 0 < ε) (hu : 0 < u) :
    (ε ^ 3 * s ^ (5 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ))) ^ (22 / 3 : ℝ) =
      ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ) * u ^ (-(11 / 3 : ℝ)) := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (ε ^ 3 : ℝ) ^ (22 / 3 : ℝ) = ε ^ (22 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have h2 : (s ^ (5 / 2 : ℝ)) ^ (22 / 3 : ℝ) = s ^ (55 / 3 : ℝ) := by
    rw [← Real.rpow_mul hs.le]; norm_num
  have h3 : (u ^ (-(1 / 2 : ℝ))) ^ (22 / 3 : ℝ) = u ^ (-(11 / 3 : ℝ)) := by
    rw [← Real.rpow_mul hu.le]; norm_num
  rw [h1, h2, h3]

/-- The pointwise bound of the young weight to the `22/3` power. -/
theorem yw_pt_le {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) (p : Chart) :
    ‖youngJetWeight ν ε p‖ₑ ^ (22 / 3 : ℝ) ≤
      (Ioc (0 : ℝ) (1 / ν)).indicator
          (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) p.1 *
        ENNReal.ofReal ((1 + (ε * p.2.2) ^ 2) ^ (-(11 / 3 : ℝ))) := by
  unfold youngJetWeight
  by_cases h : 0 < p.1 ∧ p.1 ≤ 1 / ν
  · rw [if_pos h, Set.indicator_of_mem (show p.1 ∈ Ioc (0 : ℝ) (1 / ν) from ⟨h.1, h.2⟩)]
    have hp1 : 0 < p.1 := h.1
    have hu : 0 < 1 + (ε * p.2.2) ^ 2 := by positivity
    have hw : 0 ≤ ε ^ 3 * p.1 ^ (5 / 2 : ℝ) * (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ)) := by
      positivity
    rw [Real.enorm_eq_ofReal hw, ENNReal.ofReal_rpow_of_nonneg hw (by norm_num),
      yw_rpow_eq h.1 hε hu,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε ^ (22 : ℝ) * p.1 ^ (55 / 3 : ℝ))]
  · rw [if_neg h]
    simp only [norm_zero, enorm_zero]
    exact le_trans (le_of_eq (ENNReal.zero_rpow_of_pos (by norm_num))) zero_le

/-- The density `s^{-5/2}` times the `s^{55/3}` profile on the young range. -/
theorem yw_dens_le {ν ε s : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hs : 0 < s) (hsν : s ≤ 1 / ν) :
    ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ)) ≤
      ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s ^ (-5 / 2 : ℝ)),
    ENNReal.ofReal_le_ofReal_iff (by positivity)]
  have e : s ^ (-5 / 2 : ℝ) * (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ)) =
      ε ^ (22 : ℝ) * s ^ (95 / 6 : ℝ) := by
    have h : s ^ (-5 / 2 : ℝ) * s ^ (55 / 3 : ℝ) = s ^ (95 / 6 : ℝ) := by
      rw [← Real.rpow_add hs]; norm_num
    rw [← h]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hsν (by norm_num)) (by positivity)

/-- The measurable `s`-profile. -/
theorem yw_F_meas (ν ε : ℝ) :
    Measurable (fun s : ℝ =>
      (Ioc (0 : ℝ) (1 / ν)).indicator
        (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) s) :=
  Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop)) measurableSet_Ioc

/-- The `s`-integral against the density `s^{-5/2}` on `(0,∞)`. -/
theorem yw_sint {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) :
    ∫⁻ s, (Ioc (0 : ℝ) (1 / ν)).indicator
        (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) s
        ∂((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))) ≤
      ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) * ENNReal.ofReal (1 / ν) := by
  have hd : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (yw_F_meas ν ε)]
  calc _ ≤ ∫⁻ a in Ioi (0 : ℝ), (Ioc (0 : ℝ) (1 / ν)).indicator
          (fun _ => ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ))) a := by
        apply setLIntegral_mono (measurable_const.indicator measurableSet_Ioc)
        intro a ha
        simp only [Pi.mul_apply]
        by_cases hI : a ∈ Ioc (0 : ℝ) (1 / ν)
        · rw [Set.indicator_of_mem hI, Set.indicator_of_mem hI]
          exact yw_dens_le hν hε (Set.mem_Ioi.mp ha) hI.2
        · have hz1 : (Ioc (0 : ℝ) (1 / ν)).indicator
              (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) a = 0 := by
            rw [Set.indicator_apply, if_neg hI]
          have hz2 : (Ioc (0 : ℝ) (1 / ν)).indicator
              (fun _ => ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ))) a = 0 := by
            rw [Set.indicator_apply, if_neg hI]
          simp only [hz1, hz2, mul_zero, le_refl]
    _ ≤ ∫⁻ a, (Ioc (0 : ℝ) (1 / ν)).indicator
          (fun _ => ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ))) a := by
        exact setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) * volume (Ioc (0 : ℝ) (1 / ν)) :=
        lintegral_indicator_const measurableSet_Ioc _
    _ = _ := by rw [Real.volume_Ioc, sub_zero]

/-- The `η`-integral `∫(1+(εη)²)^{-11/3} dη ≤ π/ε`. -/
theorem yw_eta_le {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ y, ENNReal.ofReal ((1 + (ε * y) ^ 2) ^ (-(11 / 3 : ℝ))) ≤
      ENNReal.ofReal (ε⁻¹ * Real.pi) := by
  have hI : Integrable (fun y : ℝ => (1 + (ε * y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hε.ne'
  have hnn : ∀ y : ℝ, 0 ≤ (1 + (ε * y) ^ 2)⁻¹ := fun y => by positivity
  calc ∫⁻ y, ENNReal.ofReal ((1 + (ε * y) ^ 2) ^ (-(11 / 3 : ℝ)))
      ≤ ∫⁻ y, ENNReal.ofReal ((1 + (ε * y) ^ 2)⁻¹) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le
        · have : 0 ≤ (ε * y) ^ 2 := by positivity
          linarith
        · norm_num
    _ = ENNReal.ofReal (∫ y, (1 + (ε * y) ^ 2)⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)).symm
    _ = ENNReal.ofReal (ε⁻¹ * Real.pi) := by
        congr 1
        have h := MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) ε
        rw [h, integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos (inv_pos.mpr hε)]

/-- The `η`-cell integral over `cell c = Ico × univ`. -/
theorem yw_cell_le {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))) ≤
      ENNReal.ofReal c * ENNReal.ofReal (ε⁻¹ * Real.pi) := by
  have hm : Measurable fun z : ℝ × ℝ => ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  unfold Cyl.cell
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
  have hinner : ∀ x : ℝ, ∫⁻ y in (univ : Set ℝ),
      ENNReal.ofReal ((1 + (ε * (x, y).2) ^ 2) ^ (-(11 / 3 : ℝ))) ≤
        ENNReal.ofReal (ε⁻¹ * Real.pi) := by
    intro x
    rw [Measure.restrict_univ]
    exact yw_eta_le hε
  have hc2 : c / 2 - -c / 2 = c := by ring
  calc ∫⁻ x in Ico (-c / 2) (c / 2), ∫⁻ y in (univ : Set ℝ),
          ENNReal.ofReal ((1 + (ε * (x, y).2) ^ 2) ^ (-(11 / 3 : ℝ)))
      ≤ ∫⁻ _x in Ico (-c / 2) (c / 2), ENNReal.ofReal (ε⁻¹ * Real.pi) :=
        setLIntegral_mono measurable_const (fun x _ => hinner x)
    _ = ENNReal.ofReal c * ENNReal.ofReal (ε⁻¹ * Real.pi) := by
        rw [setLIntegral_const, Real.volume_Ico, hc2, mul_comm]

/-- The cell-averaged `η`-integral with the normalizing factor `c⁻¹`. -/
theorem yw_avg_le {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∫⁻ z, ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))) ∂(Cyl.avgμ c) ≤
      ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (ε⁻¹ * Real.pi)) := by
  rw [Cyl.avgμ, Cyl.cellμ, lintegral_smul_measure, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (yw_cell_le hε hc) zero_le

/-- The real identity for the bound. -/
theorem yw_real_eq {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) :
    Real.pi * (ε⁻¹) ^ 2 * (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ) * (1 / ν)) * (ε⁻¹ * Real.pi) =
      Real.pi ^ 2 * ε ^ (19 : ℝ) * (1 / ν) ^ (101 / 6 : ℝ) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have e1 : ε ^ (22 : ℝ) = ε ^ (19 : ℝ) * ε ^ 3 := by
    rw [show (22 : ℝ) = 19 + 3 by norm_num, Real.rpow_add hε,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : (1 / ν) ^ (95 / 6 : ℝ) * (1 / ν) = (1 / ν) ^ (101 / 6 : ℝ) := by
    rw [← Real.rpow_add_one (by positivity)]; norm_num
  rw [e1, ← e2]
  field_simp

/-- The final `L^{22/3}` bound on the young weight. -/
theorem yw_main {ν ε c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hc : 0 < c) :
    eLpNorm (youngJetWeight ν ε) (22 / 3) (ringPhysμ ε⁻¹ c) ≤
      ENNReal.ofReal ((Real.pi ^ 2) ^ (3 / 22 : ℝ) * ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ)) := by
  have hp : ENNReal.toReal (22 / 3 : ℝ≥0∞) = 22 / 3 := by
    rw [ENNReal.toReal_div]; norm_num
  have hpt : (22 / 3 : ℝ≥0∞) ≠ ⊤ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.2 (by norm_num))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) hpt, hp]
  set J := ∫⁻ x, ‖youngJetWeight ν ε x‖ₑ ^ (22 / 3 : ℝ) ∂ringPhysμ ε⁻¹ c with hJ
  set Q := Real.pi * (ε⁻¹) ^ 2 * (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ) * (1 / ν)) *
    (ε⁻¹ * Real.pi) with hQ
  have hF := yw_F_meas ν ε
  have hG : Measurable fun z : ℝ × ℝ =>
      ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hJle : J ≤ ENNReal.ofReal Q := by
    rw [hJ, ringPhysμ, lintegral_smul_measure, smul_eq_mul]
    unfold ageμ
    have hprod := lintegral_prod_mul (μ := (volume.restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))) (ν := Cyl.avgμ c)
        (f := fun s => (Ioc (0 : ℝ) (1 / ν)).indicator
          (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) s)
        (g := fun z : ℝ × ℝ => ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))))
        hF.aemeasurable hG.aemeasurable
    calc ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
          ∫⁻ x, ‖youngJetWeight ν ε x‖ₑ ^ (22 / 3 : ℝ)
            ∂((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))).prod
              (Cyl.avgμ c)
        ≤ ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
          ∫⁻ x, (Ioc (0 : ℝ) (1 / ν)).indicator
              (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) x.1 *
            ENNReal.ofReal ((1 + (ε * x.2.2) ^ 2) ^ (-(11 / 3 : ℝ)))
            ∂((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))).prod
              (Cyl.avgμ c) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact lintegral_mono fun p => yw_pt_le hν hε p
      _ = ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
          ((∫⁻ s, (Ioc (0 : ℝ) (1 / ν)).indicator
              (fun s => ENNReal.ofReal (ε ^ (22 : ℝ) * s ^ (55 / 3 : ℝ))) s
              ∂((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)))) *
            ∫⁻ z, ENNReal.ofReal ((1 + (ε * z.2) ^ 2) ^ (-(11 / 3 : ℝ))) ∂(Cyl.avgμ c)) := by
          congr 1
      _ ≤ ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
          ((ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) * ENNReal.ofReal (1 / ν)) *
            (ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (ε⁻¹ * Real.pi)))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (yw_sint hν hε) (yw_avg_le hε hc) zero_le zero_le) zero_le
      _ = ENNReal.ofReal Q := by
          have e1 : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
              ENNReal.ofReal_one]
          have e3 : ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
              ((ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) * ENNReal.ofReal (1 / ν)) *
                (ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (ε⁻¹ * Real.pi)))) =
              ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
                ENNReal.ofReal (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) *
                ENNReal.ofReal (1 / ν) * ENNReal.ofReal (ε⁻¹ * Real.pi) *
                (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) := by ring
          have h1 : (0 : ℝ) ≤ Real.pi * (ε⁻¹) ^ 2 := by positivity
          have h2 : (0 : ℝ) ≤ Real.pi * (ε⁻¹) ^ 2 * (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) := by
            positivity
          have h3 : (0 : ℝ) ≤ Real.pi * (ε⁻¹) ^ 2 * (ε ^ (22 : ℝ) * (1 / ν) ^ (95 / 6 : ℝ)) *
              (1 / ν) := by positivity
          rw [e3, e1, mul_one, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
            ← ENNReal.ofReal_mul h3, hQ]
          congr 1
          ring
  have hQeq : Q = Real.pi ^ 2 * ε ^ (19 : ℝ) * (1 / ν) ^ (101 / 6 : ℝ) := by
    rw [hQ]; exact yw_real_eq hν hε
  have hQnn : 0 ≤ Q := by rw [hQeq]; positivity
  have hνb : (1 / ν) ^ (101 / 44 : ℝ) ≤ ν⁻¹ ^ 3 := by
    have h1 : (1 : ℝ) ≤ 1 / ν := one_le_one_div hν hν1
    calc (1 / ν) ^ (101 / 44 : ℝ) ≤ (1 / ν) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = ν⁻¹ ^ 3 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  calc J ^ (1 / (22 / 3 : ℝ)) ≤ (ENNReal.ofReal Q) ^ (1 / (22 / 3 : ℝ)) :=
        ENNReal.rpow_le_rpow hJle (by norm_num)
    _ = ENNReal.ofReal (Q ^ (1 / (22 / 3 : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg hQnn (by norm_num)
    _ ≤ ENNReal.ofReal ((Real.pi ^ 2) ^ (3 / 22 : ℝ) * ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hQeq, show (1 : ℝ) / (22 / 3) = 3 / 22 by norm_num,
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hε.le, ← Real.rpow_mul (by positivity),
          show (19 : ℝ) * (3 / 22) = 57 / 22 by norm_num,
          show (101 / 6 : ℝ) * (3 / 22) = 101 / 44 by norm_num]
        calc _ = ((Real.pi ^ 2) ^ (3 / 22 : ℝ) * ε ^ (57 / 22 : ℝ)) * (1 / ν) ^ (101 / 44 : ℝ) := by
              ring
          _ ≤ ((Real.pi ^ 2) ^ (3 / 22 : ℝ) * ε ^ (57 / 22 : ℝ)) * ν⁻¹ ^ 3 :=
              mul_le_mul_of_nonneg_left hνb (by positivity)
          _ = _ := by ring

/-- **The young-jet weight integral** (`PartIII-b:C/rep/8/2/pres/5/5`). -/
theorem youngJetWeightInt : YoungJetWeightInt :=
  ⟨(Real.pi ^ 2) ^ (3 / 22 : ℝ), 3, fun _ν _ε _c hν hν1 hε hc => yw_main hν hν1 hε hc⟩

end UnforcedLeray.Short.PartIIIb.Concrete
