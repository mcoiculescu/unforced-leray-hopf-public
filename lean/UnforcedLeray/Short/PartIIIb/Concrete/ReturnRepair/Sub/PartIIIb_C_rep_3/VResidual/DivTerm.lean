import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound.Young
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2.ChartPhaseAvg

/-!
# `L²(srcMeasure)` bound for the transport term `vrDiv` (`2V·∇Y`) (`PartIII-b:C/rep/3/2`)

Source: `the November 2 reference manuscript`, 5225-5232.
Uses the young support of `Y` (`wyl_Y_zero_nhds`), the phase average (`chartPhaseAvg`), the
age-surface bound on `DY`, `vEtaSup` on `V`, and `∫_0^{1/ν} s^{34/11} ds ≤ ν^{-5}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem vr_rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- On `νs > 1`, `coefOf R (vrDiv V Y)` vanishes at the chart point `p`. -/
theorem vr_coefOf_div_zero_of_lt {ν μ R c : ℝ} {χy : ℝ → ℝ} (hν : 0 < ν) (hR : 0 < R)
    (hχy : IsYoungCutoff χy) (V : ℝ → SpatialField) (g : Chart → Ten3) {p : Chart}
    (hp : 1 < ν * p.1) :
    coefOf R (vrDiv V (wardY ν μ R c χy g)) p = 0 := by
  have hev := wyl_Y_zero_nhds (μ := μ) (c := c) hν hR hχy g hp (NearInst.chartTau R p)
  have hf : fderiv ℝ (wardY ν μ R c χy g (NearInst.chartTau R p)) (NearInst.chartY R p) = 0 := by
    rw [hev.fderiv_eq, fderiv_const_apply]
  have h0 : vrDiv V (wardY ν μ R c χy g) (NearInst.chartTau R p) (NearInst.chartY R p) = 0 := by
    simp [vrDiv, hf]
  simp [coefOf, h0]

/-- Pointwise bound on `‖coefOf R (vrDiv V Y) (s, (q, η))‖ₑ ^ 2` for `s > 0`. -/
theorem vr_coefOf_div_sq_le (R : ℝ) (V Y : ℝ → Space → Space) {s : ℝ} (hs : 0 < s) (q η : ℝ) :
    ‖coefOf R (vrDiv V Y) (s, (q, η))‖ₑ ^ 2 ≤
      ENNReal.ofReal 4 *
        ENNReal.ofReal ((Real.sqrt s)⁻¹ *
          ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖) ^ (2 : ℝ) *
        ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) (NearInst.chartY R (s, (0, η)))‖ ^
          (2 : ℝ) := by
  set p : Chart := (s, (q, η))
  have hy : NearInst.chartY R p = NearInst.chartY R (s, (0, η)) := rfl
  have hτ : NearInst.chartTau R p = 2 * q / R + Real.log s := rfl
  have h1 := wyl_coefOf_norm_le R (vrDiv V Y) p
  have h2 : ‖vrDiv V Y (NearInst.chartTau R p) (NearInst.chartY R p)‖ ≤
      2 * (‖fderiv ℝ (Y (NearInst.chartTau R p)) (NearInst.chartY R p)‖ *
        ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖) := by
    unfold vrDiv
    rw [norm_smul, Real.norm_eq_abs, abs_two]
    exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
  have h3 : ‖coefOf R (vrDiv V Y) p‖ ≤
      2 * ((Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖) *
        ‖fderiv ℝ (Y (2 * q / R + Real.log s)) (NearInst.chartY R (s, (0, η)))‖ := by
    calc ‖coefOf R (vrDiv V Y) p‖
        ≤ (Real.sqrt s)⁻¹ * ‖vrDiv V Y (NearInst.chartTau R p) (NearInst.chartY R p)‖ := h1
      _ ≤ (Real.sqrt s)⁻¹ *
            (2 * (‖fderiv ℝ (Y (NearInst.chartTau R p)) (NearInst.chartY R p)‖ *
              ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (Real.sqrt_nonneg _))
      _ = 2 * ((Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖) *
            ‖fderiv ℝ (Y (2 * q / R + Real.log s)) (NearInst.chartY R (s, (0, η)))‖ := by
          rw [hτ, hy]; ring
  have hVnn : 0 ≤ (Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖ :=
    mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (norm_nonneg _)
  rw [← ofReal_norm, ENNReal.rpow_two, ENNReal.rpow_two]
  calc ENNReal.ofReal ‖coefOf R (vrDiv V Y) p‖ ^ 2
      ≤ ENNReal.ofReal (2 * ((Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖) *
          ‖fderiv ℝ (Y (2 * q / R + Real.log s)) (NearInst.chartY R (s, (0, η)))‖) ^ 2 :=
        ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal h3)
    _ = ENNReal.ofReal 4 *
          ENNReal.ofReal ((Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R p) (NearInst.chartY R p)‖) ^ 2 *
          ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) (NearInst.chartY R (s, (0, η)))‖ ^
            2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          mul_pow, mul_pow, ← ENNReal.ofReal_pow (by norm_num)]
        norm_num

/-- Age power bound: for `0 < ν ≤ 1` and `0 < s ≤ ν⁻¹`,
`s ^ (-3 / 2 : ℝ) * (s ^ (101 / 44 : ℝ)) ^ 2 ≤ ν⁻¹ ^ 4`. -/
theorem vr_age_pow_le {ν s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 0 < s) (hνs : ν * s ≤ 1) :
    s ^ (-3 / 2 : ℝ) * (s ^ (101 / 44 : ℝ)) ^ 2 ≤ ν⁻¹ ^ 4 := by
  have hsle : s ≤ ν⁻¹ := by
    rw [← mul_le_mul_iff_right₀ hν, mul_inv_cancel₀ hν.ne']
    exact hνs
  have hνinv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have h1 : s ^ (-3 / 2 : ℝ) * (s ^ (101 / 44 : ℝ)) ^ 2 = s ^ (34 / 11 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (101 / 44 : ℝ)) 2, ← Real.rpow_mul hs.le,
      ← Real.rpow_add hs]
    norm_num
  rw [h1]
  calc s ^ (34 / 11 : ℝ)
      ≤ (ν⁻¹) ^ (34 / 11 : ℝ) := Real.rpow_le_rpow hs.le hsle (by norm_num)
    _ ≤ (ν⁻¹) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hνinv1 (by norm_num)
    _ = ν⁻¹ ^ 4 := by norm_num

/-- `L²(srcMeasure)` bound for `vrDiv` at one regime. -/
theorem vr_div_bound_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hν1 : L.ν ≤ 1) (hχy : IsYoungCutoff K.χy) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    {k₁ k₂ : ℕ} {w : LVel Pl L}
    (hFr : phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) ≠ ⊤)
    (hDivm : Measurable (coefOf L.ε⁻¹ (vrDiv L.V (repY Pl K L μ w))))
    (hDYm : ∀ y : Space, y ∉ axis → Measurable fun τ : ℝ => ‖fderiv ℝ (repY Pl K L μ w τ) y‖)
    (hA1 : ∀ s : ℝ, 0 < s → L.ν * s ≤ 1 →
      ageSurfL2 (2 * L.ε * cOf L.ν) L.ε⁻¹ s (fun τ y => ‖fderiv ℝ (repY Pl K L μ w τ) y‖) ≤
        ENNReal.ofReal (C₁ * L.ν⁻¹ ^ k₁ * L.ε ^ (101 / 22 : ℝ) * s ^ (101 / 44 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w))
    (hVeta : ∀ s : ℝ, 0 < s → vEtaSup L.ε⁻¹ (cOf L.ν) L.V s ≤ ENNReal.ofReal (C₂ * L.ν⁻¹ ^ k₂)) :
    eLpNorm (coefOf L.ε⁻¹ (vrDiv L.V (repY Pl K L μ w))) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) *
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  set R : ℝ := L.ε⁻¹
  have hR : 0 < R := inv_pos.2 hε
  set c : ℝ := cOf L.ν
  have hc : 0 < c := cOf_pos hν
  set P : ℝ := 2 * L.ε * c
  have hP : 0 < P := by positivity
  have hPeq : 2 * c / R = P := by
    unfold R P
    rw [div_inv_eq_mul]
    ring
  set Y := repY Pl K L μ w
  set Fr := phaseL2Lr P (22 / 19) (repStressPhys Pl K L w)
  set A₁ : ℝ := C₁ * L.ν⁻¹ ^ k₁ * L.ε ^ (101 / 22 : ℝ)
  have hA₁0 : 0 ≤ A₁ := by positivity
  set A₂ : ℝ := C₂ * L.ν⁻¹ ^ k₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal A₁ * Fr
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFr
  set Ψ : Chart → ℝ≥0∞ := fun p => ‖coefOf R (vrDiv L.V Y) p‖ₑ ^ 2
  have hΨm : Measurable Ψ := hDivm.enorm.pow_const 2
  -- Bound the `(q, η)` slice at age `s > 0`
  have hslice : ∀ s ∈ Ioi (0 : ℝ),
      ∫⁻ x in qCell c, ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, x) ≤
        (Ioc (0 : ℝ) L.ν⁻¹).indicator
          (fun _ => ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2) s := by
    intro s hs
    have hs' : 0 < s := hs
    by_cases hνs : L.ν * s ≤ 1
    · have hsle : s ≤ L.ν⁻¹ := by
        rw [← mul_le_mul_iff_right₀ hν, mul_inv_cancel₀ hν.ne']
        exact hνs
      have hsIoc : s ∈ Ioc (0 : ℝ) L.ν⁻¹ := ⟨hs', hsle⟩
      rw [indicator_of_mem hsIoc, qCell_eq_cell]
      unfold Cyl.cell
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod_symm]
      · set y₀ : Space := NearInst.chartY R (s, (0, 0))
        -- For each `η`, bound the `q`-cell integral
        have hη_bound : ∀ η : ℝ,
            ∫⁻ q in Ico (-c / 2) (c / 2),
                ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, (q, η)) ≤
              (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2) *
                (essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
                  ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
                  (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) := by
          intro η
          set y_sη : Space := NearInst.chartY R (s, (0, η))
          have hy_ax : y_sη ∉ axis :=
            wo_chartY_not_mem_axis (p := (s, (0, η))) hR.ne' hs'
          have hage_y : age R y_sη = s := wyl_age_chartY (q := (s, (0, η))) hR hs'
          set Mq : ℝ≥0∞ := essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
              ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
            (volume.restrict (Ico (-(c / 2)) (c / 2)))
          have hIco_eq : Ico (-c / 2) (c / 2) = Ico (-(c / 2)) (c / 2) := by
            rw [neg_div]
          have hae_q : ∀ᵐ q ∂(volume.restrict (Ico (-c / 2) (c / 2))),
              ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, (q, η)) ≤
                (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                  (ENNReal.ofReal c⁻¹ *
                    ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) y_sη‖ ^ (2 : ℝ)) := by
            rw [hIco_eq]
            filter_upwards [ENNReal.ae_le_essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
              ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))] with q hq
            have hpt := vr_coefOf_div_sq_le R L.V Y hs' q η
            have hMq : ENNReal.ofReal ((Real.sqrt s)⁻¹ *
                ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖) ^ (2 : ℝ) ≤
                Mq ^ (2 : ℝ) := ENNReal.rpow_le_rpow hq (by norm_num)
            have hcoeff : ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal 4 =
                ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal c⁻¹ := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1; ring
            calc ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, (q, η))
                ≤ ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) *
                    (ENNReal.ofReal 4 *
                      ENNReal.ofReal ((Real.sqrt s)⁻¹ *
                        ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖) ^
                        (2 : ℝ) *
                      ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) y_sη‖ ^ (2 : ℝ)) :=
                  mul_le_mul' le_rfl hpt
              _ ≤ ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) *
                    (ENNReal.ofReal 4 * Mq ^ (2 : ℝ) *
                      ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) y_sη‖ ^ (2 : ℝ)) := by
                  gcongr
              _ = (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                    (ENNReal.ofReal c⁻¹ *
                      ENNReal.ofReal ‖fderiv ℝ (Y (2 * q / R + Real.log s)) y_sη‖ ^ (2 : ℝ)) := by
                  rw [← mul_assoc, ← mul_assoc, hcoeff]
                  ring
          set H : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal ‖fderiv ℝ (Y τ) y_sη‖ ^ (2 : ℝ)
          have hHm : Measurable H := ((hDYm y_sη hy_ax).ennreal_ofReal).pow_const (2 : ℝ)
          have hHper : ∀ τ, H (τ + 2 * c / R) = H τ := by
            intro τ
            have hYp := vr_wardY_periodic L.ν μ R c K.χy (repSrcTen Pl K L w) τ
            dsimp only [H, Y, repY, R, c] at hYp ⊢
            rw [hYp]
          have havg := chartPhaseAvg R c hR hc H hHm hHper (Real.log s)
          have hsup_le : ∀ τ : ℝ, H τ ≤ ageSurfSup R s (fun y => ‖fderiv ℝ (Y τ) y‖) ^ (2 : ℝ) := by
            intro τ
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            exact le_iSup₂ (f := fun (y : Space) (_ : age R y = s) =>
              ENNReal.ofReal ‖fderiv ℝ (Y τ) y‖) y_sη hage_y
          have hP_int : (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), H τ ≤
              ENNReal.ofReal (s ^ (101 / 44 : ℝ)) ^ 2 * B ^ 2 := by
            rw [hPeq, ← ENNReal.ofReal_inv_of_pos hP]
            have h1 : ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc 0 P, H τ ≤
                ageSurfL2 P R s (fun τ y => ‖fderiv ℝ (Y τ) y‖) ^ 2 := by
              rw [ageSurfL2, vr_rpow_half_sq]
              exact mul_le_mul' le_rfl (lintegral_mono hsup_le)
            have h2 := ENNReal.pow_le_pow_left (n := 2) (hA1 s hs' hνs)
            have h3 : (ENNReal.ofReal (A₁ * s ^ (101 / 44 : ℝ)) * Fr) ^ 2 =
                ENNReal.ofReal (s ^ (101 / 44 : ℝ)) ^ 2 * B ^ 2 := by
              unfold B
              rw [ENNReal.ofReal_mul hA₁0, mul_pow, mul_pow]
              ring
            exact h1.trans (h2.trans (le_of_eq h3))
          have hage_pow : ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) *
              ENNReal.ofReal (s ^ (101 / 44 : ℝ)) ^ 2 ≤
              ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) := by
            rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hs'.le _),
              ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hp := vr_age_pow_le hν hν1 hs' hνs
            nlinarith
          have hMqt : ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ) *
              (ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), H (2 * q / R + Real.log s)) =
              ∫⁻ q in Ico (-c / 2) (c / 2),
                (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                  (ENNReal.ofReal c⁻¹ * H (2 * q / R + Real.log s)) := by
            have hHq_m : Measurable fun q : ℝ => H (2 * q / R + Real.log s) :=
              hHm.comp (((measurable_id.const_mul 2).div_const R).add_const _)
            rw [← lintegral_const_mul _ hHq_m, ← lintegral_const_mul _ (hHq_m.const_mul _)]
          calc ∫⁻ q in Ico (-c / 2) (c / 2),
                ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, (q, η))
              ≤ ∫⁻ q in Ico (-c / 2) (c / 2),
                  (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                    (ENNReal.ofReal c⁻¹ * H (2 * q / R + Real.log s)) :=
                lintegral_mono_ae hae_q
            _ = (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                  (ENNReal.ofReal c⁻¹ *
                    ∫⁻ q in Ico (-c / 2) (c / 2), H (2 * q / R + Real.log s)) :=
                hMqt.symm
            _ = (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                  ((ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), H τ) := by
                rw [havg]
            _ ≤ (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) * Mq ^ (2 : ℝ)) *
                  (ENNReal.ofReal (s ^ (101 / 44 : ℝ)) ^ 2 * B ^ 2) :=
                mul_le_mul' le_rfl hP_int
            _ = (ENNReal.ofReal (4 * s ^ (-3 / 2 : ℝ)) *
                  ENNReal.ofReal (s ^ (101 / 44 : ℝ)) ^ 2) * B ^ 2 * Mq ^ (2 : ℝ) := by
                ring
            _ ≤ (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2) * Mq ^ (2 : ℝ) := by
                gcongr
        have hVeta_sq : ∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
            ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
            (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) ≤
            ENNReal.ofReal (A₂ ^ 2) := by
          have h1 := ENNReal.pow_le_pow_left (n := 2) (hVeta s hs')
          rw [vEtaSup, vr_rpow_half_sq, ← ENNReal.ofReal_pow hA₂0] at h1
          exact h1
        have hB4t : ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2 ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hBt)
        have h4A₂ : ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) =
            ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * ENNReal.ofReal (A₂ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
        calc ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
              ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, (q, η))
            ≤ ∫⁻ η : ℝ, (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2) *
                (essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
                  ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
                  (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) :=
              lintegral_mono hη_bound
          _ = (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2) *
                ∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
                  ‖L.V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
                  (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) :=
              lintegral_const_mul' _ _ hB4t
          _ ≤ (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4) * B ^ 2) * ENNReal.ofReal (A₂ ^ 2) :=
              mul_le_mul' le_rfl hVeta_sq
          _ = ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2 := by
              rw [h4A₂]
              ring
      · exact (measurable_const.mul (hΨm.comp measurable_prodMk_left)).aemeasurable
    · have hlt : 1 < L.ν * s := not_le.1 hνs
      have h0 : ∀ x : ℝ × ℝ, ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, x) = 0 := by
        intro x
        have hz := vr_coefOf_div_zero_of_lt (μ := μ) (c := c) hν hR hχy L.V
          (repSrcTen Pl K L w) (p := (s, x)) hlt
        dsimp only [Ψ, Y, repY, R, c] at hz ⊢
        simp [hz]
      calc ∫⁻ x in qCell c, ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, x)
          ≤ ∫⁻ _ in qCell c, 0 := lintegral_mono fun x => by rw [h0 x]
        _ = 0 := lintegral_zero
        _ ≤ _ := zero_le
  -- Integrate over `s ∈ Ioi 0`
  have hint_s : ∫⁻ p, Ψ p ∂(srcMeasure c) ≤
      (ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) * Fr) ^ 2 := by
    rw [srcMeasure, lintegral_smul_measure, smul_eq_mul, lintegral_ageμ hc _ hΨm,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
    · have hs_int : ∫⁻ s in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) L.ν⁻¹).indicator
            (fun _ => ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2) s =
          (ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2) * ENNReal.ofReal L.ν⁻¹ := by
        rw [setLIntegral_indicator measurableSet_Ioc, setLIntegral_const,
          inter_eq_self_of_subset_left Ioc_subset_Ioi_self, Real.volume_Ioc, sub_zero]
      have hpi4 : ENNReal.ofReal Real.pi ≤ ENNReal.ofReal 4 :=
        ENNReal.ofReal_le_ofReal Real.pi_le_four
      have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
      have hreal : 4 * (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * L.ν⁻¹ * A₁ ^ 2 ≤
          (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) ^ 2 := by
        have h56 : L.ν⁻¹ ^ 5 ≤ L.ν⁻¹ ^ 6 := pow_le_pow_right₀ hνinv1 (by norm_num)
        have h1 : 4 * (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * L.ν⁻¹ * A₁ ^ 2 =
            (16 * A₁ ^ 2 * A₂ ^ 2) * L.ν⁻¹ ^ 5 := by ring
        have h2 : (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) ^ 2 =
            (16 * A₁ ^ 2 * A₂ ^ 2) * L.ν⁻¹ ^ 6 := by
          unfold A₁ A₂
          rw [pow_add, pow_add]
          ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_left h56 (by positivity)
      have hsplit : ENNReal.ofReal (4 * (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * L.ν⁻¹ * A₁ ^ 2) =
          ENNReal.ofReal 4 * ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) *
            ENNReal.ofReal L.ν⁻¹ * ENNReal.ofReal A₁ ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_pow hA₁0]
      calc ENNReal.ofReal Real.pi *
            ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in qCell c,
              ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * Ψ (s, x)
          ≤ ENNReal.ofReal 4 *
              ∫⁻ s in Ioi (0 : ℝ),
                (Ioc (0 : ℝ) L.ν⁻¹).indicator
                  (fun _ => ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2) s :=
            mul_le_mul' hpi4 (setLIntegral_mono
              ((measurable_const.indicator measurableSet_Ioc)) hslice)
        _ = ENNReal.ofReal 4 *
              ((ENNReal.ofReal (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * B ^ 2) * ENNReal.ofReal L.ν⁻¹) := by
            rw [hs_int]
        _ = ENNReal.ofReal (4 * (4 * L.ν⁻¹ ^ 4 * A₂ ^ 2) * L.ν⁻¹ * A₁ ^ 2) * Fr ^ 2 := by
            unfold B
            rw [hsplit, mul_pow]
            ring
        _ ≤ ENNReal.ofReal ((4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) ^ 2) *
              Fr ^ 2 :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
        _ = (ENNReal.ofReal (4 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂ + 3) * L.ε ^ (101 / 22 : ℝ)) *
              Fr) ^ 2 := by
            rw [ENNReal.ofReal_pow (by positivity), mul_pow]
    · exact ((ENNReal.measurable_ofReal.comp
        (by fun_prop : Measurable fun p : Chart => c⁻¹ * p.1 ^ (-3 / 2 : ℝ))).mul hΨm).aemeasurable
  have hX : eLpNorm (coefOf R (vrDiv L.V Y)) 2 (srcMeasure c) ^ 2 =
      ∫⁻ p, Ψ p ∂(srcMeasure c) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := coefOf R (vrDiv L.V Y)) (μ := srcMeasure c)
      (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using h
  rw [← hX] at hint_s
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hint_s

end UnforcedLeray.Short.PartIIIb.Concrete
