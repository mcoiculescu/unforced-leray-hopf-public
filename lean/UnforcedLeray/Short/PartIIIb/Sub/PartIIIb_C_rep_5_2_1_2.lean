import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org

/-!
# `PartIII-b:C/rep/5/2/1/2`: `ChartPhysL2` from three change-of-variables lemmas

Source `the November 2 reference manuscript` 2683-2689
(`R⁻¹‖𝒩_v b‖_{Y_2} = √π‖b‖_H`): `c⁻¹dq = dτ/P` (phase average), cylindrical coordinates
`dy = 2πr dr dz`, and `π s^{-5/2} ds dη = R^{-2}·2πr dr dz` for `r = R/√s`, `z = η/√s`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Phase average (step (i)): for a measurable `2c/R`-periodic `H`, as `q` runs over the cell
`[-c/2, c/2)`, `τ = 2q/R + a` sweeps one period, so `c⁻¹∫ H(2q/R + a) dq = P⁻¹∫_{(0,P]} H`,
`P = 2c/R` (`c⁻¹dq = dτ/P`). -/
def ChartPhaseAvg : Prop :=
  ∀ R c : ℝ, 0 < R → 0 < c → ∀ H : ℝ → ℝ≥0∞, Measurable H → (∀ τ, H (τ + 2 * c / R) = H τ) →
    ∀ a : ℝ, ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), H (2 * q / R + a) =
      (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), H τ

/-- Cylindrical coordinates (step (ii)): for measurable axisymmetric `Φ` on `Space`,
`∫ Φ dy = ∫∫ 2πr Φ(r,0,z) dr dz` (`ℝ³ = ℝ²×ℝ`, polar coordinates on `ℝ²`). -/
def CylPolar : Prop :=
  ∀ Φ : Space → ℝ≥0∞, Measurable Φ →
    (∀ y y' : Space, y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 → Φ y' = Φ y) →
    ∫⁻ y, Φ y = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ,
      ENNReal.ofReal (2 * Real.pi * r) * Φ (WithLp.toLp 2 ![r, 0, z])

/-- Chart Jacobian (step (iii)), source 2683-2689: under `r = R/√s`, `z = η/√s`,
`π s^{-5/2} ds dη = R^{-2}·2πr dr dz`. -/
def ChartJacobian : Prop :=
  ∀ R : ℝ, 0 < R → ∀ Ψ : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry Ψ) →
    ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (Real.pi * s ^ (-5 / 2 : ℝ)) *
        Ψ (R / Real.sqrt s) (η / Real.sqrt s) =
      ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ,
        ENNReal.ofReal (2 * Real.pi * r) * Ψ r z

theorem chartPhysL2_of (h1 : ChartPhaseAvg) (h2 : CylPolar) (h3 : ChartJacobian) :
    ChartPhysL2 := by
  intro R c hR hc G hGm hper hax
  have hP : 0 < 2 * c / R := by positivity
  set P : ℝ := 2 * c / R with hPdef
  set g : ℝ → Space → ℝ≥0∞ := fun τ y => G τ y ^ (2 : ℝ) with hg
  have hgm : Measurable (Function.uncurry g) := hGm.pow_const 2
  have hgper : ∀ τ y, g (τ + P) y = g τ y := fun τ y => by simp only [hg, hper]
  set Φ : Space → ℝ≥0∞ := fun y => (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, g τ y with hΦ
  have hΦm : Measurable Φ :=
    (((hgm.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Ioc 0 P))).const_mul _)
  have hΦax : ∀ y y' : Space, y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 → Φ y' = Φ y := by
    intro y y' h2 h01
    simp only [hΦ, hg, hax _ y y' h2 h01]
  have hτm : Measurable (NearInst.chartTau R) := by
    unfold NearInst.chartTau; fun_prop
  have hym : Measurable (NearInst.chartY R) := by
    unfold NearInst.chartY
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
      (measurable_pi_lambda _ (fun i => ?_))
    fin_cases i <;> simp <;> fun_prop
  have hF : Measurable (fun p : Chart => ENNReal.ofReal p.1⁻¹ *
      g (NearInst.chartTau R p) (NearInst.chartY R p)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.inv).mul (hgm.comp (hτm.prodMk hym))
  have hYm : Measurable (fun rz : ℝ × ℝ => (WithLp.toLp 2 ![rz.1, 0, rz.2] : Space)) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
      (measurable_pi_lambda _ (fun i => ?_))
    fin_cases i <;> simp <;> fun_prop
  have key : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ x in qCell c, ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal s⁻¹ * g (NearInst.chartTau R (s, x)) (NearInst.chartY R (s, x))) =
      ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
        Φ (WithLp.toLp 2 ![R / Real.sqrt s, 0, η / Real.sqrt s]) := by
    intro s hs
    have hs' : 0 < s := hs
    rw [qCell_eq_cell]; unfold Cyl.cell
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [lintegral_prod_symm]
    · refine lintegral_congr fun η => ?_
      set Y : Space := WithLp.toLp 2 ![R / Real.sqrt s, 0, η / Real.sqrt s] with hY
      have hHm : Measurable (fun τ => g τ Y) := hgm.comp (measurable_id.prodMk measurable_const)
      have h1' := h1 R c hR hc (fun τ => g τ Y) hHm (fun τ => hgper τ Y) (Real.log s)
      have hq : Measurable (fun q : ℝ => g (2 * q / R + Real.log s) Y) :=
        hHm.comp (by fun_prop)
      have e : ∀ q : ℝ, ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) *
          (ENNReal.ofReal s⁻¹ * g (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))) =
          ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ * g (2 * q / R + Real.log s) Y) := by
        intro q
        have : s ^ (-5 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hs']; norm_num
        rw [this, mul_comm c⁻¹, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [NearInst.chartTau, NearInst.chartY, hY]
        ring
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hq, h1']
    · exact (measurable_const.mul (measurable_const.mul (hgm.comp
        ((hτm.comp measurable_prodMk_left).prodMk (hym.comp measurable_prodMk_left))))).aemeasurable
  have hLHS : ∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)
        ∂srcMeasure c =
      ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ y, Φ y := by
    have hmain : ∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)
        ∂srcMeasure c = ENNReal.ofReal Real.pi *
          ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
            Φ (WithLp.toLp 2 ![R / Real.sqrt s, 0, η / Real.sqrt s]) := by
      rw [srcMeasure, lintegral_smul_measure, smul_eq_mul]
      congr 1
      rw [lintegral_ageμ hc _ hF, Measure.volume_eq_prod, ← Measure.prod_restrict,
        lintegral_prod]
      · exact setLIntegral_congr_fun measurableSet_Ioi (fun s hs => key s hs)
      · exact ((ENNReal.measurable_ofReal.comp (by fun_prop :
          Measurable fun p : Chart => c⁻¹ * p.1 ^ (-3 / 2 : ℝ))).mul hF).aemeasurable
    set Ψ : ℝ → ℝ → ℝ≥0∞ := fun r z => Φ (WithLp.toLp 2 ![r, 0, z]) with hΨ
    have hΨm : Measurable (Function.uncurry Ψ) := hΦm.comp hYm
    have step : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (Real.pi * s ^ (-5 / 2 : ℝ)) *
        Ψ (R / Real.sqrt s) (η / Real.sqrt s) = ENNReal.ofReal Real.pi *
          ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
            Φ (WithLp.toLp 2 ![R / Real.sqrt s, 0, η / Real.sqrt s]) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun s => ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun η => ?_
      rw [ENNReal.ofReal_mul Real.pi_pos.le, mul_assoc]
    rw [hmain, ← step, h3 R hR Ψ hΨm, h2 Φ hΦm hΦax]
  rw [hLHS]
  apply le_of_eq
  congr 1
  unfold IIIa.ltauLq
  rw [← ENNReal.rpow_mul]
  norm_num
  have hinner : Measurable fun y : Space => ∫⁻ τ in Ioc 0 P, g τ y :=
    (hgm.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Ioc 0 P))
  show ∫⁻ y, (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, g τ y = _
  rw [lintegral_const_mul _ hinner, lintegral_lintegral_swap (μ := (volume : Measure Space))
    (ν := volume.restrict (Ioc 0 P)) (f := fun y τ => g τ y) (hgm.comp measurable_swap).aemeasurable]
  simp only [hg, ENNReal.rpow_two]

end UnforcedLeray.Short.PartIIIb.Concrete
