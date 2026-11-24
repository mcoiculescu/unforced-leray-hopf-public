import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart.Core1

/-!
# `ThinChart/Core2`: one age `s`, Tonelli in `(q, η)`, `L^∞_q` of the coefficient against `L²_q` of `f`
(source 2697, 2717, 2666-2668)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TC

theorem measurable_chartTau' (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem measurable_chartY' (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem measurable_multMaj {R : ℝ} {V : ℝ → Space → Space}
    (hVm : Measurable (IIIa.chartCoeff R V)) {f : ℝ → Space → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) : Measurable (multMaj R V f) := by
  unfold multMaj
  refine (ENNReal.measurable_ofReal.comp ?_).mul ?_
  · exact hVm.norm.mul (measurable_fst.sqrt.inv)
  · exact hf.comp ((measurable_chartTau' R).prodMk (measurable_chartY' R))

theorem transWeight_nonneg (mZ : ℝ) (p : Chart) : 0 ≤ IIIa.transWeight mZ p := by
  unfold IIIa.transWeight
  exact Real.rpow_nonneg (by positivity) _

theorem ltauAt_sq (P : ℝ) (g : ℝ → ℝ≥0∞) :
    IIIa.ltauAt P g ^ (2 : ℝ) = (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ) := by
  unfold IIIa.ltauAt
  rw [← ENNReal.rpow_mul]
  norm_num

/-- One age `s`: the `(q,η)`-cell integral of `W²(multMaj)²`. -/
theorem cell_bound {R c mZ : ℝ} (hR : 0 < R) (hc : 0 < c) {V : ℝ → Space → Space}
    (hVm : Measurable (IIIa.chartCoeff R V)) {f : ℝ → Space → ℝ≥0∞}
    (hf : ChartGood (2 * c / R) f) (A : ℝ≥0∞)
    (hA : ∀ y : Space, IIIa.ltauAt (2 * c / R) (fun τ => f τ y) ≤ A) (hAtop : A ≠ ⊤)
    (s : ℝ) (hs : 0 < s) :
    ∫⁻ x in Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (IIIa.transWeight mZ (s, x) ^ 2) * multMaj R V f (s, x) ^ (2 : ℝ) ≤
      IIIa.etaL2QSup c mZ (IIIa.chartCoeff R V) s ^ (2 : ℝ) *
        (ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ))) := by
  have hmeasG : Measurable fun p : Chart =>
      ENNReal.ofReal (IIIa.transWeight mZ p ^ 2) * multMaj R V f p ^ (2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp ((IIIa.measurable_transWeight mZ).pow_const 2)).mul
      ((measurable_multMaj hVm hf.1).pow_const _)
  have hGs : Measurable fun x : ℝ × ℝ =>
      ENNReal.ofReal (IIIa.transWeight mZ (s, x) ^ 2) * multMaj R V f (s, x) ^ (2 : ℝ) :=
    hmeasG.comp (measurable_const.prodMk measurable_id)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ hGs.aemeasurable]
  have hK : ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAtop))
  have hneg : -c / 2 = -(c / 2) := neg_div 2 c
  set Mq : ℝ → ℝ≥0∞ := fun η => essSup (fun q : ℝ => ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η))) *
      ‖IIIa.chartCoeff R V (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2))) with hMq
  have hinner : ∀ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
      ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η)) ^ 2) * multMaj R V f (s, (q, η)) ^ (2 : ℝ) ≤
      Mq η ^ (2 : ℝ) * (ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ))) := by
    intro η
    set y : Space := NearInst.chartY R (s, (0, η)) with hy
    have hae := ENNReal.ae_le_essSup (μ := volume.restrict (Ico (-(c / 2)) (c / 2)))
      (fun q : ℝ => ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η))) *
        ‖IIIa.chartCoeff R V (s, (q, η))‖ₑ)
    rw [hneg]
    have hpt : ∀ q : ℝ,
        ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η)) ^ 2) *
            multMaj R V f (s, (q, η)) ^ (2 : ℝ) =
          (ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η))) *
            ‖IIIa.chartCoeff R V (s, (q, η))‖ₑ) ^ (2 : ℝ) *
          (ENNReal.ofReal s⁻¹ * f (2 * q / R + Real.log s) y ^ (2 : ℝ)) := by
      intro q
      unfold multMaj
      rw [← ofReal_norm_eq_enorm]
      exact weight_alg (transWeight_nonneg mZ _) hs _
    simp_rw [hpt]
    calc ∫⁻ q in Ico (-(c / 2)) (c / 2),
          (ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η))) *
            ‖IIIa.chartCoeff R V (s, (q, η))‖ₑ) ^ (2 : ℝ) *
          (ENNReal.ofReal s⁻¹ * f (2 * q / R + Real.log s) y ^ (2 : ℝ))
        ≤ ∫⁻ q in Ico (-(c / 2)) (c / 2), Mq η ^ (2 : ℝ) *
          (ENNReal.ofReal s⁻¹ * f (2 * q / R + Real.log s) y ^ (2 : ℝ)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with q hq
          exact mul_le_mul' (ENNReal.rpow_le_rpow hq (by norm_num)) le_rfl
      _ = Mq η ^ (2 : ℝ) * (ENNReal.ofReal s⁻¹ *
            ∫⁻ q in Ico (-(c / 2)) (c / 2), f (2 * q / R + Real.log s) y ^ (2 : ℝ)) := by
          have hfm : Measurable fun q : ℝ => f (2 * q / R + Real.log s) y ^ (2 : ℝ) :=
            ((hf.1.comp (measurable_id.prodMk measurable_const)).comp
              ((measurable_const.mul measurable_id).div_const R |>.add_const _)).pow_const _
          have hm1 : Measurable fun q : ℝ => ENNReal.ofReal s⁻¹ * f (2 * q / R + Real.log s) y ^ (2 : ℝ) :=
            hfm.const_mul _
          rw [lintegral_const_mul _ hm1, lintegral_const_mul _ hfm]
      _ ≤ Mq η ^ (2 : ℝ) * (ENNReal.ofReal s⁻¹ * (ENNReal.ofReal c * A ^ (2 : ℝ))) := by
          refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
          have hFm : Measurable fun τ : ℝ => f τ y ^ (2 : ℝ) :=
            (hf.1.comp (measurable_id.prodMk measurable_const)).pow_const _
          have hper : ∀ τ, f (τ + 2 * c / R) y ^ (2 : ℝ) = f τ y ^ (2 : ℝ) := fun τ => by
            rw [hf.2.1 τ y]
          have hq := qint hR hc hFm hper (Real.log s)
          rw [hneg] at hq
          rw [hq, ← ltauAt_sq (2 * c / R) (fun τ => f τ y)]
          exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hA y) (by norm_num))
      _ = _ := by ring
  calc ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (IIIa.transWeight mZ (s, (q, η)) ^ 2) *
          multMaj R V f (s, (q, η)) ^ (2 : ℝ)
      ≤ ∫⁻ η, Mq η ^ (2 : ℝ) * (ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ))) :=
        lintegral_mono hinner
    _ = (∫⁻ η, Mq η ^ (2 : ℝ)) * (ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ))) :=
        lintegral_mul_const' _ _ hK
    _ = _ := by
        unfold IIIa.etaL2QSup
        rw [← ENNReal.rpow_mul]
        norm_num
        rfl

end TC

end UnforcedLeray.Short.PartIIIb.Concrete

end
