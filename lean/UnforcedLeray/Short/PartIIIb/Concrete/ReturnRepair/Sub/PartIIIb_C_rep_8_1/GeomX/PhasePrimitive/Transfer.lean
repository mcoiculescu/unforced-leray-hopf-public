import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Deriv

/-!
# Bridge (3): from a periodic phase majorant to the cell norm (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 5415-5427 (normalized phase `L²_τ`): at the chart point `(s, η)` the receiver
`chartY R (s,·,η)` is fixed and `τ = 2q/R + log s` runs over one period `P = 2c/R = 2εc` as `q`
runs over the cell, `dq/c = dτ/P`.  So a `P`-periodic measurable majorant `B` of `F(·, y)` (a.e.
in `τ`) gives `cellL2 ≤ ‖B‖_{L²_τ}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PhasePrim

theorem map_affine (α β : ℝ) (hα : 0 < α) :
    Measure.map (fun q : ℝ => α * q + β) volume = ENNReal.ofReal α⁻¹ • (volume : Measure ℝ) := by
  have h1 : (fun q : ℝ => α * q + β) = (fun x => x + β) ∘ (fun q => α * q) := rfl
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hα.ne',
    Measure.map_smul, map_add_right_eq_self, abs_of_pos (inv_pos.2 hα)]

theorem qmp_affine (α β : ℝ) (hα : 0 < α) :
    Measure.QuasiMeasurePreserving (fun q : ℝ => α * q + β) volume volume :=
  ⟨by fun_prop, by rw [map_affine α β hα]; exact Measure.smul_absolutelyContinuous⟩

theorem lintegral_affine (α β a b : ℝ) (hα : 0 < α) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q in Ico a b, f (α * q + β) =
      ENNReal.ofReal α⁻¹ * ∫⁻ τ in Ico (α * a + β) (α * b + β), f τ := by
  have hpre : (fun q : ℝ => α * q + β) ⁻¹' Ico (α * a + β) (α * b + β) = Ico a b := by
    ext q
    simp only [mem_preimage, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hm : Measurable fun q : ℝ => α * q + β := by fun_prop
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico, ← hpre]
  have e : ∀ q, (((fun q : ℝ => α * q + β) ⁻¹' Ico (α * a + β) (α * b + β)).indicator
      (fun q => f (α * q + β))) q = (Ico (α * a + β) (α * b + β)).indicator f (α * q + β) :=
    fun q => Set.indicator_comp_right (fun q : ℝ => α * q + β)
  simp only [e]
  rw [← lintegral_map ((hf.indicator measurableSet_Ico)) hm, map_affine α β hα,
    lintegral_smul_measure, smul_eq_mul]

/-- **Bridge (3)**: a periodic majorant controls the cell norm. -/
theorem cellL2_le (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (F : ℝ → Space → ℝ) (s η : ℝ)
    (B : ℝ → ℝ≥0∞) (hBm : Measurable B) (hBp : Function.Periodic B (2 * ε * c))
    (hF : ∀ᵐ τ ∂(volume : Measure ℝ),
      ENNReal.ofReal (F τ (NearInst.chartY ε⁻¹ (s, (0, η)))) ≤ B τ) :
    cellL2 ε⁻¹ c F s η ≤ IIIa.ltauAt (2 * ε * c) B := by
  have hP : 0 < 2 * ε * c := by positivity
  have htau : ∀ q, NearInst.chartTau ε⁻¹ (s, (q, η)) = 2 * ε * q + Real.log s := by
    intro q
    unfold NearInst.chartTau
    rw [div_inv_eq_mul]
    ring
  have hy : ∀ q, NearInst.chartY ε⁻¹ (s, (q, η)) = NearInst.chartY ε⁻¹ (s, (0, η)) := fun q => rfl
  have hq : ∀ᵐ q ∂(volume : Measure ℝ),
      ENNReal.ofReal (F (2 * ε * q + Real.log s) (NearInst.chartY ε⁻¹ (s, (0, η)))) ≤
        B (2 * ε * q + Real.log s) :=
    (qmp_affine (2 * ε) (Real.log s) (by positivity)).ae hF
  unfold cellL2 IIIa.ltauAt
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  simp only [htau, hy]
  calc ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (F (2 * ε * q + Real.log s) (NearInst.chartY ε⁻¹ (s, (0, η)))) ^ 2
      ≤ ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * B (2 * ε * q + Real.log s) ^ 2 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hq] with q hq'
        gcongr
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), B (2 * ε * q + Real.log s) ^ 2 :=
        lintegral_const_mul _ ((hBm.comp (by fun_prop)).pow_const 2)
    _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (2 * ε)⁻¹ *
          ∫⁻ τ in Ico (2 * ε * (-c / 2) + Real.log s) (2 * ε * (c / 2) + Real.log s), B τ ^ 2) := by
        rw [lintegral_affine (2 * ε) (Real.log s) (-c / 2) (c / 2) (by positivity)
          (fun τ => B τ ^ 2) (hBm.pow_const 2)]
    _ = (ENNReal.ofReal (2 * ε * c))⁻¹ * ∫⁻ τ in Ioc 0 (2 * ε * c), B τ ^ (2 : ℝ) := by
        have hper : Function.Periodic (fun τ => B τ ^ 2) (2 * ε * c) := fun τ => by
          simp only [hBp τ]
        have e1 : ∫⁻ τ in Ico (2 * ε * (-c / 2) + Real.log s) (2 * ε * (c / 2) + Real.log s),
            B τ ^ 2 = ∫⁻ τ in Ioc (2 * ε * (-c / 2) + Real.log s)
              ((2 * ε * (-c / 2) + Real.log s) + 2 * ε * c), B τ ^ 2 := by
          rw [show (2 * ε * (-c / 2) + Real.log s) + 2 * ε * c = 2 * ε * (c / 2) + Real.log s by
            ring]
          exact setLIntegral_congr Ico_ae_eq_Ioc
        have e2 := lintegral_periodic hP hper (2 * ε * (-c / 2) + Real.log s) 0
        rw [zero_add] at e2
        rw [e1, e2]
        have e3 : ∀ τ, B τ ^ (2 : ℝ) = B τ ^ 2 := fun τ => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        simp only [e3]
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_inv_of_pos (by positivity),
          ← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
          ← ENNReal.ofReal_mul hc.le]
        congr 2
        ring

end PhasePrim

end UnforcedLeray.Short.PartIIIb.Concrete
