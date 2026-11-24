import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart.Core2

/-!
# `ThinChart/Core3`: `‖multMaj R V f‖_{Z₁} ≤ B ν⁻¹ A` on the transition window
(source 2697, 2706, 2717-2723)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TC

/-- The window integral `∫_{4/(5ν)}^{1/ν} s^{-3/2} ds ≤ ν⁻¹`. -/
theorem window_int {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ∫⁻ s in Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) ≤
      ENNReal.ofReal ν⁻¹ := by
  have hlow : ∀ s ∈ Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) ≤
      ENNReal.ofReal 2 := by
    intro s hs
    have h45 : 4 / 5 ≤ s := by
      have : 4 / 5 ≤ 4 / (5 * ν) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      linarith [hs.1]
    apply ENNReal.ofReal_le_ofReal
    have h1 : s ^ (-(3 / 2) : ℝ) ≤ (4 / 5 : ℝ) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h45 (by norm_num)
    have h2 : (4 / 5 : ℝ) ^ (-(3 / 2) : ℝ) = (5 / 4 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
    have h3 : (5 / 4 : ℝ) ^ (3 / 2 : ℝ) ≤ (5 / 4 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h4 : (5 / 4 : ℝ) ^ (2 : ℝ) = 25 / 16 := by norm_num
    linarith
  calc ∫⁻ s in Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal (s ^ (-(3 / 2) : ℝ))
      ≤ ∫⁻ s in Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal 2 :=
        setLIntegral_mono' measurableSet_Icc hlow
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (1 / ν - 4 / (5 * ν)) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ ≤ ENNReal.ofReal ν⁻¹ := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have : 1 / ν - 4 / (5 * ν) = ν⁻¹ / 5 := by field_simp; ring
        rw [this]
        have : 0 < ν⁻¹ := inv_pos.2 hν
        linarith

/-- **Thin multiplication on the window, abstract form** (source 2697, 2706, 2717-2723). -/
theorem z1Maj_multMaj_le {R c mZ ν B : ℝ} (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hB : 0 < B) {V : ℝ → Space → Space} (hVm : Measurable (IIIa.chartCoeff R V))
    (hVb : ∀ s : ℝ, 0 < s → IIIa.etaL2QSup c mZ (IIIa.chartCoeff R V) s ≤ ENNReal.ofReal B)
    {f : ℝ → Space → ℝ≥0∞} (hf : ChartGood (2 * c / R) f)
    (hvan : ∀ τ (y : Space), y ∉ streamAnn ν R → f τ y = 0) (A : ℝ≥0∞)
    (hA : ∀ y : Space, IIIa.ltauAt (2 * c / R) (fun τ => f τ y) ≤ A) :
    z1Maj c mZ (multMaj R V f) ≤ ENNReal.ofReal (B * ν⁻¹) * A := by
  by_cases hAtop : A = ⊤
  · rw [hAtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hmeasG : Measurable fun p : Chart =>
      ENNReal.ofReal (IIIa.transWeight mZ p ^ 2) * multMaj R V f p ^ (2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp ((IIIa.measurable_transWeight mZ).pow_const 2)).mul
      ((measurable_multMaj hVm hf.1).pow_const _)
  have hd : Measurable fun p : Chart => ENNReal.ofReal (IIIa.transWeight mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((IIIa.measurable_transWeight mZ).pow_const 2)
  -- the integral against `z1Measure`
  have step1 : ∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(z1Measure c mZ) ≤
      ∫⁻ p, ENNReal.ofReal (IIIa.transWeight mZ p ^ 2) * multMaj R V f p ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) :=
    lintegral_withDensity_le_lintegral_mul (ageμ c (-1 / 2)) hd (fun p => multMaj R V f p ^ (2 : ℝ))
  -- the age integrand
  set Jf : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, ENNReal.ofReal (IIIa.transWeight mZ (s, x) ^ 2) *
      multMaj R V f (s, x) ^ (2 : ℝ) ∂(Cyl.avgμ c) with hJf
  have step2 : ∫⁻ p, ENNReal.ofReal (IIIa.transWeight mZ p ^ 2) * multMaj R V f p ^ (2 : ℝ)
      ∂(ageμ c (-1 / 2)) ≤
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * Jf s := by
    unfold ageμ
    rw [lintegral_prod _ hmeasG.aemeasurable]
    exact lintegral_withDensity_le_lintegral_mul (volume.restrict (Ioi (0 : ℝ)))
      (measurable_ofReal_rpow (-1 / 2)) Jf
  have hJ : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * Jf s ≤ (Icc (4 / (5 * ν)) (1 / ν)).indicator
        (fun s => ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) * ENNReal.ofReal (s ^ (-(3 / 2) : ℝ))) s := by
    intro s hs
    by_cases hw : s ∈ Icc (4 / (5 * ν)) (1 / ν)
    · rw [indicator_of_mem hw]
      have hcell := cell_bound (mZ := mZ) hR hc hVm hf A hA hAtop s hs
      have hJs : Jf s = ENNReal.ofReal c⁻¹ * ∫⁻ x in Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (IIIa.transWeight mZ (s, x) ^ 2) * multMaj R V f (s, x) ^ (2 : ℝ) := by
        simp only [hJf, Cyl.avgμ, Cyl.cellμ, Cyl.cell, lintegral_smul_measure, smul_eq_mul]
      have hE : IIIa.etaL2QSup c mZ (IIIa.chartCoeff R V) s ^ (2 : ℝ) ≤ ENNReal.ofReal B ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (hVb s hs) (by norm_num)
      have e1 : ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal s⁻¹ =
          ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_neg_one,
          ← Real.rpow_add hs]
        norm_num
      have e2 : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
      calc ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * Jf s
          ≤ ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ *
            (ENNReal.ofReal B ^ (2 : ℝ) * (ENNReal.ofReal c * (ENNReal.ofReal s⁻¹ * A ^ (2 : ℝ))))) := by
            rw [hJs]
            exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hcell.trans (mul_le_mul' hE le_rfl)))
        _ = ENNReal.ofReal B ^ (2 : ℝ) * A ^ (2 : ℝ) * ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) := by
            rw [← e1]
            calc _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * (ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
                ENNReal.ofReal s⁻¹) * (ENNReal.ofReal B ^ (2 : ℝ) * A ^ (2 : ℝ)) := by ring
              _ = _ := by rw [e2, one_mul]; ring
        _ = _ := by
            simp only [ENNReal.rpow_two, ENNReal.ofReal_pow hB.le]
    · rw [indicator_of_notMem hw]
      have hz : ∀ x : ℝ × ℝ, multMaj R V f (s, x) = 0 := by
        intro x
        unfold multMaj
        have h0 : f (NearInst.chartTau R (s, x)) (NearInst.chartY R (s, x)) = 0 :=
          hvan _ _ (fun hy => hw (window_of_mem hR hν hs hy))
        rw [h0, mul_zero]
      have hJ0 : Jf s = 0 := by
        simp only [hJf, hz]
        simp
      rw [hJ0, mul_zero]
  have hK : ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAtop)
  have hI : ∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(z1Measure c mZ) ≤
      ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) * ENNReal.ofReal ν⁻¹ := by
    refine step1.trans (step2.trans ?_)
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * Jf s
        ≤ ∫⁻ s in Ioi (0 : ℝ), (Icc (4 / (5 * ν)) (1 / ν)).indicator
            (fun s => ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) *
              ENNReal.ofReal (s ^ (-(3 / 2) : ℝ))) s :=
          setLIntegral_mono' measurableSet_Ioi (fun s hs => hJ s hs)
      _ ≤ ∫⁻ s, (Icc (4 / (5 * ν)) (1 / ν)).indicator
            (fun s => ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) *
              ENNReal.ofReal (s ^ (-(3 / 2) : ℝ))) s := setLIntegral_le_lintegral _ _
      _ = ∫⁻ s in Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) *
              ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) := lintegral_indicator measurableSet_Icc _
      _ = ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) *
            ∫⁻ s in Icc (4 / (5 * ν)) (1 / ν), ENNReal.ofReal (s ^ (-(3 / 2) : ℝ)) :=
          lintegral_const_mul _ (measurable_ofReal_rpow _)
      _ ≤ _ := mul_le_mul' le_rfl (window_int hν hν1)
  have hfin : ENNReal.ofReal (B ^ 2) * A ^ (2 : ℝ) * ENNReal.ofReal ν⁻¹ ≤
      (ENNReal.ofReal (B * ν⁻¹) * A) ^ (2 : ℝ) := by
    have hinv : 0 < ν⁻¹ := inv_pos.2 hν
    have h1 : ν⁻¹ ≤ ν⁻¹ ^ 2 := by
      have : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
      nlinarith
    simp only [ENNReal.rpow_two, mul_pow]
    rw [← ENNReal.ofReal_pow (by positivity)]
    calc ENNReal.ofReal (B ^ 2) * A ^ 2 * ENNReal.ofReal ν⁻¹
        = ENNReal.ofReal (B ^ 2 * ν⁻¹) * A ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ ENNReal.ofReal ((B * ν⁻¹) ^ 2) * A ^ 2 := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
  unfold z1Maj
  calc (∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal (B * ν⁻¹) * A) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hI.trans hfin) (by norm_num)
    _ = ENNReal.ofReal (B * ν⁻¹) * A := by
        rw [← ENNReal.rpow_mul]; norm_num

end TC

end UnforcedLeray.Short.PartIIIb.Concrete

end
