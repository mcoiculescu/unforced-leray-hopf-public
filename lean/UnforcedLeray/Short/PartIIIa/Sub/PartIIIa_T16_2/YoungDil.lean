import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem ydSmul (c : ℝ) (hc : 0 < c) {f : Space → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x : Space, f (c • x) = ENNReal.ofReal ((c ^ 3)⁻¹) * ∫⁻ x, f x := by
  have h := Measure.map_addHaar_smul (volume : Measure Space) hc.ne'
  have hm : Measurable fun x : Space => c • x := measurable_const_smul c
  rw [← lintegral_map hf hm, h, lintegral_smul_measure]
  simp [abs_of_pos (inv_pos.mpr (pow_pos hc 3))]

theorem ydMul (k h : ℝ≥0∞) {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsab : s * a + s * b = 1)
    (hpac : p * a + p * c = 1) :
    k * h = (k ^ s * h ^ p) ^ a * (k ^ s) ^ b * (h ^ p) ^ c := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc k * h = k ^ (s * a + s * b) * h ^ (p * a + p * c) := by
        rw [hsab, hpac, ENNReal.rpow_one, ENNReal.rpow_one]
    _ = k ^ (s * a) * h ^ (p * a) * k ^ (s * b) * h ^ (p * c) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hs ha) (mul_nonneg hs hb),
          ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp ha) (mul_nonneg hp hc)]
        ring

theorem ydThree {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f₁ f₂ f₃ : α → ℝ≥0∞} (h₁ : AEMeasurable f₁ ν) (h₂ : AEMeasurable f₂ ν)
    (h₃ : AEMeasurable f₃ ν) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    ∫⁻ y, f₁ y ^ a * f₂ y ^ b * f₃ y ^ c ∂ν ≤
      (∫⁻ y, f₁ y ∂ν) ^ a * (∫⁻ y, f₂ y ∂ν) ^ b * (∫⁻ y, f₃ y ∂ν) ^ c := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (μ := ν) (Finset.univ : Finset (Fin 2))
    (g := f₁) (f := ![f₂, f₃]) h₁ (by intro i _; fin_cases i <;> simpa) a (p := ![b, c])
    (by simp [Fin.sum_univ_two]; linarith) ha (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.prod_univ_two, mul_assoc] using h

/-- Young's inequality in `ℝ≥0∞` form on `ℝ³` (no dilation). -/
theorem ydConv {k g : Space → ℝ≥0∞} (hk : Measurable k) (hg : Measurable g) {s p r : ℝ}
    (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r) (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    (∫⁻ x : Space, (∫⁻ y : Space, k (x - y) * g y) ^ r) ^ (1 / r) ≤
      (∫⁻ z : Space, k z ^ s) ^ (1 / s) * (∫⁻ y : Space, g y ^ p) ^ (1 / p) := by
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  set a : ℝ := 1 / r with ha_def
  set b : ℝ := 1 - 1 / p with hb_def
  set c : ℝ := 1 - 1 / s with hc_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by
    rw [hb_def, sub_nonneg, div_le_one hp0]; exact hp
  have hc : 0 ≤ c := by
    rw [hc_def, sub_nonneg, div_le_one hs0]; exact hs
  have habc : a + b + c = 1 := by rw [ha_def, hb_def, hc_def]; linarith
  have hab : a + b = 1 / s := by rw [ha_def, hb_def]; linarith
  have hac : a + c = 1 / p := by rw [ha_def, hc_def]; linarith
  have hsab : s * a + s * b = 1 := by rw [← mul_add, hab]; field_simp
  have hpac : p * a + p * c = 1 := by rw [← mul_add, hac]; field_simp
  have har : a * r = 1 := by rw [ha_def]; field_simp
  have hF : Measurable (Function.uncurry fun (x y : Space) => k (x - y) ^ s * g y ^ p) :=
    ((hk.comp (measurable_fst.sub measurable_snd)).pow_const s).mul
      ((hg.comp measurable_snd).pow_const p)
  set A : ℝ≥0∞ := ∫⁻ z : Space, k z ^ s with hA
  set B : ℝ≥0∞ := ∫⁻ y : Space, g y ^ p with hB
  set Φ : Space → ℝ≥0∞ := fun x => ∫⁻ y : Space, k (x - y) ^ s * g y ^ p with hΦ
  have hΦm : Measurable Φ := hF.lintegral_prod_right'
  have h2 : ∀ x : Space, ∫⁻ y : Space, k (x - y) ^ s = A := fun x =>
    lintegral_sub_left_eq_self (fun z => k z ^ s) x
  have h2r : ∀ y : Space, ∫⁻ x : Space, k (x - y) ^ s = A := fun y =>
    lintegral_sub_right_eq_self (fun z => k z ^ s) y
  have hΦint : ∫⁻ x, Φ x = A * B := by
    calc ∫⁻ x, Φ x = ∫⁻ x : Space, ∫⁻ y : Space, k (x - y) ^ s * g y ^ p := rfl
      _ = ∫⁻ y : Space, ∫⁻ x : Space, k (x - y) ^ s * g y ^ p :=
          lintegral_lintegral_swap hF.aemeasurable
      _ = ∫⁻ y : Space, A * g y ^ p := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable fun x : Space => k (x - y) ^ s :=
            (hk.comp (measurable_id.sub measurable_const)).pow_const s
          rw [lintegral_mul_const _ hm]
          congr 1
          exact h2r y
      _ = A * B := lintegral_const_mul _ (hg.pow_const p)
  have hconv : ∀ x : Space, (∫⁻ y : Space, k (x - y) * g y) ≤ Φ x ^ a * A ^ b * B ^ c := by
    intro x
    have hpt : ∀ y : Space, k (x - y) * g y =
        (k (x - y) ^ s * g y ^ p) ^ a * (k (x - y) ^ s) ^ b * (g y ^ p) ^ c :=
      fun y => ydMul _ _ hs0.le hp0.le ha hb hc hsab hpac
    have hm1 : AEMeasurable (fun y : Space => k (x - y) ^ s * g y ^ p) volume :=
      (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
    have hm2 : AEMeasurable (fun y : Space => k (x - y) ^ s) volume :=
      ((hk.comp (measurable_const.sub measurable_id)).pow_const s).aemeasurable
    have hm3 : AEMeasurable (fun y : Space => g y ^ p) volume :=
      ((hg).pow_const p).aemeasurable
    calc ∫⁻ y : Space, k (x - y) * g y
        = ∫⁻ y : Space, (k (x - y) ^ s * g y ^ p) ^ a * (k (x - y) ^ s) ^ b * (g y ^ p) ^ c :=
          lintegral_congr hpt
      _ ≤ (∫⁻ y : Space, k (x - y) ^ s * g y ^ p) ^ a * (∫⁻ y : Space, k (x - y) ^ s) ^ b *
          (∫⁻ y : Space, g y ^ p) ^ c := ydThree hm1 hm2 hm3 ha hb hc habc
      _ = Φ x ^ a * A ^ b * B ^ c := by rw [h2 x]
  have hbr : 0 ≤ b * r := mul_nonneg hb hr0.le
  have hcr : 0 ≤ c * r := mul_nonneg hc hr0.le
  have h3 : ∫⁻ x : Space, (∫⁻ y : Space, k (x - y) * g y) ^ r ≤
      ∫⁻ x : Space, Φ x * (A ^ (b * r) * B ^ (c * r)) := by
    refine lintegral_mono fun x => ?_
    calc (∫⁻ y : Space, k (x - y) * g y) ^ r ≤ (Φ x ^ a * A ^ b * B ^ c) ^ r :=
          ENNReal.rpow_le_rpow (hconv x) hr0.le
      _ = Φ x * (A ^ (b * r) * B ^ (c * r)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, har, ENNReal.rpow_one,
            mul_assoc]
  have h4 : ∫⁻ x : Space, (∫⁻ y : Space, k (x - y) * g y) ^ r ≤
      A * B * (A ^ (b * r) * B ^ (c * r)) := by
    calc _ ≤ _ := h3
      _ = (∫⁻ x, Φ x) * (A ^ (b * r) * B ^ (c * r)) := lintegral_mul_const _ hΦm
      _ = A * B * (A ^ (b * r) * B ^ (c * r)) := by rw [hΦint]
  have hprod : A * B * (A ^ (b * r) * B ^ (c * r)) = A ^ (b * r + 1) * B ^ (c * r + 1) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ hbr zero_le_one,
      ENNReal.rpow_add_of_nonneg _ _ hcr zero_le_one, ENNReal.rpow_one, ENNReal.rpow_one]
    ring
  have hexpA : (b * r + 1) * (1 / r) = 1 / s := by
    rw [← hab, ha_def]; field_simp; ring
  have hexpB : (c * r + 1) * (1 / r) = 1 / p := by
    rw [← hac, ha_def]; field_simp; ring
  calc (∫⁻ x : Space, (∫⁻ y : Space, k (x - y) * g y) ^ r) ^ (1 / r)
      ≤ (A * B * (A ^ (b * r) * B ^ (c * r))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h4 (by positivity)
    _ = A ^ (1 / s) * B ^ (1 / p) := by
        rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, hexpA, hexpB]

theorem sepYoungDil_exp (l : ℝ) (hl : 0 < l) (p : ℝ) :
    (l ^ 3)⁻¹ * (l ^ 3) ^ (1 / p) = l ^ (-3 + 3 / p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg hl.le, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
  congr 1
  push_cast
  ring

/-- **Young's inequality with dilation** (SP 3631-3636). -/
theorem sepYoungDil : UnforcedLeray.Short.IIIa.SepYoungDil := by
  intro p q b hp hb hq hrel k G hk hG l hl
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hbq : 1 / b + 1 / p = 1 + 1 / q := by linarith
  have hGl : Measurable fun w : Space => G (l⁻¹ • w) := hG.comp (measurable_const_smul _)
  -- substitution `w = l z` in the inner integral
  have hinner : ∀ y : Space, ∫⁻ z : Space, k (y - l • z) * G z =
      ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ w : Space, k (y - w) * G (l⁻¹ • w) := by
    intro y
    have hf : Measurable fun w : Space => k (y - w) * G (l⁻¹ • w) :=
      (hk.comp (measurable_const.sub measurable_id)).mul hGl
    calc ∫⁻ z : Space, k (y - l • z) * G z
        = ∫⁻ z : Space, (fun w : Space => k (y - w) * G (l⁻¹ • w)) (l • z) :=
          lintegral_congr fun z => by simp only [inv_smul_smul₀ hl.ne']
      _ = _ := ydSmul l hl hf
  have hCm : Measurable fun y : Space => ∫⁻ w : Space, k (y - w) * G (l⁻¹ • w) := by
    have hF : Measurable (Function.uncurry fun (y w : Space) => k (y - w) * G (l⁻¹ • w)) :=
      (hk.comp (measurable_fst.sub measurable_snd)).mul (hG.comp
        ((measurable_const_smul (l⁻¹)).comp measurable_snd))
    exact hF.lintegral_prod_right'
  have hLHS : (∫⁻ y : Space, (∫⁻ z : Space, k (y - l • z) * G z) ^ q) ^ (1 / q) =
      ENNReal.ofReal ((l ^ 3)⁻¹) *
        (∫⁻ y : Space, (∫⁻ w : Space, k (y - w) * G (l⁻¹ • w)) ^ q) ^ (1 / q) := by
    simp_rw [hinner]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    rw [lintegral_const_mul _ (hCm.pow_const q), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hY : (∫⁻ x : Space, (∫⁻ y : Space, k (x - y) * G (l⁻¹ • y)) ^ q) ^ (1 / q) ≤
      (∫⁻ z : Space, k z ^ b) ^ (1 / b) * (∫⁻ y : Space, G (l⁻¹ • y) ^ p) ^ (1 / p) :=
    ydConv hk hGl hb hp hq hbq
  have hG2 : ∫⁻ y : Space, G (l⁻¹ • y) ^ p = ENNReal.ofReal (l ^ 3) * ∫⁻ y : Space, G y ^ p := by
    have h := ydSmul l⁻¹ (inv_pos.mpr hl) (hG.pow_const p)
    simp only [inv_pow, inv_inv] at h
    exact h
  calc (∫⁻ y : Space, (∫⁻ z : Space, k (y - l • z) * G z) ^ q) ^ (1 / q)
      = ENNReal.ofReal ((l ^ 3)⁻¹) *
          (∫⁻ y : Space, (∫⁻ w : Space, k (y - w) * G (l⁻¹ • w)) ^ q) ^ (1 / q) := hLHS
    _ ≤ ENNReal.ofReal ((l ^ 3)⁻¹) * ((∫⁻ z : Space, k z ^ b) ^ (1 / b) *
          (∫⁻ y : Space, G (l⁻¹ • y) ^ p) ^ (1 / p)) := by gcongr
    _ = ENNReal.ofReal ((l ^ 3)⁻¹) * ((∫⁻ z : Space, k z ^ b) ^ (1 / b) *
          (ENNReal.ofReal (l ^ 3) * ∫⁻ y : Space, G y ^ p) ^ (1 / p)) := by rw [hG2]
    _ = ENNReal.ofReal (l ^ (-3 + 3 / p)) * (∫⁻ z : Space, k z ^ b) ^ (1 / b) *
          (∫⁻ y : Space, G y ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← sepYoungDil_exp l hl p, ENNReal.ofReal_mul (by positivity)]
        ring

end UnforcedLeray.Short.IIIa

end
