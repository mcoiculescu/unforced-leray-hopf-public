import UnforcedLeray.Statement
import Mathlib.Analysis.Convolution
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Young's convolution inequality on three-dimensional Euclidean space

The majorant proof is adapted from `NonUniqueEuler/P/Infra/ConvMinkowski/YoungGeneral.lean`
at public NonUniqueEuler commit `d81c3f456505f8a3e8211f2a9f63313d0599ed5a`
(Apache-2.0; original attribution is retained in `lean/NOTICE-NonUniqueEuler`). The original proof on `ℂ`
uses only Haar-measure invariance and is specialized here to `Space = EuclideanSpace ℝ (Fin 3)`.
The Bochner-convolution existence and finite-norm statements below are added for this project.

For `convAbs K g x = ∫⁻ ‖K(x-y)‖ ‖g(y)‖ dy` on `Space` and real exponents `1 ≤ s, p, r` with
`1/s + 1/p = 1 + 1/r`: `‖|K| ⋆ |g|‖_r ≤ ‖K‖_s ‖g‖_p`
(upstream manuscript `lem:velocity`(a),(b), `02_prelim.tex:323-381`).

The classical three-factor Hölder argument, entirely in `ℝ≥0∞` (so no degenerate case needs a
separate treatment). Put `k = ‖K‖ₑ`, `h = ‖g‖ₑ`, `a = 1/r`, `b = 1 - 1/p`, `c = 1 - 1/s`
(`a, b, c ≥ 0`, `a + b + c = 1`), `A = ∫ k^s`, `B = ∫ h^p`, `Φ(x) = ∫ k(x-y)^s h(y)^p dy`.
1. Pointwise: `k(x-y) h(y) = (k(x-y)^s h(y)^p)^a (k(x-y)^s)^b (h(y)^p)^c` (because
   `s(a + b) = 1` and `p(a + c) = 1`), so the three-factor Hölder inequality
   (`ENNReal.lintegral_mul_prod_norm_pow_le`) and translation invariance give
   `(|K| ⋆ |g|)(x) ≤ Φ(x)^a A^b B^c`.
2. Tonelli and translation invariance: `∫ Φ = A B`.
3. Since `a r = 1`: `∫ (|K| ⋆ |g|)^r ≤ A^{br} B^{cr} A B`, and taking the `r`-th root,
   `(b r + 1)/r = 1/s`, `(c r + 1)/r = 1/p` give `A^{1/s} B^{1/p} = ‖K‖_s ‖g‖_p`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace UnforcedLeray.PressureAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Nonnegative convolution majorant, retaining its value `∞` when the integral diverges. -/
def convAbs (K : Space → E) (g : Space → F) (x : Space) : ℝ≥0∞ :=
  ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ

/-! ### Helpers -/

/-- Three-factor Hölder inequality for `ℝ≥0∞`-valued functions, with weights summing to `1`. -/
private theorem lintegral_three_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ : α → ℝ≥0∞} (h₁ : AEMeasurable f₁ μ) (h₂ : AEMeasurable f₂ μ)
    (h₃ : AEMeasurable f₃ μ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    ∫⁻ y, f₁ y ^ a * f₂ y ^ b * f₃ y ^ c ∂μ ≤
      (∫⁻ y, f₁ y ∂μ) ^ a * (∫⁻ y, f₂ y ∂μ) ^ b * (∫⁻ y, f₃ y ∂μ) ^ c := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 2))
    (g := f₁) (f := ![f₂, f₃]) h₁ (by intro i _; fin_cases i <;> simpa) a (p := ![b, c])
    (by simp [Fin.sum_univ_two]; linarith) ha (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.prod_univ_two, mul_assoc] using h

/-- The pointwise factorization `k h = (k^s h^p)^a (k^s)^b (h^p)^c` when `s (a + b) = 1` and
`p (a + c) = 1`. -/
private theorem mul_eq_three_rpow (k h : ℝ≥0∞) {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
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

/-- Joint measurability of `(x, y) ↦ ‖K (x - y)‖^s ‖g y‖^p`. -/
private theorem aemeasurable_prod_conv_rpow {K : Space → E} {g : Space → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) (s p : ℝ) :
    AEMeasurable (fun q : Space × Space => ‖K (q.1 - q.2)‖ₑ ^ s * ‖g q.2‖ₑ ^ p)
      ((volume : Measure Space).prod volume) :=
  ((hK.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).pow_const
    s).mul (hg.enorm.comp_snd.pow_const p)

/-- For fixed `x`, `y ↦ ‖K (x - y)‖ₑ` is a.e.-measurable. -/
private theorem aemeasurable_enorm_sub_left {K : Space → E} (hK : AEStronglyMeasurable K volume)
    (x : Space) : AEMeasurable (fun y => ‖K (x - y)‖ₑ) volume :=
  hK.enorm.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving

/-- Tonelli: `∫∫ ‖K (x - y)‖^s ‖g y‖^p dy dx = (∫ ‖K‖^s) (∫ ‖g‖^p)`. -/
private theorem lintegral_lintegral_conv_rpow {K : Space → E} {g : Space → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) (s p : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p =
      (∫⁻ z, ‖K z‖ₑ ^ s) * ∫⁻ y, ‖g y‖ₑ ^ p := by
  rw [lintegral_lintegral_swap (aemeasurable_prod_conv_rpow hK hg s p)]
  have hm : ∀ y : Space, AEMeasurable (fun x => ‖K (x - y)‖ₑ ^ s) volume := fun y =>
    (hK.enorm.comp_quasiMeasurePreserving
      (measurePreserving_sub_right volume y).quasiMeasurePreserving).pow_const s
  have h2 : ∀ y : Space, ∫⁻ x, ‖K (x - y)‖ₑ ^ s = ∫⁻ z, ‖K z‖ₑ ^ s := fun y =>
    lintegral_sub_right_eq_self (fun z => ‖K z‖ₑ ^ s) y
  calc ∫⁻ y, ∫⁻ x, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p
      = ∫⁻ y, (∫⁻ z, ‖K z‖ₑ ^ s) * ‖g y‖ₑ ^ p := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const'' _ (hm y), h2 y]
    _ = (∫⁻ z, ‖K z‖ₑ ^ s) * ∫⁻ y, ‖g y‖ₑ ^ p :=
        lintegral_const_mul'' _ (hg.enorm.pow_const p)

/-- Step 1: `(|K| ⋆ |g|)(x) ≤ Φ(x)^a (∫ ‖K‖^s)^b (∫ ‖g‖^p)^c`. -/
private theorem convAbs_le_three_rpow {K : Space → E} {g : Space → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume)
    {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) (hsab : s * a + s * b = 1) (hpac : p * a + p * c = 1) (x : Space) :
    convAbs K g x ≤ (∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p) ^ a *
      (∫⁻ z, ‖K z‖ₑ ^ s) ^ b * (∫⁻ y, ‖g y‖ₑ ^ p) ^ c := by
  have hk := aemeasurable_enorm_sub_left hK x
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) volume := hg.enorm
  have htr : ∫⁻ y, ‖K (x - y)‖ₑ ^ s = ∫⁻ z, ‖K z‖ₑ ^ s :=
    lintegral_sub_left_eq_self (fun z => ‖K z‖ₑ ^ s) x
  rw [← htr, convAbs]
  calc ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ
      = ∫⁻ y, (‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p) ^ a * (‖K (x - y)‖ₑ ^ s) ^ b *
          (‖g y‖ₑ ^ p) ^ c :=
        lintegral_congr fun y => mul_eq_three_rpow _ _ hs hp ha hb hc hsab hpac
    _ ≤ _ := lintegral_three_rpow_le ((hk.pow_const s).mul (hgm.pow_const p))
        (hk.pow_const s) (hgm.pow_const p) ha hb hc habc

/-! ### Young's inequality -/

/-- **Young's convolution inequality**: `‖|K| ⋆ |g|‖_r ≤ ‖K‖_s ‖g‖_p` for
`1 ≤ s, p, r < ∞` with `1/s + 1/p = 1 + 1/r`. -/
theorem eLpNorm_convAbs_le_young {K : Space → E} {g : Space → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (convAbs K g) (ENNReal.ofReal r) volume ≤
      eLpNorm K (ENNReal.ofReal s) volume * eLpNorm g (ENNReal.ofReal p) volume := by
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  -- exponents
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
  -- the integrals
  set A : ℝ≥0∞ := ∫⁻ z, ‖K z‖ₑ ^ s with hA_def
  set B : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ p with hB_def
  set Φ : Space → ℝ≥0∞ := fun x => ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p with hΦ_def
  have hΦm : AEMeasurable Φ volume := (aemeasurable_prod_conv_rpow hK hg s p).lintegral_prod_right'
  have hΦint : ∫⁻ x, Φ x = A * B := lintegral_lintegral_conv_rpow hK hg s p
  -- Step 3: the `r`-th power
  have h3 : ∫⁻ x, convAbs K g x ^ r ≤ A * B * (A ^ (b * r) * B ^ (c * r)) := by
    calc ∫⁻ x, convAbs K g x ^ r
        ≤ ∫⁻ x, (Φ x ^ a * A ^ b * B ^ c) ^ r := by
          refine lintegral_mono fun x => ?_
          exact ENNReal.rpow_le_rpow
            (convAbs_le_three_rpow hK hg hs0.le hp0.le ha hb hc habc hsab hpac x) hr0.le
      _ = ∫⁻ x, Φ x * (A ^ (b * r) * B ^ (c * r)) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, har, ENNReal.rpow_one,
            mul_assoc]
      _ = A * B * (A ^ (b * r) * B ^ (c * r)) := by
          rw [lintegral_mul_const'' _ hΦm, hΦint]
  -- Step 4: the `r`-th root
  have hr_ne : ENNReal.ofReal r ≠ 0 := by simp [hr0]
  have hs_ne : ENNReal.ofReal s ≠ 0 := by simp [hs0]
  have hp_ne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hs_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le, ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hp0.le]
  simp only [enorm_eq_self]
  rw [← hA_def, ← hB_def]
  have hbr : 0 ≤ b * r := mul_nonneg hb hr0.le
  have hcr : 0 ≤ c * r := mul_nonneg hc hr0.le
  have hexpA : (b * r + 1) * (1 / r) = 1 / s := by rw [← hab, ha_def]; field_simp; ring
  have hexpB : (c * r + 1) * (1 / r) = 1 / p := by rw [← hac, ha_def]; field_simp; ring
  have hprod : A * B * (A ^ (b * r) * B ^ (c * r)) = A ^ (b * r + 1) * B ^ (c * r + 1) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ hbr zero_le_one,
      ENNReal.rpow_add_of_nonneg _ _ hcr zero_le_one, ENNReal.rpow_one, ENNReal.rpow_one]
    ring
  calc (∫⁻ x, convAbs K g x ^ r) ^ (1 / r)
      ≤ (A * B * (A ^ (b * r) * B ^ (c * r))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h3 (by positivity)
    _ = A ^ (1 / s) * B ^ (1 / p) := by
        rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, hexpA, hexpB]


/-- The nonnegative convolution majorant is a.e. measurable. -/
theorem aemeasurable_convAbs {K : Space → E} {g : Space → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (convAbs K g) volume := by
  exact ((hK.enorm.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub volume volume)).mul hg.enorm.comp_snd).lintegral_prod_right'

/-- Under Young's finite-norm hypotheses the majorant is finite almost everywhere. -/
theorem convAbs_lt_top_ae_young {K : Space → E} {g : Space → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hg : MemLp g (ENNReal.ofReal p) volume) :
    ∀ᵐ x, convAbs K g x < ∞ := by
  have hr0 : 0 < r := by linarith
  have hrne : ENNReal.ofReal r ≠ 0 := by simp [hr0]
  have hfinite : eLpNorm (convAbs K g) (ENNReal.ofReal r) volume < ∞ :=
    (eLpNorm_convAbs_le_young hK.1 hg.1 hs hp hr hspr).trans_lt
      (ENNReal.mul_lt_top hK.2 hg.2)
  have hpower : ∫⁻ x, convAbs K g x ^ (ENNReal.ofReal r).toReal < ∞ := by
    simpa only [enorm_eq_self] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hrne ENNReal.ofReal_ne_top hfinite
  filter_upwards [ae_lt_top' ((aemeasurable_convAbs hK.1 hg.1).pow_const _) hpower.ne]
    with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos
    (ENNReal.toReal_pos hrne ENNReal.ofReal_ne_top)).mp hx

section ScalarConvolution

/-- Joint measurability gives measurability of the literal Bochner convolution. -/
theorem aestronglyMeasurable_convolution {K f : Space → ℝ}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * f y) volume := by
  exact ((hK.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub volume volume)).mul hf.comp_snd).integral_prod_right'

/-- Young's hypotheses ensure actual absolute integrability of the Bochner convolution a.e. -/
theorem convolution_integrable_ae_young {K f : Space → ℝ}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by
  filter_upwards [convAbs_lt_top_ae_young hs hp hr hspr hK hf] with x hx
  refine ⟨(hK.1.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).mul hf.1, ?_⟩
  simpa only [HasFiniteIntegral, enorm_mul, convAbs] using hx

/-- The actual scalar convolution satisfies Young's norm inequality. -/
theorem eLpNorm_convolution_le_young {K f : Space → ℝ}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume)
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal r) volume ≤
      eLpNorm K (ENNReal.ofReal s) volume * eLpNorm f (ENNReal.ofReal p) volume := by
  refine (eLpNorm_mono_enorm (g := convAbs K f) fun x => ?_).trans
    (eLpNorm_convAbs_le_young hK hf hs hp hr hspr)
  simpa only [enorm_eq_self, convAbs, enorm_mul] using
    enorm_integral_le_lintegral_enorm (fun y => K (x - y) * f y)

/-- Finite input norms give actual `Lʳ` membership of the scalar convolution. -/
theorem convolution_memLp_young {K f : Space → ℝ}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal r) volume :=
  ⟨aestronglyMeasurable_convolution hK.1 hf.1,
    (eLpNorm_convolution_le_young hK.1 hf.1 hs hp hr hspr).trans_lt
      (ENNReal.mul_lt_top hK.2 hf.2)⟩

/-- Young's inequality for finite, real-valued `Lᵖ` norms. -/
theorem convolution_norm_le_young {K f : Space → ℝ}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal r) volume).toReal ≤
      (eLpNorm K (ENNReal.ofReal s) volume).toReal *
        (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
  simpa only [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hK.2.ne hf.2.ne)
      (eLpNorm_convolution_le_young hK.1 hf.1 hs hp hr hspr)

end ScalarConvolution


section VectorConvolution

variable [NormedSpace ℝ F]

/-- Joint measurability gives measurability of the literal Bochner convolution. -/
theorem smul_aestronglyMeasurable_convolution [CompleteSpace F] {K : Space → ℝ} {f : Space → F}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) • f y) volume := by
  exact ((hK.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub volume volume)).smul hf.comp_snd).integral_prod_right'

/-- Young's hypotheses ensure actual absolute integrability of the Bochner convolution a.e. -/
theorem smul_convolution_integrable_ae_young [CompleteSpace F] {K : Space → ℝ} {f : Space → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) • f y) volume := by
  filter_upwards [convAbs_lt_top_ae_young hs hp hr hspr hK hf] with x hx
  refine ⟨(hK.1.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).smul hf.1, ?_⟩
  simpa only [HasFiniteIntegral, enorm_smul, convAbs] using hx

/-- The actual scalar-kernel vector convolution satisfies Young's norm inequality. -/
theorem smul_eLpNorm_convolution_le_young [CompleteSpace F] {K : Space → ℝ} {f : Space → F}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume)
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (fun x => ∫ y, K (x - y) • f y) (ENNReal.ofReal r) volume ≤
      eLpNorm K (ENNReal.ofReal s) volume * eLpNorm f (ENNReal.ofReal p) volume := by
  refine (eLpNorm_mono_enorm (g := convAbs K f) fun x => ?_).trans
    (eLpNorm_convAbs_le_young hK hf hs hp hr hspr)
  simpa only [enorm_eq_self, convAbs, enorm_smul] using
    enorm_integral_le_lintegral_enorm (fun y => K (x - y) • f y)

/-- Finite input norms give actual `Lʳ` membership of the scalar-kernel vector convolution. -/
theorem smul_convolution_memLp_young [CompleteSpace F] {K : Space → ℝ} {f : Space → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (fun x => ∫ y, K (x - y) • f y) (ENNReal.ofReal r) volume :=
  ⟨smul_aestronglyMeasurable_convolution hK.1 hf.1,
    (smul_eLpNorm_convolution_le_young hK.1 hf.1 hs hp hr hspr).trans_lt
      (ENNReal.mul_lt_top hK.2 hf.2)⟩

/-- Young's inequality for finite, real-valued `Lᵖ` norms. -/
theorem smul_convolution_norm_le_young [CompleteSpace F] {K : Space → ℝ} {f : Space → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (eLpNorm (fun x => ∫ y, K (x - y) • f y) (ENNReal.ofReal r) volume).toReal ≤
      (eLpNorm K (ENNReal.ofReal s) volume).toReal *
        (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
  simpa only [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hK.2.ne hf.2.ne)
      (smul_eLpNorm_convolution_le_young hK.1 hf.1 hs hp hr hspr)


end VectorConvolution

private theorem ofReal_fifteenFourteenths : ENNReal.ofReal (15 / 14 : ℝ) = (15 / 14 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

private theorem ofReal_threeHalves : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

private theorem ofReal_fiveThirds : ENNReal.ofReal (5 / 3 : ℝ) = (5 / 3 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- Young's inequality with the exact exponents used for the near pressure kernel. -/
theorem convolution_integrable_ae_near {K f : Space → ℝ}
    (hK : MemLp K (15 / 14) volume) (hf : MemLp f (3 / 2) volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by
  have h := convolution_integrable_ae_young (s := 15 / 14) (p := 3 / 2) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using h

/-- Young's inequality with the exact exponents used for the near pressure kernel. -/
theorem convolution_memLp_near {K f : Space → ℝ}
    (hK : MemLp K (15 / 14) volume) (hf : MemLp f (3 / 2) volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) (5 / 3) volume := by
  have h := convolution_memLp_young (s := 15 / 14) (p := 3 / 2) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using h

/-- Young's inequality with the exact exponents used for the near pressure kernel. -/
theorem convolution_norm_le_near {K f : Space → ℝ}
    (hK : MemLp K (15 / 14) volume) (hf : MemLp f (3 / 2) volume) :
    (eLpNorm (fun x => ∫ y, K (x - y) * f y) (5 / 3) volume).toReal ≤
      (eLpNorm K (15 / 14) volume).toReal * (eLpNorm f (3 / 2) volume).toReal := by
  have h := convolution_norm_le_young (s := 15 / 14) (p := 3 / 2) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fifteenFourteenths, ofReal_threeHalves] using h

/-- Young's inequality with the exact exponents used for the far pressure kernel. -/
theorem convolution_integrable_ae_far {K f : Space → ℝ}
    (hK : MemLp K (5 / 3) volume) (hf : MemLp f (1) volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by
  have h := convolution_integrable_ae_young (s := 5 / 3) (p := 1) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using h

/-- Young's inequality with the exact exponents used for the far pressure kernel. -/
theorem convolution_memLp_far {K f : Space → ℝ}
    (hK : MemLp K (5 / 3) volume) (hf : MemLp f (1) volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) (5 / 3) volume := by
  have h := convolution_memLp_young (s := 5 / 3) (p := 1) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using h

/-- Young's inequality with the exact exponents used for the far pressure kernel. -/
theorem convolution_norm_le_far {K f : Space → ℝ}
    (hK : MemLp K (5 / 3) volume) (hf : MemLp f (1) volume) :
    (eLpNorm (fun x => ∫ y, K (x - y) * f y) (5 / 3) volume).toReal ≤
      (eLpNorm K (5 / 3) volume).toReal * (eLpNorm f (1) volume).toReal := by
  have h := convolution_norm_le_young (s := 5 / 3) (p := 1) (r := 5 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hK)
    (by simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using hf)
  simpa only [ofReal_fiveThirds, ofReal_fiveThirds, ENNReal.ofReal_one] using h

end UnforcedLeray.PressureAnalysis
