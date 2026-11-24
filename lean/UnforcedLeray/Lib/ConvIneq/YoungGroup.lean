import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.ENNReal.Holder

/-!
# Young's convolution inequality on a measurable abelian group (INF22 A1, bypass BP1)

Blueprint infrastructure target **INF22 A1** of the scoping note

bypass BP1 of §4). One Young inequality on an abelian group `G` with a σ-finite measure `μ`
that is invariant under translations and under `x ↦ -x`; the instances `ℝ³`, `ℝ`, `ℝ²`, `ℂ`
are by `inferInstance`, the cylinder `AddCircle c × ℝ` in `YoungInstances.lean`.

Manuscript uses (scoping note §2.1–§2.2): Young `(1,p,p)` for heat contractions
(`paper/main.tex` 7416–7425, 5205–5216; units B0419, B0420), Young `(11/3, 22/19, 22/3)` and
`(11/7, 2, 22/3)` for kernels outside a radial gap (8968–8975, 10381–10399, 11467–11484;
units B0559, B0761, B0795, B0975), `L¹ ⋆ L²` for the partial-strip kernel (10214–10242,
B0619), the pointwise Hölder bound against a kernel (8960–8967, B0561), and the
one-dimensional and cylinder mode kernels (2589–2598, 2672–2718; B0172, B0178).

Provenance. The majorant proof is copied from the compiled library file
`lean/UnforcedLeray/Analysis/Pressure/Young.lean` (itself a port of
`NonUniqueEuler/P/Infra/ConvMinkowski/YoungGeneral.lean`), with `Space` and `volume` replaced
by a general group `G` and measure `μ`; the endpoint statements are adapted from the reference
file `NonUniqueEuler/P/Infra/ConvMinkowski/Young.lean` (`convAbs_le_eLpNorm_top_mul`,
`convAbs_le_eLpNorm_mul_eLpNorm`, `eLpNorm_convAbs_le`) in the clone
`NonUniqueEuler/lean/NonUniqueEuler` (Apache-2.0; attribution in
`lean/NOTICE-NonUniqueEuler`). Minkowski's integral inequality is the vendored, compiled
`NonUniqueEuler.Conv.eLpNorm_lintegral_le`
(`lean/NonUniqueEuler/P/Infra/ConvMinkowski/Minkowski.lean`).

**Conventions.** `convAbs μ K g x = ∫⁻ ‖K(x-y)‖ ‖g(y)‖ dμ(y)` is `[0,∞]`-valued, so every
inequality below needs no integrability hypothesis; a divergent integral is `∞`, never a junk
`0`. The Bochner statements (`eLpNorm_convolution_le_young`, `eLpNorm_bilinConv_le_young`) bound
the literal Bochner convolution; where it is not integrable the Bochner junk value `0` only
lowers the left side, and `convolution_integrable_ae_young` shows that under finite input norms
the integrand is integrable for a.e. `x`.

**Main results.**
* `eLpNorm_convAbs_le_young`: `‖|K| ⋆ |g|‖_r ≤ ‖K‖_s ‖g‖_p`, `1 ≤ s,p,r < ∞`,
  `1/s + 1/p = 1 + 1/r`;
* `eLpNorm_convAbs_le_L1`: `‖|K| ⋆ |g|‖_p ≤ ‖K‖_1 ‖g‖_p` for `1 ≤ p ≤ ∞`;
* `convAbs_le_eLpNorm_top_mul`, `convAbs_le_lintegral_mul_essSup`,
  `convAbs_le_eLpNorm_mul_eLpNorm` (pointwise `L^∞·L¹`, `L¹·L^∞` and Hölder bounds);
* `convAbs_le_add_of_split` (split kernels);
* Bochner forms with scalar kernels (`•`) and with a continuous bilinear pairing `L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Conv

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The nonnegative convolution majorant `(|K| ⋆ |g|)(x) = ∫⁻ ‖K(x-y)‖ ‖g(y)‖ dμ(y)`, with value
`∞` where the integral diverges (scoping note INF22 A1). -/
def convAbs (μ : Measure G) (K : G → E) (g : G → F) (x : G) : ℝ≥0∞ :=
  ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ ∂μ

/-! ### Helpers (copied from `Pressure/Young.lean`, generalized) -/

/-- Three-factor Hölder inequality for `ℝ≥0∞`-valued functions, with weights summing to `1`. -/
theorem lintegral_three_rpow_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f₁ f₂ f₃ : α → ℝ≥0∞} (h₁ : AEMeasurable f₁ ν) (h₂ : AEMeasurable f₂ ν)
    (h₃ : AEMeasurable f₃ ν) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    ∫⁻ y, f₁ y ^ a * f₂ y ^ b * f₃ y ^ c ∂ν ≤
      (∫⁻ y, f₁ y ∂ν) ^ a * (∫⁻ y, f₂ y ∂ν) ^ b * (∫⁻ y, f₃ y ∂ν) ^ c := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (μ := ν) (Finset.univ : Finset (Fin 2))
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

variable (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

omit [μ.IsNegInvariant] in
/-- Joint measurability of `(x, y) ↦ ‖K (x - y)‖^s ‖g y‖^p`. -/
private theorem aemeasurable_prod_conv_rpow {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ) (s p : ℝ) :
    AEMeasurable (fun q : G × G => ‖K (q.1 - q.2)‖ₑ ^ s * ‖g q.2‖ₑ ^ p) (μ.prod μ) :=
  ((hK.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)).pow_const
    s).mul (hg.enorm.comp_snd.pow_const p)

omit [SigmaFinite μ] in
/-- For fixed `x`, `y ↦ ‖K (x - y)‖ₑ` is a.e.-measurable. -/
private theorem aemeasurable_enorm_sub_left {K : G → E} (hK : AEStronglyMeasurable K μ)
    (x : G) : AEMeasurable (fun y => ‖K (x - y)‖ₑ) μ :=
  hK.enorm.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving

omit [μ.IsNegInvariant] in
/-- Tonelli: `∫∫ ‖K (x - y)‖^s ‖g y‖^p dy dx = (∫ ‖K‖^s) (∫ ‖g‖^p)`. -/
private theorem lintegral_lintegral_conv_rpow {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ) (s p : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p ∂μ ∂μ =
      (∫⁻ z, ‖K z‖ₑ ^ s ∂μ) * ∫⁻ y, ‖g y‖ₑ ^ p ∂μ := by
  rw [lintegral_lintegral_swap (aemeasurable_prod_conv_rpow μ hK hg s p)]
  have hm : ∀ y : G, AEMeasurable (fun x => ‖K (x - y)‖ₑ ^ s) μ := fun y =>
    (hK.enorm.comp_quasiMeasurePreserving
      (measurePreserving_sub_right μ y).quasiMeasurePreserving).pow_const s
  have h2 : ∀ y : G, ∫⁻ x, ‖K (x - y)‖ₑ ^ s ∂μ = ∫⁻ z, ‖K z‖ₑ ^ s ∂μ := fun y =>
    lintegral_sub_right_eq_self (fun z => ‖K z‖ₑ ^ s) y
  calc ∫⁻ y, ∫⁻ x, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p ∂μ ∂μ
      = ∫⁻ y, (∫⁻ z, ‖K z‖ₑ ^ s ∂μ) * ‖g y‖ₑ ^ p ∂μ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const'' _ (hm y), h2 y]
    _ = (∫⁻ z, ‖K z‖ₑ ^ s ∂μ) * ∫⁻ y, ‖g y‖ₑ ^ p ∂μ :=
        lintegral_const_mul'' _ (hg.enorm.pow_const p)

omit [SigmaFinite μ] in
/-- Step 1: `(|K| ⋆ |g|)(x) ≤ Φ(x)^a (∫ ‖K‖^s)^b (∫ ‖g‖^p)^c`. -/
private theorem convAbs_le_three_rpow {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ)
    {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) (hsab : s * a + s * b = 1) (hpac : p * a + p * c = 1) (x : G) :
    convAbs μ K g x ≤ (∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p ∂μ) ^ a *
      (∫⁻ z, ‖K z‖ₑ ^ s ∂μ) ^ b * (∫⁻ y, ‖g y‖ₑ ^ p ∂μ) ^ c := by
  have hk := aemeasurable_enorm_sub_left μ hK x
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg.enorm
  have htr : ∫⁻ y, ‖K (x - y)‖ₑ ^ s ∂μ = ∫⁻ z, ‖K z‖ₑ ^ s ∂μ :=
    lintegral_sub_left_eq_self (fun z => ‖K z‖ₑ ^ s) x
  rw [← htr, convAbs]
  calc ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ ∂μ
      = ∫⁻ y, (‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p) ^ a * (‖K (x - y)‖ₑ ^ s) ^ b *
          (‖g y‖ₑ ^ p) ^ c ∂μ :=
        lintegral_congr fun y => mul_eq_three_rpow _ _ hs hp ha hb hc hsab hpac
    _ ≤ _ := lintegral_three_rpow_le ((hk.pow_const s).mul (hgm.pow_const p))
        (hk.pow_const s) (hgm.pow_const p) ha hb hc habc

/-! ### Young's inequality -/

/-- **Young's convolution inequality on a group** (INF22 A1, BP1):
`‖|K| ⋆ |g|‖_{L^r(μ)} ≤ ‖K‖_{L^s(μ)} ‖g‖_{L^p(μ)}` for real `1 ≤ s, p, r` with
`1/s + 1/p = 1 + 1/r`, as an inequality in `[0,∞]`. -/
theorem eLpNorm_convAbs_le_young {K : G → E} {g : G → F} (hK : AEStronglyMeasurable K μ)
    (hg : AEStronglyMeasurable g μ) {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (convAbs μ K g) (ENNReal.ofReal r) μ ≤
      eLpNorm K (ENNReal.ofReal s) μ * eLpNorm g (ENNReal.ofReal p) μ := by
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
  set A : ℝ≥0∞ := ∫⁻ z, ‖K z‖ₑ ^ s ∂μ with hA_def
  set B : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ p ∂μ with hB_def
  set Φ : G → ℝ≥0∞ := fun x => ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p ∂μ with hΦ_def
  have hΦm : AEMeasurable Φ μ := (aemeasurable_prod_conv_rpow μ hK hg s p).lintegral_prod_right'
  have hΦint : ∫⁻ x, Φ x ∂μ = A * B := lintegral_lintegral_conv_rpow μ hK hg s p
  have h3 : ∫⁻ x, convAbs μ K g x ^ r ∂μ ≤ A * B * (A ^ (b * r) * B ^ (c * r)) := by
    calc ∫⁻ x, convAbs μ K g x ^ r ∂μ
        ≤ ∫⁻ x, (Φ x ^ a * A ^ b * B ^ c) ^ r ∂μ := by
          refine lintegral_mono fun x => ?_
          exact ENNReal.rpow_le_rpow
            (convAbs_le_three_rpow μ hK hg hs0.le hp0.le ha hb hc habc hsab hpac x) hr0.le
      _ = ∫⁻ x, Φ x * (A ^ (b * r) * B ^ (c * r)) ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, har, ENNReal.rpow_one,
            mul_assoc]
      _ = A * B * (A ^ (b * r) * B ^ (c * r)) := by
          rw [lintegral_mul_const'' _ hΦm, hΦint]
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
  calc (∫⁻ x, convAbs μ K g x ^ r ∂μ) ^ (1 / r)
      ≤ (A * B * (A ^ (b * r) * B ^ (c * r))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h3 (by positivity)
    _ = A ^ (1 / s) * B ^ (1 / p) := by
        rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, hexpA, hexpB]

omit [μ.IsNegInvariant] in
/-- The nonnegative convolution majorant is a.e. measurable. -/
theorem aemeasurable_convAbs {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (convAbs μ K g) μ :=
  ((hK.enorm.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub μ μ)).mul hg.enorm.comp_snd).lintegral_prod_right'

omit [SigmaFinite μ] in
/-- For fixed `x`, the integrand `y ↦ ‖K (x - y)‖ ‖g y‖` is a.e. measurable. -/
theorem aemeasurable_convAbs_integrand {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ) (x : G) :
    AEMeasurable (fun y => ‖K (x - y)‖ₑ * ‖g y‖ₑ) μ :=
  (aemeasurable_enorm_sub_left μ hK x).mul hg.enorm

/-- Under Young's finite-norm hypotheses the majorant is finite almost everywhere. -/
theorem convAbs_lt_top_ae_young {K : G → E} {g : G → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    ∀ᵐ x ∂μ, convAbs μ K g x < ∞ := by
  have hr0 : 0 < r := by linarith
  have hrne : ENNReal.ofReal r ≠ 0 := by simp [hr0]
  have hfinite : eLpNorm (convAbs μ K g) (ENNReal.ofReal r) μ < ∞ :=
    (eLpNorm_convAbs_le_young μ hK.1 hg.1 hs hp hr hspr).trans_lt
      (ENNReal.mul_lt_top hK.2 hg.2)
  have hpower : ∫⁻ x, convAbs μ K g x ^ (ENNReal.ofReal r).toReal ∂μ < ∞ := by
    simpa only [enorm_eq_self] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hrne ENNReal.ofReal_ne_top hfinite
  filter_upwards [ae_lt_top' ((aemeasurable_convAbs μ hK.1 hg.1).pow_const _) hpower.ne]
    with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos
    (ENNReal.toReal_pos hrne ENNReal.ofReal_ne_top)).mp hx

/-! ### Substitution, pointwise bounds and endpoints -/

omit [SigmaFinite μ] in
/-- `(|K| ⋆ |g|)(x) = ∫⁻ ‖K(z)‖ ‖g(x - z)‖ dμ(z)`. -/
theorem convAbs_eq_lintegral_sub (K : G → E) (g : G → F) (x : G) :
    convAbs μ K g x = ∫⁻ z, ‖K z‖ₑ * ‖g (x - z)‖ₑ ∂μ := by
  have h := (Measure.measurePreserving_sub_left μ x).lintegral_comp_emb
    (MeasurableEquiv.subLeft x).measurableEmbedding (fun y => ‖K (x - y)‖ₑ * ‖g y‖ₑ)
  simp only [sub_sub_cancel] at h
  rw [convAbs, ← h]

omit [SigmaFinite μ] in
/-- Pointwise `L¹ · L^∞`: `(|K| ⋆ |g|)(x) ≤ ‖K‖₁ ‖g‖_∞` for every `x`. -/
theorem convAbs_le_lintegral_mul_essSup {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (x : G) :
    convAbs μ K g x ≤ (∫⁻ z, ‖K z‖ₑ ∂μ) * eLpNormEssSup g μ := by
  rw [convAbs_eq_lintegral_sub, ← lintegral_mul_const'' _ hK.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae
    (ae_le_eLpNormEssSup (f := g))] with z hz
  gcongr

omit [SigmaFinite μ] in
/-- Pointwise `L^∞ · L¹`: `(|K| ⋆ |g|)(x) ≤ ‖K‖_∞ ‖g‖₁` for every `x`. -/
theorem convAbs_le_eLpNorm_top_mul {K : G → E} {g : G → F}
    (hg : AEStronglyMeasurable g μ) (x : G) :
    convAbs μ K g x ≤ eLpNorm K ⊤ μ * eLpNorm g 1 μ := by
  rw [convAbs, eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul'' _ hg.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae
    (ae_le_eLpNormEssSup (f := K))] with y hy
  gcongr

omit [SigmaFinite μ] in
/-- Pointwise Hölder: `(|K| ⋆ |g|)(x) ≤ ‖K‖_p ‖g‖_q` for every `x`, `1/p + 1/q = 1`
(used against kernels outside a gap, `paper/main.tex` 8960–8967, unit B0561). -/
theorem convAbs_le_eLpNorm_mul_eLpNorm {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ)
    {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) (x : G) :
    convAbs μ K g x ≤ eLpNorm K p μ * eLpNorm g q μ := by
  have hmp := Measure.measurePreserving_sub_left μ x
  have hK' : AEStronglyMeasurable (fun y => K (x - y)) μ := hK.comp_measurePreserving hmp
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := μ) (p := p) (q := q) (r := 1)
    hK' hg (fun a b => ‖a‖ * ‖b‖) 1 (Eventually.of_forall fun y => by simp) (hpqr := hpq)
  have hKeq : eLpNorm (fun y => K (x - y)) p μ = eLpNorm K p μ :=
    eLpNorm_comp_measurePreserving (f := fun y => x - y) hK hmp
  rw [hKeq, ENNReal.coe_one, one_mul, eLpNorm_one_eq_lintegral_enorm] at h
  refine le_of_eq_of_le ?_ h
  rw [convAbs]
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, enorm_norm, enorm_norm]

omit [SigmaFinite μ] in
/-- Split kernel: `|K| ⋆ |g| ≤ |K₁| ⋆ |g| + |K₂| ⋆ |g|` pointwise when `‖K‖ ≤ ‖K₁‖ + ‖K₂‖`. -/
theorem convAbs_le_add_of_split {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] {K : G → E} {K₁ : G → E₁} {K₂ : G → E₂}
    (hK₁ : AEStronglyMeasurable K₁ μ) (hsplit : ∀ z, ‖K z‖ ≤ ‖K₁ z‖ + ‖K₂ z‖)
    {g : G → F} (hg : AEStronglyMeasurable g μ) (x : G) :
    convAbs μ K g x ≤ convAbs μ K₁ g x + convAbs μ K₂ g x := by
  have hle : ∀ z, ‖K z‖ₑ ≤ ‖K₁ z‖ₑ + ‖K₂ z‖ₑ := fun z => by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hsplit z)
  calc convAbs μ K g x
      ≤ ∫⁻ y, ‖K₁ (x - y)‖ₑ * ‖g y‖ₑ + ‖K₂ (x - y)‖ₑ * ‖g y‖ₑ ∂μ := by
        refine lintegral_mono fun y => ?_
        rw [← add_mul]
        gcongr
        exact hle _
    _ = convAbs μ K₁ g x + convAbs μ K₂ g x :=
        lintegral_add_left' (aemeasurable_convAbs_integrand μ hK₁ hg x) _

omit [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- Pointwise monotonicity in the kernel: `‖K‖ ≤ ‖K'‖` gives `|K| ⋆ |g| ≤ |K'| ⋆ |g|`. -/
theorem convAbs_mono_kernel {E' : Type*} [NormedAddCommGroup E'] {K : G → E} {K' : G → E'}
    (hKK' : ∀ z, ‖K z‖ ≤ ‖K' z‖) (g : G → F) (x : G) :
    convAbs μ K g x ≤ convAbs μ K' g x := by
  refine lintegral_mono fun y => ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hKK' _)

/-- **`L¹ ⋆ L^p`** (INF22 A1): `‖|K| ⋆ |g|‖_{L^p(μ)} ≤ (∫⁻ ‖K‖ dμ) ‖g‖_{L^p(μ)}` for
`1 ≤ p ≤ ∞` (heat contractions, `paper/main.tex` 7416–7425, 5205–5216). -/
theorem eLpNorm_convAbs_le_L1 {K : G → E} {g : G → F} (hK : AEStronglyMeasurable K μ)
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (convAbs μ K g) p μ ≤ (∫⁻ z, ‖K z‖ₑ ∂μ) * eLpNorm g p μ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine essSup_le_of_ae_le _ (Eventually.of_forall fun x => ?_)
    change ‖convAbs μ K g x‖ₑ ≤ _
    rw [enorm_eq_self]
    exact convAbs_le_lintegral_mul_essSup μ hK x
  have hprod : AEMeasurable (Function.uncurry fun x z => ‖K z‖ₑ * ‖g (x - z)‖ₑ) (μ.prod μ) :=
    hK.enorm.comp_snd.mul
      (hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ))
  have hmink := NonUniqueEuler.Conv.eLpNorm_lintegral_le (μ := μ) (ν := μ)
    (F := fun x z => ‖K z‖ₑ * ‖g (x - z)‖ₑ) hprod hp hp'
  have hfun : convAbs μ K g = fun x => ∫⁻ z, ‖K z‖ₑ * ‖g (x - z)‖ₑ ∂μ :=
    funext (convAbs_eq_lintegral_sub μ K g)
  rw [hfun]
  refine hmink.trans ?_
  calc ∫⁻ z, eLpNorm (fun x => ‖K z‖ₑ * ‖g (x - z)‖ₑ) p μ ∂μ
      ≤ ∫⁻ z, ‖K z‖ₑ * eLpNorm g p μ ∂μ := by
        refine lintegral_mono fun z => ?_
        have h1 : eLpNorm (fun x => ‖K z‖ₑ * ‖g (x - z)‖ₑ) p μ ≤
            ‖K z‖₊ • eLpNorm (fun x => g (x - z)) p μ :=
          eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
            (Eventually.of_forall fun x => by rw [enorm_eq_self]; rfl) p
        have h2 : eLpNorm (fun x => g (x - z)) p μ = eLpNorm g p μ :=
          eLpNorm_comp_measurePreserving (f := fun x => x - z) hg
            (measurePreserving_sub_right μ z)
        rw [h2] at h1
        exact h1
    _ = (∫⁻ z, ‖K z‖ₑ ∂μ) * eLpNorm g p μ := lintegral_mul_const'' _ hK.enorm

/-- `L¹ ⋆ L^p` in `eLpNorm` form: `‖|K| ⋆ |g|‖_p ≤ ‖K‖_1 ‖g‖_p`, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_convAbs_le_eLpNorm_one {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (convAbs μ K g) p μ ≤ eLpNorm K 1 μ * eLpNorm g p μ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_convAbs_le_L1 μ hK hg hp

/-! ### Bochner convolutions -/

section Bochner

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] [NormedSpace ℝ F]

omit [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- The Bochner convolution with a scalar kernel is bounded pointwise by the majorant. -/
theorem enorm_convolution_le_convAbs (K : G → 𝕜) (f : G → F) (x : G) :
    ‖∫ y, K (x - y) • f y ∂μ‖ₑ ≤ convAbs μ K f x := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [convAbs]
  refine lintegral_congr fun y => ?_
  rw [enorm_smul]

omit [μ.IsNegInvariant] in
/-- Joint measurability gives measurability of the Bochner convolution with a scalar kernel. -/
theorem aestronglyMeasurable_convolution [CompleteSpace F] {K : G → 𝕜} {f : G → F}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) • f y ∂μ) μ :=
  ((hK.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub μ μ)).smul hf.comp_snd).integral_prod_right'

omit [NormedSpace ℝ F] in
/-- Under Young's finite-norm hypotheses the convolution integrand is integrable for a.e. `x`. -/
theorem convolution_integrable_ae_young {K : G → 𝕜} {f : G → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) μ) (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x - y) • f y) μ := by
  filter_upwards [convAbs_lt_top_ae_young μ hs hp hr hspr hK hf] with x hx
  refine ⟨(hK.1.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving).smul hf.1, ?_⟩
  simpa only [HasFiniteIntegral, enorm_smul, convAbs] using hx

/-- **Young's inequality for the Bochner convolution** `x ↦ ∫ K(x-y) • f(y) dμ(y)`. -/
theorem eLpNorm_convolution_le_young {K : G → 𝕜} {f : G → F}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ)
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (fun x => ∫ y, K (x - y) • f y ∂μ) (ENNReal.ofReal r) μ ≤
      eLpNorm K (ENNReal.ofReal s) μ * eLpNorm f (ENNReal.ofReal p) μ :=
  (eLpNorm_mono_enorm (g := convAbs μ K f) fun x => by
      rw [enorm_eq_self]; exact enorm_convolution_le_convAbs μ K f x).trans
    (eLpNorm_convAbs_le_young μ hK hf hs hp hr hspr)

/-- `L¹ ⋆ L^p` for the Bochner convolution, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_convolution_le_L1 {K : G → 𝕜} {f : G → F}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, K (x - y) • f y ∂μ) p μ ≤ eLpNorm K 1 μ * eLpNorm f p μ :=
  (eLpNorm_mono_enorm (g := convAbs μ K f) fun x => by
      rw [enorm_eq_self]; exact enorm_convolution_le_convAbs μ K f x).trans
    (eLpNorm_convAbs_le_eLpNorm_one μ hK hf hp)

/-- Finite input norms give `L^r` membership of the Bochner convolution. -/
theorem convolution_memLp_young [CompleteSpace F] {K : G → 𝕜} {f : G → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) μ) (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => ∫ y, K (x - y) • f y ∂μ) (ENNReal.ofReal r) μ :=
  ⟨aestronglyMeasurable_convolution μ hK.1 hf.1,
    (eLpNorm_convolution_le_young μ hK.1 hf.1 hs hp hr hspr).trans_lt
      (ENNReal.mul_lt_top hK.2 hf.2)⟩

/-- Young's inequality for finite real-valued norms. -/
theorem convolution_norm_le_young {K : G → 𝕜} {f : G → F}
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r)
    (hK : MemLp K (ENNReal.ofReal s) μ) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm (fun x => ∫ y, K (x - y) • f y ∂μ) (ENNReal.ofReal r) μ).toReal ≤
      (eLpNorm K (ENNReal.ofReal s) μ).toReal * (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  simpa only [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hK.2.ne hf.2.ne)
      (eLpNorm_convolution_le_young μ hK.1 hf.1 hs hp hr hspr)

end Bochner

section Bilinear

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℝ E]
  [NormedSpace ℝ F]

omit [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- The Bochner convolution through a continuous bilinear pairing `L` (matrix kernels acting on
vectors, tensor pairings) is bounded pointwise by `‖L‖` times the majorant. -/
theorem enorm_bilinConv_le_convAbs (L : E →L[ℝ] F →L[ℝ] F') (K : G → E) (f : G → F) (x : G) :
    ‖∫ y, L (K (x - y)) (f y) ∂μ‖ₑ ≤ ‖L‖₊ * convAbs μ K f x := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [convAbs, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← mul_assoc, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal (L.le_opNorm₂ _ _)

/-- **Young's inequality for a bilinear convolution**
`‖x ↦ ∫ L(K(x-y), f(y)) dμ(y)‖_r ≤ ‖L‖ ‖K‖_s ‖f‖_p`. -/
theorem eLpNorm_bilinConv_le_young (L : E →L[ℝ] F →L[ℝ] F') {K : G → E} {f : G → F}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ)
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (fun x => ∫ y, L (K (x - y)) (f y) ∂μ) (ENNReal.ofReal r) μ ≤
      ‖L‖₊ * (eLpNorm K (ENNReal.ofReal s) μ * eLpNorm f (ENNReal.ofReal p) μ) := by
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (μ := μ) (c := ‖L‖₊)
    (f := fun x => ∫ y, L (K (x - y)) (f y) ∂μ) (g := convAbs μ K f)
    (Eventually.of_forall fun x => by
      rw [enorm_eq_self]; exact enorm_bilinConv_le_convAbs μ L K f x) (ENNReal.ofReal r)
  refine h.trans ?_
  rw [ENNReal.smul_def, smul_eq_mul]
  gcongr
  exact eLpNorm_convAbs_le_young μ hK hf hs hp hr hspr

/-- `L¹ ⋆ L^p` for a bilinear convolution, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_bilinConv_le_L1 (L : E →L[ℝ] F →L[ℝ] F') {K : G → E} {f : G → F}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, L (K (x - y)) (f y) ∂μ) p μ ≤
      ‖L‖₊ * (eLpNorm K 1 μ * eLpNorm f p μ) := by
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (μ := μ) (c := ‖L‖₊)
    (f := fun x => ∫ y, L (K (x - y)) (f y) ∂μ) (g := convAbs μ K f)
    (Eventually.of_forall fun x => by
      rw [enorm_eq_self]; exact enorm_bilinConv_le_convAbs μ L K f x) p
  refine h.trans ?_
  rw [ENNReal.smul_def, smul_eq_mul]
  gcongr
  exact eLpNorm_convAbs_le_eLpNorm_one μ hK hf hp

end Bilinear

end UnforcedLeray.Conv
