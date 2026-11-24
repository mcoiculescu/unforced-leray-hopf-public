import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Real.ConjExponents

/-!
# B0276 `mixed-background:C.4`: weighted `L^p` to `L^1` age embedding

Unit B0276 of `paper/main.tex`, label `mixed-background:C.4`, tex lines 4783–4794
(the exponents and the norm are fixed at tex lines 4749–4754, and `b = -9/8 + p` is
recalled at tex line 4776).

Statement in words. Fix `p = 11/4` and `b = 13/8` and, for a cutoff age `S`, put
`‖k‖_{p,b;Y} = (∫_0^S s^b ‖k(s)‖_Y^p ds)^{1/p}`. Then for every Banach space `Y` and every
strongly measurable `k : (0,S) → Y`,
`‖k‖_{L^1(0,S;Y)} ≤ 14^{7/11} S^{1/22} ‖k‖_{p,b;Y}`. The proof is Hölder's inequality
with the conjugate exponent `p' = 11/7` applied to `‖k‖ = s^{-b/p} · s^{b/p}‖k‖`; the second
Hölder factor is `(∫_0^S s^{-b/(p-1)} ds)^{1/p'} = (14 S^{1/14})^{7/11} = 14^{7/11} S^{1/22}`,
since `b/(p-1) = 13/14`.

Lean conventions. The age interval `(0,S)` is `Set.Ioo 0 S` with Lebesgue measure. Both norms
are taken in `ℝ≥0∞`, so no integrability is assumed and no junk value enters: the `L^1` norm is
Mathlib's `eLpNorm k 1`, and `‖k‖_{p,b;Y}` is `weightedAgeNorm p b S k`, a lower Lebesgue
integral. The only hypothesis is the strong (Bochner) measurability of `k` on `(0,S)`, which
is part of the meaning of `L^1(0,S;Y)` in the manuscript. The inequality needs only a normed
group `Y`, so in particular it holds for every Banach space. For `S ≤ 0` the interval is empty
and the statements are trivial, so no sign hypothesis on `S` is needed. A real-valued form
(with the Bochner integrals, under the integrability of `s^b ‖k(s)‖^p`, which is what makes
the real-valued norm non-junk) and the consequence `k ∈ L^1(0,S;Y)` ("the source lies in
age `L^1`", tex line 4782) are also proved. The general Hölder step is proved for every
`p > 1` and every real `b`; the stated constant is specific to `p = 11/4`, `b = 13/8`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.B0276

variable {Y : Type*} [NormedAddCommGroup Y]

/-- The weighted age norm `‖k‖_{p,b;Y} := (∫_0^S s^b ‖k(s)‖_Y^p ds)^{1/p}` of tex lines
4753–4754, as an element of `ℝ≥0∞` (a lower Lebesgue integral, so no integrability is
presupposed). -/
def weightedAgeNorm (p b S : ℝ) (k : ℝ → Y) : ℝ≥0∞ :=
  (∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ b) * ‖k s‖ₑ ^ p) ^ (1 / p)

/-! ### The fixed exponents (tex lines 4749–4752 and 4776) -/

/-- Tex line 4776: `b = -9/8 + p` for `p = 11/4`, `b = 13/8`. -/
theorem weight_eq : (13 / 8 : ℝ) = -9 / 8 + 11 / 4 := by norm_num

/-- Tex line 4793: the Hölder conjugate of `p = 11/4` is `p' = 11/7`. -/
theorem conjExponent_eq : Real.conjExponent (11 / 4 : ℝ) = 11 / 7 := by
  unfold Real.conjExponent; norm_num

/-- `p = 11/4` and `p' = 11/7` are Hölder conjugate. -/
theorem holderConjugate : (11 / 4 : ℝ).HolderConjugate (11 / 7) := by
  rw [← conjExponent_eq]
  exact Real.HolderConjugate.conjExponent (by norm_num)

/-- The exponent in Hölder's second factor (tex line 4791): `b/(p-1) = 13/14`. -/
theorem weight_div_eq : (13 / 8 : ℝ) / (11 / 4 - 1) = 13 / 14 := by norm_num

/-! ### Hölder with a power weight, for general exponents -/

/-- Hölder's inequality with a power weight on the age interval `(0,S)`, for any `p > 1` and
any real `b`, with conjugate exponent `p' = p/(p-1)`:
`∫_0^S ‖k‖ ≤ (∫_0^S s^{-b/(p-1)} ds)^{1/p'} ‖k‖_{p,b;Y}`. This is the argument of tex lines
4787–4793 before the exponents are specialized. All integrals are lower Lebesgue integrals. -/
theorem lintegral_enorm_le_holder {p b S : ℝ} (hp : 1 < p) {k : ℝ → Y}
    (hk : AEMeasurable (fun s => ‖k s‖ₑ) (volume.restrict (Ioo 0 S))) :
    ∫⁻ s in Ioo 0 S, ‖k s‖ₑ ≤
      (∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(b / (p - 1))))) ^ ((p - 1) / p) *
        weightedAgeNorm p b S k := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hq0 : (0 : ℝ) ≤ p / (p - 1) := hpq.symm.nonneg
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-(b / p))) with hf_def
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (b / p)) * ‖k s‖ₑ with hg_def
  have hfm : AEMeasurable f (volume.restrict (Ioo 0 S)) := by
    have : Measurable f := by
      rw [hf_def]
      fun_prop
    exact this.aemeasurable
  have hgm : AEMeasurable g (volume.restrict (Ioo 0 S)) := by
    have : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (b / p)) := by fun_prop
    exact this.aemeasurable.mul hk
  -- factor `‖k‖ = s^{-b/p} · (s^{b/p} ‖k‖)` on `(0,S)`
  have h1 : ∫⁻ s in Ioo 0 S, ‖k s‖ₑ = ∫⁻ s in Ioo 0 S, (f * g) s := by
    refine setLIntegral_congr_fun measurableSet_Ioo ?_
    intro s hs
    have hs0 : 0 < s := hs.1
    simp only [Pi.mul_apply, hf_def, hg_def]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _),
      ← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  -- the first Hölder factor
  have h2 : ∫⁻ s in Ioo 0 S, f s ^ (p / (p - 1)) =
      ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(b / (p - 1)))) := by
    refine setLIntegral_congr_fun measurableSet_Ioo ?_
    intro s hs
    have hs0 : 0 < s := hs.1
    simp only [hf_def]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) hq0,
      ← Real.rpow_mul hs0.le]
    congr 2
    field_simp
  -- the second Hölder factor is the weighted norm
  have h3 : ∫⁻ s in Ioo 0 S, g s ^ p =
      ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ b) * ‖k s‖ₑ ^ p := by
    refine setLIntegral_congr_fun measurableSet_Ioo ?_
    intro s hs
    have hs0 : 0 < s := hs.1
    simp only [hg_def]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) hp0.le,
      ← Real.rpow_mul hs0.le]
    congr 3
    field_simp
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo 0 S)) hpq.symm hfm hgm
  rw [h1]
  calc ∫⁻ s in Ioo 0 S, (f * g) s
      ≤ (∫⁻ s in Ioo 0 S, f s ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) *
          (∫⁻ s in Ioo 0 S, g s ^ p) ^ (1 / p) := hH
    _ = (∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(b / (p - 1))))) ^ ((p - 1) / p) *
          weightedAgeNorm p b S k := by
        rw [h2, h3, one_div_div]
        rfl

/-! ### The second Hölder factor for `p = 11/4`, `b = 13/8` -/

/-- `∫_0^S s^{-13/14} ds = 14 S^{1/14}` (Bochner form; the integrand is integrable). -/
theorem integral_rpow_neg_thirteen_fourteenths {S : ℝ} (hS : 0 < S) :
    ∫ s in Ioo 0 S, s ^ (-(13 / 14 : ℝ)) = 14 * S ^ (1 / 14 : ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hS.le,
    integral_rpow (Or.inl (by norm_num))]
  have h : (-(13 / 14 : ℝ) + 1) = 1 / 14 := by norm_num
  rw [h, Real.zero_rpow (by norm_num)]
  ring

/-- `s ↦ s^{-13/14}` is integrable on `(0,S)`. -/
theorem integrableOn_rpow_neg_thirteen_fourteenths {S : ℝ} (hS : 0 < S) :
    IntegrableOn (fun s : ℝ => s ^ (-(13 / 14 : ℝ))) (Ioo 0 S) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff hS).2 (by norm_num)

/-- `∫_0^S s^{-13/14} ds = 14 S^{1/14}` as a lower Lebesgue integral. -/
theorem lintegral_rpow_neg_thirteen_fourteenths {S : ℝ} (hS : 0 < S) :
    ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(13 / 14 : ℝ))) =
      ENNReal.ofReal (14 * S ^ (1 / 14 : ℝ)) := by
  rw [← integral_rpow_neg_thirteen_fourteenths hS,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_neg_thirteen_fourteenths hS)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact Real.rpow_nonneg hs.1.le _

/-- `(14 S^{1/14})^{7/11} = 14^{7/11} S^{1/22}` (tex lines 4786 and 4792). -/
theorem second_factor_simplify {S : ℝ} (hS : 0 ≤ S) :
    (14 * S ^ (1 / 14 : ℝ)) ^ (7 / 11 : ℝ) = (14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hS _), ← Real.rpow_mul hS]
  norm_num

/-- Tex lines 4789–4793: Hölder's second factor for `p = 11/4`, `b = 13/8`,
`p' = 11/7`: `(∫_0^S s^{-b/(p-1)} ds)^{1/p'} = (14 S^{1/14})^{7/11}`, and this equals
`14^{7/11} S^{1/22}`. The exponents are written exactly as in the manuscript. -/
theorem holder_second_factor {S : ℝ} (hS : 0 < S) :
    (∫ s in Ioo 0 S, s ^ (-((13 / 8 : ℝ) / (11 / 4 - 1)))) ^ (1 / Real.conjExponent (11 / 4)) =
        (14 * S ^ (1 / 14 : ℝ)) ^ (7 / 11 : ℝ) ∧
      (14 * S ^ (1 / 14 : ℝ)) ^ (7 / 11 : ℝ) = (14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ) := by
  refine ⟨?_, second_factor_simplify hS.le⟩
  rw [weight_div_eq, conjExponent_eq, integral_rpow_neg_thirteen_fourteenths hS]
  norm_num

/-! ### The embedding (C.4) -/

/-- **Tex line 4784, `mixed-background:C.4`.** For `p = 11/4`, `b = 13/8` and any
strongly measurable `k : (0,S) → Y` into a normed group (in particular a Banach space),
`‖k‖_{L^1(0,S;Y)} ≤ 14^{7/11} S^{1/22} ‖k‖_{p,b;Y}`. Both sides are in `ℝ≥0∞`; no
integrability is assumed, and if `‖k‖_{p,b;Y} = ∞` the inequality is trivial. -/
theorem eLpNorm_one_le_weightedAgeNorm {S : ℝ} {k : ℝ → Y}
    (hk : AEStronglyMeasurable k (volume.restrict (Ioo 0 S))) :
    eLpNorm k 1 (volume.restrict (Ioo 0 S)) ≤
      ENNReal.ofReal ((14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ)) *
        weightedAgeNorm (11 / 4) (13 / 8) S k := by
  rcases le_or_gt S 0 with hS | hS
  · rw [Ioo_eq_empty (not_lt.mpr hS), Measure.restrict_empty, eLpNorm_measure_zero]
    exact zero_le
  rw [eLpNorm_one_eq_lintegral_enorm]
  refine (lintegral_enorm_le_holder (p := 11 / 4) (b := 13 / 8) (by norm_num) hk.enorm).trans
    (le_of_eq ?_)
  rw [weight_div_eq, lintegral_rpow_neg_thirteen_fourteenths hS,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  have h : ((11 / 4 : ℝ) - 1) / (11 / 4) = 7 / 11 := by norm_num
  rw [h, second_factor_simplify hS.le]

/-- Tex line 4782 ("the source lies in age `L^1`"), from (C.4): a strongly measurable `k`
with `‖k‖_{p,b;Y} < ∞` (`p = 11/4`, `b = 13/8`) is Bochner integrable on `(0,S)`. -/
theorem integrableOn_of_weightedAgeNorm_lt_top {S : ℝ} {k : ℝ → Y}
    (hk : AEStronglyMeasurable k (volume.restrict (Ioo 0 S)))
    (hfin : weightedAgeNorm (11 / 4) (13 / 8) S k < ∞) :
    IntegrableOn k (Ioo 0 S) := by
  refine memLp_one_iff_integrable.mp ⟨hk, ?_⟩
  exact (eLpNorm_one_le_weightedAgeNorm hk).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- On `(0,S)` the weighted integrand in `ℝ≥0∞` is the `ofReal` of the real integrand
`s^b ‖k(s)‖^p` (for `p ≥ 0`). -/
theorem lintegral_weight_eq_lintegral_ofReal {p b S : ℝ} (hp : 0 ≤ p) (k : ℝ → Y) :
    ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ b) * ‖k s‖ₑ ^ p =
      ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ b * ‖k s‖ ^ p) := by
  refine setLIntegral_congr_fun measurableSet_Ioo ?_
  intro s hs
  simp only
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp, ofReal_norm]

/-- **Tex line 4784, `mixed-background:C.4`, real-valued form.** Let `p = 11/4`,
`b = 13/8`, let `k : (0,S) → Y` be strongly measurable and let `s ↦ s^b ‖k(s)‖^p` be
integrable on `(0,S)` (so that `‖k‖_{p,b;Y}` below is the real number of tex line 4753 and
not a junk value). Then `k ∈ L^1(0,S;Y)` and
`∫_0^S ‖k(s)‖ ds ≤ 14^{7/11} S^{1/22} (∫_0^S s^b ‖k(s)‖^p ds)^{1/p}`. -/
theorem integral_norm_le_weightedAgeNorm {S : ℝ} {k : ℝ → Y}
    (hk : AEStronglyMeasurable k (volume.restrict (Ioo 0 S)))
    (hw : IntegrableOn (fun s => s ^ (13 / 8 : ℝ) * ‖k s‖ ^ (11 / 4 : ℝ)) (Ioo 0 S)) :
    IntegrableOn k (Ioo 0 S) ∧
      ∫ s in Ioo 0 S, ‖k s‖ ≤
        (14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ) *
          (∫ s in Ioo 0 S, s ^ (13 / 8 : ℝ) * ‖k s‖ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) := by
  rcases le_or_gt S 0 with hS | hS
  · have hE : Ioo (0 : ℝ) S = ∅ := Ioo_eq_empty (not_lt.mpr hS)
    refine ⟨by rw [hE]; exact integrableOn_empty, ?_⟩
    rw [hE]
    simp
  set I := ∫ s in Ioo 0 S, s ^ (13 / 8 : ℝ) * ‖k s‖ ^ (11 / 4 : ℝ) with hI_def
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 S)]
      fun s => s ^ (13 / 8 : ℝ) * ‖k s‖ ^ (11 / 4 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hI0 : 0 ≤ I := integral_nonneg_of_ae hnn
  have hW : weightedAgeNorm (11 / 4) (13 / 8) S k = ENNReal.ofReal (I ^ (1 / (11 / 4 : ℝ))) := by
    unfold weightedAgeNorm
    rw [lintegral_weight_eq_lintegral_ofReal (by norm_num), ← ofReal_integral_eq_lintegral_ofReal hw hnn,
      ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num)]
  have hint : IntegrableOn k (Ioo 0 S) :=
    integrableOn_of_weightedAgeNorm_lt_top hk (by rw [hW]; exact ENNReal.ofReal_lt_top)
  refine ⟨hint, ?_⟩
  have hC : 0 ≤ (14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ) := by positivity
  have hmain := eLpNorm_one_le_weightedAgeNorm hk
  rw [eLpNorm_one_eq_lintegral_enorm, hW, ← ENNReal.ofReal_mul hC] at hmain
  have hL : ENNReal.ofReal (∫ s in Ioo 0 S, ‖k s‖) = ∫⁻ s in Ioo 0 S, ‖k s‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint.norm (Filter.Eventually.of_forall
      fun s => norm_nonneg _)]
    simp_rw [ofReal_norm]
  rw [← hL] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg hI0 _))).1 hmain

end UnforcedLeray.B0276
