import UnforcedLeray.Lib.ConvIneq.YoungGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Peetre's inequality and weighted Young (INF22 A2; built once per decision D14)

Blueprint infrastructure target **INF22 A2** of the scoping note

Decision D14 of `scoping/README.md` §3: Peetre's inequality is built once, here.

**Statement.** For `m ≥ 0` and `x, y` in a normed group,
`(1 + ‖x‖²)^{m/2} ≤ 2^{m/2} (1 + ‖x - y‖²)^{m/2} (1 + ‖y‖²)^{m/2}`
(`one_add_sq_rpow_le`), and for every real `s`,
`(1 + ‖x‖²)^{s/2} ≤ 2^{|s|/2} (1 + ‖x - y‖²)^{|s|/2} (1 + ‖y‖²)^{s/2}` (`peetre`).
The base case is `1 + ‖x‖² ≤ 2 (1 + ‖x - y‖²)(1 + ‖y‖²)`, from `‖x‖ ≤ ‖x - y‖ + ‖y‖` and
`(a + b)² ≤ 2a² + 2b²`.

**Weighted Young.** With `⟨x⟩^m = (1 + ‖x‖²)^{m/2}`, Peetre gives the pointwise bound
`⟨x⟩^m (|K| ⋆ |g|)(x) ≤ 2^{m/2} (|⟨·⟩^m K| ⋆ |⟨·⟩^m g|)(x)`, hence
`‖⟨·⟩^m (|K| ⋆ |g|)‖_r ≤ 2^{m/2} ‖⟨·⟩^m K‖_s ‖⟨·⟩^m g‖_p` (`eLpNorm_japanese_mul_convAbs_le`).
Manuscript uses: the weighted mode-kernel Young bounds of `paper/main.tex` 2589–2598 and
2672–2718 (units B0172, B0178: "weighted L¹ norms ≤ C_m(1 + |k_n|^{-m}), followed by weighted
Young and Parseval"), and the weighted cylinder kernel bounds (INF22 K9, folded into INF13 CY10).

The norm is the norm of the group: on `Plane = ℝ × ℝ` that is the sup norm (scoping note §6,
risk 4), and the inequality holds for it as stated.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Conv

section Peetre

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The base case of Peetre's inequality: `1 + ‖x‖² ≤ 2 (1 + ‖x - y‖²)(1 + ‖y‖²)`. -/
theorem one_add_sq_le_two_mul (x y : E) :
    1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
  have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa using norm_add_le (x - y) y
  have ha := norm_nonneg (x - y)
  have hb := norm_nonneg y
  have hx := norm_nonneg x
  have h2 : ‖x‖ ^ 2 ≤ (‖x - y‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ hx h1 2
  nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x - y‖) (sq_nonneg ‖y‖)]

/-- **Peetre's inequality** (INF22 A2), nonnegative exponent:
`(1 + ‖x‖²)^{m/2} ≤ 2^{m/2} (1 + ‖x - y‖²)^{m/2} (1 + ‖y‖²)^{m/2}` for `m ≥ 0`. -/
theorem one_add_sq_rpow_le (m : ℝ) (hm : 0 ≤ m) (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (m / 2) ≤ 2 ^ (m / 2) * (1 + ‖x - y‖ ^ 2) ^ (m / 2) *
      (1 + ‖y‖ ^ 2) ^ (m / 2) := by
  have hm2 : 0 ≤ m / 2 := by linarith
  calc (1 + ‖x‖ ^ 2) ^ (m / 2)
      ≤ (2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖y‖ ^ 2)) ^ (m / 2) :=
        Real.rpow_le_rpow (by positivity) (one_add_sq_le_two_mul x y) hm2
    _ = 2 ^ (m / 2) * (1 + ‖x - y‖ ^ 2) ^ (m / 2) * (1 + ‖y‖ ^ 2) ^ (m / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]

/-- Peetre's inequality with a negative exponent:
`(1 + ‖y‖²)^{-m/2} ≤ 2^{m/2} (1 + ‖x - y‖²)^{m/2} (1 + ‖x‖²)^{-m/2}` for `m ≥ 0`. -/
theorem one_add_sq_rpow_neg_le (m : ℝ) (hm : 0 ≤ m) (x y : E) :
    (1 + ‖y‖ ^ 2) ^ (-(m / 2)) ≤ 2 ^ (m / 2) * (1 + ‖x - y‖ ^ 2) ^ (m / 2) *
      (1 + ‖x‖ ^ 2) ^ (-(m / 2)) := by
  have hA : 0 < (1 + ‖x‖ ^ 2) ^ (m / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hB : 0 < (1 + ‖y‖ ^ 2) ^ (m / 2) := Real.rpow_pos_of_pos (by positivity) _
  have h := one_add_sq_rpow_le m hm x y
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ hA, inv_mul_le_iff₀ hB]
  exact h.trans_eq (mul_comm _ _)

/-- **Peetre's inequality** for a real exponent `s`:
`(1 + ‖x‖²)^{s/2} ≤ 2^{|s|/2} (1 + ‖x - y‖²)^{|s|/2} (1 + ‖y‖²)^{s/2}`. -/
theorem peetre (s : ℝ) (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ 2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2) *
      (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    exact one_add_sq_rpow_le s hs x y
  · rw [abs_of_nonpos hs]
    have h := one_add_sq_rpow_neg_le (-s) (by linarith) y x
    have hs2 : -(-s / 2) = s / 2 := by ring
    rw [hs2, norm_sub_rev] at h
    exact h

end Peetre

/-! ### Weighted Young -/

/-- The Japanese bracket weight `⟨x⟩^m = (1 + ‖x‖²)^{m/2}`. -/
def japanese {G : Type*} [Norm G] (m : ℝ) (x : G) : ℝ := (1 + ‖x‖ ^ 2) ^ (m / 2)

theorem japanese_nonneg {G : Type*} [Norm G] (m : ℝ) (x : G) : 0 ≤ japanese m x :=
  Real.rpow_nonneg (by positivity) _

section WeightedYoung

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F]

omit [OpensMeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] in
/-- Pointwise weighted majorant (Peetre inside the convolution integral):
`⟨x⟩^m (|K| ⋆ |g|)(x) ≤ 2^{m/2} (|⟨·⟩^m K| ⋆ |⟨·⟩^m g|)(x)` for `m ≥ 0`. -/
theorem japanese_mul_convAbs_le (μ : Measure G) (m : ℝ) (hm : 0 ≤ m) (K : G → E) (g : G → F)
    (x : G) :
    ENNReal.ofReal (japanese m x) * convAbs μ K g x ≤
      ENNReal.ofReal (2 ^ (m / 2)) *
        convAbs μ (fun z => japanese m z • K z) (fun y => japanese m y • g y) x := by
  rw [convAbs, convAbs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [enorm_smul, enorm_smul, Real.enorm_eq_ofReal (japanese_nonneg _ _),
    Real.enorm_eq_ofReal (japanese_nonneg _ _)]
  have hP : japanese m x ≤ 2 ^ (m / 2) * japanese m (x - y) * japanese m y :=
    one_add_sq_rpow_le m hm x y
  calc ENNReal.ofReal (japanese m x) * (‖K (x - y)‖ₑ * ‖g y‖ₑ)
      ≤ ENNReal.ofReal (2 ^ (m / 2) * japanese m (x - y) * japanese m y) *
          (‖K (x - y)‖ₑ * ‖g y‖ₑ) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (japanese_nonneg _ _)),
          ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Weighted Young inequality** (INF22 A2): for `m ≥ 0` and `1 ≤ s, p, r` with
`1/s + 1/p = 1 + 1/r`,
`‖⟨·⟩^m (|K| ⋆ |g|)‖_r ≤ 2^{m/2} ‖⟨·⟩^m K‖_s ‖⟨·⟩^m g‖_p`. -/
theorem eLpNorm_japanese_mul_convAbs_le (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (m : ℝ) (hm : 0 ≤ m) {K : G → E} {g : G → F}
    (hK : AEStronglyMeasurable K μ) (hg : AEStronglyMeasurable g μ)
    {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r) (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (fun x => ENNReal.ofReal (japanese m x) * convAbs μ K g x) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (2 ^ (m / 2)) *
        (eLpNorm (fun z => japanese m z • K z) (ENNReal.ofReal s) μ *
          eLpNorm (fun y => japanese m y • g y) (ENNReal.ofReal p) μ) := by
  have hw : Continuous (japanese m : G → ℝ) := by
    unfold japanese
    exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun _ => Or.inr (div_nonneg hm zero_le_two)
  have hK' : AEStronglyMeasurable (fun z => japanese m z • K z) μ :=
    hw.aestronglyMeasurable.smul hK
  have hg' : AEStronglyMeasurable (fun y => japanese m y • g y) μ :=
    hw.aestronglyMeasurable.smul hg
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (μ := μ)
    (c := (2 ^ (m / 2) : ℝ).toNNReal)
    (f := fun x => ENNReal.ofReal (japanese m x) * convAbs μ K g x)
    (g := convAbs μ (fun z => japanese m z • K z) (fun y => japanese m y • g y))
    (Eventually.of_forall fun x => by
      rw [enorm_eq_self, enorm_eq_self]
      exact japanese_mul_convAbs_le μ m hm K g x) (ENNReal.ofReal r)
  refine h.trans ?_
  rw [ENNReal.smul_def, smul_eq_mul]
  exact mul_le_mul' le_rfl (eLpNorm_convAbs_le_young μ hK' hg' hs hp hr hspr)

end WeightedYoung

end UnforcedLeray.Conv
