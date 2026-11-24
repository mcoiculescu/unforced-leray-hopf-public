import UnforcedLeray.Analysis.SobolevEmbedding.H1
import UnforcedLeray.Analysis.EnergyInterpolation.Stress
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Hypothesis H-H2Prod, helper: `H¹(ℝ³) ⊂ L⁴` and the `L⁴ × L⁴ → L²` column product

Support for `Loc/Hyp/H2ProductBound.lean` (the `H²` product bound, `paper/main.tex` line 504;
blueprint units B1021 and B0721, infrastructure INF11). The middle term
`(∂ₖg)_j ∂ₗf` of `∂ₗ∂ₖ(g_j f)` is a product of two `H¹` fields, bounded in `L²` by
`‖∂ₖg‖_{L⁴}‖∂ₗf‖_{L⁴}` and the inclusion `H¹ ⊂ L⁴`.

The interpolation `‖f‖₄⁴ ≤ ‖f‖₂‖f‖₆³` and the `H¹ ⊂ L⁴` bound are copied, with the namespace
changed, from the uncompiled draft


(`norm_h1ProductRow_le_l4`). The `L⁶` input is the compiled library theorem
`SobolevEmbedding.h1_l6Norm_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UnforcedLeray.Blueprint.L10.H2Prod

open SobolevGraph SobolevEmbedding

/-- `‖f‖₄⁴ ≤ ‖f‖₂ ‖f‖₆³` (Hölder on `|f|² · |f|⁶`), copied from
`Analysis/SobolevEmbedding/L4.lean`. -/
theorem eLpNorm_four_pow_le {f : SpatialField}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 4 volume ^ 4 ≤ eLpNorm f 2 volume * eLpNorm f 6 volume ^ 3 := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (f := fun x : Space => ‖f x‖ₑ ^ (2 : ℝ))
    (g := fun x : Space => ‖f x‖ₑ ^ (6 : ℝ))
    (hf.enorm.pow_const _) (hf.enorm.pow_const _)
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have he (x : Space) :
      (‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (‖f x‖ₑ ^ (6 : ℝ)) ^ (1 / 2 : ℝ) = ‖f x‖ₑ ^ (4 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hn (n : ℝ≥0) (hn : n ≠ 0) :
      (∫⁻ x : Space, ‖f x‖ₑ ^ (n : ℝ)) = eLpNorm f (n : ℝ≥0∞) volume ^ (n : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := n) hn).symm
  have hn' (n : ℝ≥0) (hn0 : n ≠ 0) (r : ℝ) (q : ℝ≥0∞) (hr : (n : ℝ) = r)
      (hq : (n : ℝ≥0∞) = q) :
      (∫⁻ x : Space, ‖f x‖ₑ ^ r) = eLpNorm f q volume ^ r := by
    subst hr
    subst hq
    exact hn n hn0
  simp only [he] at h
  rw [hn' 2 (by norm_num) 2 2 (by norm_num) (by norm_num),
    hn' 6 (by norm_num) 6 6 (by norm_num) (by norm_num),
    hn' 4 (by norm_num) 4 4 (by norm_num) (by norm_num)] at h
  have e1 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have e2 : (6 : ℝ) * (1 / 2) = ((3 : ℕ) : ℝ) := by norm_num
  have e3 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e1, e2, ENNReal.rpow_one, ENNReal.rpow_natCast,
    e3, ENNReal.rpow_natCast] at h
  exact h

/-- `L² ∩ L⁶ ⊂ L⁴`. -/
theorem memLp_four_of_two_six {f : SpatialField}
    (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume) : MemLp f 4 volume := by
  refine ⟨h2.aestronglyMeasurable, ?_⟩
  have hb : eLpNorm f 4 volume ^ 4 < ⊤ :=
    (eLpNorm_four_pow_le h2.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top h2.2 (ENNReal.pow_lt_top (n := 3) h6.2))
  by_contra hn
  have he : eLpNorm f 4 volume = ⊤ := top_unique (not_lt.mp hn)
  simp [he] at hb

/-- `H¹ ⊂ L⁴`. -/
theorem h1_memLp_four (F : SobolevGraph.H1) :
    MemLp (F.value : SpatialField) 4 volume :=
  memLp_four_of_two_six (Lp.memLp F.value) (h1_memLp_six F)

/-- The finite-norm interpolation bound. -/
theorem norm_four_pow_le {f : SpatialField}
    (h2 : MemLp f 2 volume) (h6 : MemLp f 6 volume) :
    (eLpNorm f 4 volume).toReal ^ 4 ≤
      (eLpNorm f 2 volume).toReal * (eLpNorm f 6 volume).toReal ^ 3 := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top h2.2.ne (ENNReal.pow_ne_top h6.2.ne))
    (eLpNorm_four_pow_le h2.aestronglyMeasurable)
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul] using h

/-- The constant of `‖F‖_{L⁴} ≤ l4Const ‖F‖_{H¹}`. -/
def l4Const : ℝ := 1 + 3 * (sobolevConstant : ℝ)

theorem l4Const_pos : 0 < l4Const := by
  unfold l4Const
  positivity

/-- `‖F‖_{L⁴} ≤ l4Const ‖F‖_{H¹}`. -/
theorem h1_l4Norm_le (F : SobolevGraph.H1) :
    (eLpNorm (F.value : SpatialField) 4 volume).toReal ≤ l4Const * ‖F‖ := by
  have hv : ‖F.value‖ ≤ ‖F‖ := PiLp.norm_apply_le (F : SobolevGraph.H1Ambient) 0
  have h1 : 1 ≤ l4Const := by
    unfold l4Const; have := NNReal.coe_nonneg sobolevConstant; linarith
  have hv' : ‖F.value‖ ≤ l4Const * ‖F‖ := by
    apply hv.trans
    nlinarith [norm_nonneg F]
  have h6 : (eLpNorm (F.value : SpatialField) 6 volume).toReal ≤ l4Const * ‖F‖ := by
    apply (h1_l6Norm_le F).trans
    unfold l4Const
    nlinarith [norm_nonneg F]
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
    (mul_nonneg l4Const_pos.le (norm_nonneg F))
  calc
    _ ≤ ‖F.value‖ * (eLpNorm (F.value : SpatialField) 6 volume).toReal ^ 3 := by
      simpa only [Lp.norm_def] using norm_four_pow_le (Lp.memLp F.value) (h1_memLp_six F)
    _ ≤ (l4Const * ‖F‖) * (l4Const * ‖F‖) ^ 3 := by
      gcongr
    _ = (l4Const * ‖F‖) ^ 4 := by ring

theorem holder_four_four : ENNReal.HolderTriple 4 4 2 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff]

/-- The column product `U_j V` of two `H¹` fields is in `L²`. -/
theorem h1_coord_smul_memLp (U V : H1) (j : Fin 3) :
    MemLp (fun x : Space => (U.value : SpatialField) x j • (V.value : SpatialField) x)
      2 volume := by
  have : ENNReal.HolderTriple 4 4 2 := holder_four_four
  exact (h1_memLp_four V).smul
    (EnergyInterpolation.coordinate_memLp (h1_memLp_four U) j)

/-- `‖U_j V‖_{L²} ≤ l4Const² ‖U‖_{H¹} ‖V‖_{H¹}` (Hölder `L⁴ × L⁴ → L²` and `H¹ ⊂ L⁴`). -/
theorem h1_coord_smul_l2Norm_le (U V : H1) (j : Fin 3) :
    l2Norm (fun x : Space => (U.value : SpatialField) x j • (V.value : SpatialField) x) ≤
      l4Const ^ 2 * ‖U‖ * ‖V‖ := by
  have : ENNReal.HolderTriple 4 4 2 := holder_four_four
  have h := eLpNorm_smul_le_mul_eLpNorm (h1_memLp_four V).aestronglyMeasurable
    (EnergyInterpolation.coordinate_memLp (h1_memLp_four U) j).aestronglyMeasurable
    (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
  have he : eLpNorm (fun x : Space => (U.value : SpatialField) x j •
      (V.value : SpatialField) x) 2 volume ≤
      eLpNorm (U.value : SpatialField) 4 volume *
        eLpNorm (V.value : SpatialField) 4 volume :=
    h.trans (mul_le_mul'
      (EnergyInterpolation.eLpNorm_coordinate_le (U.value : SpatialField) 4 j) le_rfl)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (h1_memLp_four U).2.ne (h1_memLp_four V).2.ne) he
  rw [ENNReal.toReal_mul] at hr
  calc l2Norm (fun x : Space => (U.value : SpatialField) x j • (V.value : SpatialField) x)
      ≤ (eLpNorm (U.value : SpatialField) 4 volume).toReal *
          (eLpNorm (V.value : SpatialField) 4 volume).toReal := hr
    _ ≤ (l4Const * ‖U‖) * (l4Const * ‖V‖) :=
        mul_le_mul (h1_l4Norm_le U) (h1_l4Norm_le V) ENNReal.toReal_nonneg
          (mul_nonneg l4Const_pos.le (norm_nonneg U))
    _ = l4Const ^ 2 * ‖U‖ * ‖V‖ := by ring

end UnforcedLeray.Blueprint.L10.H2Prod
