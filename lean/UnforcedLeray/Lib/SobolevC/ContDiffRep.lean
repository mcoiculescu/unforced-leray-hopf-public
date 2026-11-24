import UnforcedLeray.Lib.SobolevC.C0Rep
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# `C^k` representatives (INF11 target S10)


S10 `W.exists_contDiff_rep`.  Manuscript uses: B0091 (tex 1463–1477, "`H^{m+2}(ℝ²) ⊂ C^m_b`",
every derivative bounded), B0153 (tex 2263–2346, `H^{j+2} ⊂ C^j`), B0160 (tex 2413–2425),
B0711 (tex 279–290).

## Proof
For `x ∈ W^{m,2}(ℝⁿ)` and `j` with `n < 2(m - j)`:
`|ξ|^j |𝓕x(ξ)| ≤ ⟨ξ⟩^{j-m} · ⟨ξ⟩^m |𝓕x(ξ)|`, so `|ξ|^j 𝓕x ∈ L¹` with norm
`≤ ‖⟨ξ⟩^{j-m}‖₂ 2^{m/2} ‖x‖` (Cauchy–Schwarz and `W.bessel_sq_le`).  Differentiation under the
integral (Mathlib `VectorFourier.contDiff_fourierIntegral`,
`VectorFourier.iteratedFDeriv_fourierIntegral`) makes `g = 𝓕⁻¹(𝓕x)` a `C^k` function with
`‖D^j g‖_∞ ≤ (2π)^j ‖ |ξ|^j 𝓕x ‖₁`, and `g` represents `x` (`W.toVol_ae_eq_fourierInv`).

## Main declarations
* `W.exists_contDiff_rep_of_lt` (`n + 2k < 2m`), `W.exists_contDiff_rep` (`n ≤ 3`, `m = k + 2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric SchwartzMap TemperedDistribution
open scoped ENNReal NNReal Topology ContDiff FourierTransform SchwartzMap Real

namespace UnforcedLeray.Sob

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F] {m : ℕ}

/-- The weight `⟨ξ⟩^{-s} = (1 + |ξ|²)^{-s/2}` with a real exponent. -/
def bracketR (s : ℝ) (ξ : Eucl n) : ℂ := (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

theorem continuous_bracketR (s : ℝ) : Continuous (bracketR (n := n) s) :=
  Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun y => Or.inl (by positivity : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0))

theorem memLp_bracketR {s : ℝ} (hs : (n : ℝ) < 2 * s) : MemLp (bracketR (n := n) s) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_bracketR s).aestronglyMeasurable).mpr ?_
  have hr : ((Module.finrank ℝ (Eucl n) : ℕ) : ℝ) < 2 * s := by
    rw [finrank_euclideanSpace_fin]; exact hs
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Eucl n))) hr
  refine hint.congr (Eventually.of_forall fun ξ => ?_)
  simp only [bracketR, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- `|ξ|^j |𝓕x(ξ)| ≤ |⟨ξ⟩^{j-m} · ⟨ξ⟩^m 𝓕x(ξ)|`. -/
theorem pow_mul_norm_fourierValue_le (x : W (wholeSpace n) 1 ℂ F m 2) (j : ℕ) (ξ : Eucl n) :
    ‖ξ‖ ^ j * ‖(W.fourierValue x : Eucl n → F) ξ‖ ≤
      ‖bracketR ((m : ℝ) - j) ξ • W.besselFn x ξ‖ := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hid : bracketR ((m : ℝ) - j) ξ • W.besselFn x ξ =
      (((1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) : ℝ) : ℂ) • (W.fourierValue x : Eucl n → F) ξ := by
    rw [W.besselFn, bracketR, smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
    congr 3
    ring
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖ξ‖ ^ j = (‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _)]
        congr 1; push_cast; ring
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

theorem integrable_pow_mul_fourierValue (x : W (wholeSpace n) 1 ℂ F m 2) {j : ℕ}
    (hj : (n : ℝ) < 2 * ((m : ℝ) - j)) :
    Integrable (fun ξ => ‖ξ‖ ^ j * ‖(W.fourierValue x : Eucl n → F) ξ‖) volume := by
  have h := (W.memLp_besselFn x).smul (r := 1) (memLp_bracketR (n := n) hj)
  refine (memLp_one_iff_integrable.mp h).norm.mono'
    ((continuous_norm.pow j).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _).norm)
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_norm_fourierValue_le x j ξ

theorem integral_pow_mul_fourierValue_le (x : W (wholeSpace n) 1 ℂ F m 2) {j : ℕ}
    (hj : (n : ℝ) < 2 * ((m : ℝ) - j)) :
    ∫ ξ, ‖ξ‖ ^ j * ‖(W.fourierValue x : Eucl n → F) ξ‖ ≤
      (eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume).toReal * Real.sqrt (2 ^ m) * ‖x‖ := by
  have hsm := (W.memLp_besselFn x).smul (r := 1) (memLp_bracketR (n := n) hj)
  have hwne := (memLp_bracketR (n := n) hj).2.ne
  have hBne := (W.memLp_besselFn x).2.ne
  calc ∫ ξ, ‖ξ‖ ^ j * ‖(W.fourierValue x : Eucl n → F) ξ‖
      ≤ ∫ ξ, ‖(bracketR ((m : ℝ) - j) • W.besselFn x) ξ‖ :=
        integral_mono (integrable_pow_mul_fourierValue x hj)
          (memLp_one_iff_integrable.mp hsm).norm fun ξ => pow_mul_norm_fourierValue_le x j ξ
    _ = (eLpNorm (bracketR (n := n) ((m : ℝ) - j) • W.besselFn x) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hsm.1]
    _ ≤ (eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume *
          eLpNorm (W.besselFn x) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hwne hBne)
          (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (W.memLp_besselFn x).1
            (continuous_bracketR _).aestronglyMeasurable)
    _ = (eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume).toReal *
          (eLpNorm (W.besselFn x) 2 volume).toReal := ENNReal.toReal_mul
    _ ≤ (eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume).toReal *
          (Real.sqrt (2 ^ m) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (toReal_eLpNorm_besselFn_le x) ENNReal.toReal_nonneg
    _ = _ := by ring

theorem innerSL_neg_toLinearMap₁₂ :
    (-innerSL ℝ : Eucl n →L[ℝ] Eucl n →L[ℝ] ℝ).toLinearMap₁₂ = -innerₗ (Eucl n) := by
  ext a b
  simp

/-- **`C^k` representatives** (S10; B0091 tex 1463–1477, B0153 tex 2263–2346): for
`n + 2k < 2m`, every `x ∈ W^{m,2}(ℝⁿ; F)` has a `C^k` representative `g` with
`‖D^j g‖_∞ ≤ C ‖x‖_{H^m}` for `j ≤ k`, `C` depending only on `n, m, k`. -/
theorem W.exists_contDiff_rep_of_lt {k : ℕ} (hn : n + 2 * k < 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : W (wholeSpace n) 1 ℂ F m 2,
      ∃ g : Eucl n → F, ContDiff ℝ k g ∧
        (W.value (wholeSpace n) 1 ℂ F m 2 x : Eucl n → F) =ᵐ[volume] g ∧
        ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ C * ‖x‖ := by
  have hj : ∀ j ≤ k, (n : ℝ) < 2 * ((m : ℝ) - j) := by
    intro j hjk
    have : n + 2 * j < 2 * m := by omega
    have h' : ((n + 2 * j : ℕ) : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  set c : ℕ → ℝ := fun j =>
    (2 * π) ^ j * ((eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume).toReal *
      Real.sqrt (2 ^ m)) with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  refine ⟨∑ j ∈ Finset.range (k + 1), c j, Finset.sum_nonneg fun j _ => hc0 j, fun x => ?_⟩
  set F₀ : Eucl n → F := (W.fourierValue x : Eucl n → F) with hF₀
  set L : Eucl n →L[ℝ] Eucl n →L[ℝ] ℝ := -innerSL ℝ with hL
  have hint : ∀ j : ℕ, (j : ℕ∞) ≤ (k : ℕ∞) →
      Integrable (fun ξ => ‖ξ‖ ^ j * ‖F₀ ξ‖) volume := fun j hjk =>
    integrable_pow_mul_fourierValue x (hj j (by exact_mod_cast hjk))
  have hF₀int : Integrable F₀ volume := integrable_fourierValue (by omega) x
  have hg_eq : (𝓕⁻ F₀ : Eucl n → F) =
      VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ F₀ := by
    rw [hL, innerSL_neg_toLinearMap₁₂]
    rfl
  have hL1 : ‖L‖ ≤ 1 := by rw [hL, ContinuousLinearMap.opNorm_neg]; exact norm_innerSL_le ℝ
  refine ⟨𝓕⁻ F₀, ?_, (coeFn_toVol _).symm.trans (W.toVol_ae_eq_fourierInv x hF₀int), ?_⟩
  · have hcd := VectorFourier.contDiff_fourierIntegral L (μ := volume) (N := (k : ℕ∞)) hint
    rw [hg_eq]
    exact_mod_cast hcd
  · intro j hjk y
    have hjN : ((j : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hjk
    rw [hg_eq, VectorFourier.iteratedFDeriv_fourierIntegral L hint hF₀int.1 hjN]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    have hle : ∫ v, ‖VectorFourier.fourierPowSMulRight L F₀ v j‖ ≤
        (2 * π) ^ j * ∫ v, ‖v‖ ^ j * ‖F₀ v‖ := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
        ((hint j hjN).const_mul _) (Eventually.of_forall fun v => ?_)
      refine (VectorFourier.norm_fourierPowSMulRight_le L F₀ v j).trans ?_
      have h2 : (2 * π * ‖L‖) ^ j ≤ (2 * π) ^ j :=
        pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (by positivity) hL1) j
      calc (2 * π * ‖L‖) ^ j * ‖v‖ ^ j * ‖F₀ v‖ = (2 * π * ‖L‖) ^ j * (‖v‖ ^ j * ‖F₀ v‖) := by
            ring
        _ ≤ (2 * π) ^ j * (‖v‖ ^ j * ‖F₀ v‖) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
    have hI := integral_pow_mul_fourierValue_le x (hj j hjk)
    have hcj : c j * ‖x‖ ≤ (∑ i ∈ Finset.range (k + 1), c i) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hc0 i)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))) (norm_nonneg _)
    refine le_trans hle (le_trans ?_ hcj)
    calc (2 * π) ^ j * ∫ v, ‖v‖ ^ j * ‖F₀ v‖
        ≤ (2 * π) ^ j * ((eLpNorm (bracketR (n := n) ((m : ℝ) - j)) 2 volume).toReal *
            Real.sqrt (2 ^ m) * ‖x‖) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = c j * ‖x‖ := by simp only [hc]; ring

/-- **`H^{k+2}(ℝⁿ) ⊂ C^k_b` for `n ≤ 3`** (S10; B0091, B0153, B0160, B0711). -/
theorem W.exists_contDiff_rep {k : ℕ} (hn : n ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : W (wholeSpace n) 1 ℂ F (k + 2) 2,
      ∃ g : Eucl n → F, ContDiff ℝ k g ∧
        (W.value (wholeSpace n) 1 ℂ F (k + 2) 2 x : Eucl n → F) =ᵐ[volume] g ∧
        ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ C * ‖x‖ :=
  W.exists_contDiff_rep_of_lt (by omega)

end UnforcedLeray.Sob
