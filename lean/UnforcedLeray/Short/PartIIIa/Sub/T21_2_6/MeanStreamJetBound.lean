import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Part III-a, `PartIII-a:T21/2/6/18`: weighted pointwise bounds of the mean stream derivatives

Source of record: `the November 2 reference manuscript` (SP), lines 447-459
(`sct:expansion`, last display, with `ℓ = 0`, `p = ∞`) and lines 397-404 (`sct:mean`).
Target: `meanStreamJetBound_of`, proving `MeanStreamJetBound` from `TrainMeanExpansion` and
`TrainMeanEquations`.

Route.
* For `m ≤ 2k`, the `s`-slice of the mean stream is `C^∞` for `s > 0` (`TrainMeanEquations`), so
  `η ↦ η^m ∂_η^b S(s, η)` is continuous; its essential supremum is bounded by the last conjunct of
  `TrainMeanExpansion` (`ℓ = 0`, `p = ∞`), hence pointwise bounded (`mjb_abs_le`). The polynomial
  `polyP C M ν (trainPeriod 2 ν) = C (1 + ν⁻² + ν⁻¹)^M` is bounded by `C 3^M ν⁻^(2M)` for `ν ≤ 1`,
  and `(1+s)^((m-b-1)/2) ≤ (1+s)^k` for `m ≤ 2k`.
* The weight `(1+η²)^k ≤ 2^k (1 + η^{2k})` splits the bound into the cases `m = 0` and `m = 2k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The mean stream slice `η ↦ S(s, η)` is `C^∞` for `s > 0` (from `TrainMeanEquations`). -/
theorem mjb_slice_contDiff (hmeq : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) (s : ℝ) (hs : 0 < s) :
    ContDiff ℝ ∞ (fun η => UnforcedLeray.Short.PartI.meanStream tr s η) :=
  (hmeq ν c hν hc tr hbuc).1.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun η => ⟨hs, mem_univ η⟩)

/-- A continuous function is bounded pointwise by its `L^∞` norm. -/
theorem mjb_abs_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : 0 ≤ K)
    (h : eLpNorm f ⊤ volume ≤ ENNReal.ofReal K) (x : ℝ) : |f x| ≤ K := by
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_exponent_top] at h
    exact (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun y hy => hy.trans h
  have hd : Dense {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} := Measure.dense_of_ae hae
  have hc : IsClosed {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} :=
    isClosed_le (continuous_enorm.comp hf) continuous_const
  have hx : x ∈ {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} := by
    rw [← hc.closure_eq, hd.closure_eq]; trivial
  have hx' : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal K := by
    rw [ofReal_norm]; exact hx
  rw [ENNReal.ofReal_le_ofReal_iff hK, Real.norm_eq_abs] at hx'
  exact hx'

/-- `(1 + η²)^k ≤ 2^k (1 + η^{2k})`. -/
theorem mjb_pow_le (k : ℕ) (η : ℝ) : (1 + η ^ 2) ^ k ≤ 2 ^ k * (1 + η ^ (2 * k)) := by
  rw [pow_mul]
  set x := η ^ 2 with hxdef
  have hx0 : 0 ≤ x := sq_nonneg η
  have hmax : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hstep2 : (1 + x) ^ k ≤ 2 ^ k * (max 1 x) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hmax k
  have hstep3 : (max 1 x) ^ k ≤ 1 + x ^ k := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx0 k]
  calc (1 + x) ^ k ≤ 2 ^ k * (max 1 x) ^ k := hstep2
    _ ≤ 2 ^ k * (1 + x ^ k) := mul_le_mul_of_nonneg_left hstep3 (by positivity)

/-- Lemma A: for `m ≤ 2k` the weighted pointwise bound of `η^m ∂_η^b S(s, η)`, `s > 0`,
with a polynomial in `ν⁻¹` and the power `(1+s)^k`, uniformly for `0 < ν ≤ ν₀ ≤ 1`. -/
theorem mjb_lemmaA (hme : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hmeq : UnforcedLeray.Short.PartI.TrainMeanEquations) (b m k : ℕ) (hm : m ≤ 2 * k) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
            |η ^ m * iteratedDeriv b (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
              C * ν⁻¹ ^ M * (1 + s) ^ k := by
  obtain ⟨C, M, ν₀, hC, hν₀, H⟩ := hme 2 (by norm_num) 0 m b 0 ⊤ le_top
  have hC' : 0 ≤ C := hC.le
  refine ⟨C * 3 ^ M, 2 * M, min ν₀ 1, mul_nonneg hC' (by positivity), lt_min hν₀ one_pos,
    min_le_right _ _, ?_⟩
  intro ν hν0 hνle tr htr s hs η
  have hνM : ν ≤ ν₀ := le_trans hνle (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans hνle (min_le_right _ _)
  obtain ⟨-, -, -, H5⟩ := H ν hν0 hνM tr htr
  have H6 := H5 s hs.le
  simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, ENNReal.toReal_top, inv_zero,
    zero_div, add_zero] at H6
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hS := mjb_slice_contDiff hmeq ν (ν ^ (-2 : ℝ)) hν0 hc tr htr s hs
  have hI : Continuous (iteratedDeriv b (fun e => UnforcedLeray.Short.PartI.meanStream tr s e)) :=
    hS.continuous_iteratedDeriv b (by exact_mod_cast le_top)
  have hcont : Continuous
      (fun η : ℝ => η ^ m * iteratedDeriv b (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) :=
    (continuous_pow m).mul hI
  have hK : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2) := by
    have h1 : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
      unfold UnforcedLeray.Short.PartI.polyP UnforcedLeray.Short.PartI.trainPeriod
      exact mul_nonneg hC' (pow_nonneg (by have := Real.rpow_pos_of_pos hν0 (-2 : ℝ); positivity) _)
    exact mul_nonneg h1 (Real.rpow_nonneg (by linarith) _)
  have habs := mjb_abs_le hcont hK H6 η
  have hcu : UnforcedLeray.Short.PartI.trainPeriod 2 ν = ν⁻¹ ^ 2 := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν0.le, Real.rpow_two, inv_pow]
  have hu1 : 1 ≤ ν⁻¹ := by
    rw [one_le_inv₀ hν0]; exact hν1
  have hle : 1 + ν⁻¹ ^ 2 + ν⁻¹ ≤ 3 * ν⁻¹ ^ 2 := by
    nlinarith
  have hA1 : (1 + ν⁻¹ ^ 2 + ν⁻¹) ^ M ≤ (3 * ν⁻¹ ^ 2) ^ M :=
    pow_le_pow_left₀ (by positivity) hle M
  have he : ((m : ℝ) - b - 1) / 2 ≤ (k : ℝ) := by
    have h2m : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm
    have hb0 : (0 : ℝ) ≤ b := by positivity
    linarith
  have hpow : (1 + s) ^ (((m : ℝ) - b - 1) / 2) ≤ (1 + s) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) he
  have hK' : UnforcedLeray.Short.PartI.polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2) ≤ (C * 3 ^ M) * ν⁻¹ ^ (2 * M) * (1 + s) ^ k := by
    calc UnforcedLeray.Short.PartI.polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          (1 + s) ^ (((m : ℝ) - b - 1) / 2)
        = C * (1 + ν⁻¹ ^ 2 + ν⁻¹) ^ M * (1 + s) ^ (((m : ℝ) - b - 1) / 2) := by
          unfold UnforcedLeray.Short.PartI.polyP
          rw [hcu]
      _ ≤ C * (3 * ν⁻¹ ^ 2) ^ M * (1 + s) ^ k :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA1 hC') hpow
            (Real.rpow_nonneg (by linarith) _)
            (mul_nonneg hC' (pow_nonneg (by positivity) _))
      _ = (C * 3 ^ M) * ν⁻¹ ^ (2 * M) * (1 + s) ^ k := by
          rw [mul_pow, ← pow_mul]; ring
  exact habs.trans hK'

/-- **Weighted pointwise bounds of the mean stream derivatives** (`MeanStreamJetBound`,
SP 456-459 with `ℓ = 0`, `p = ∞`, `m ∈ {0, 2k}`). -/
theorem meanStreamJetBound_of (hme : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hmeq : UnforcedLeray.Short.PartI.TrainMeanEquations) : MeanStreamJetBound := by
  intro k b
  obtain ⟨C0, M0, ν0, hC0, hν0, hν0le, H0⟩ := mjb_lemmaA hme hmeq b 0 k (by omega)
  obtain ⟨C1, M1, ν1, hC1, hν1, hν1le, H1⟩ := mjb_lemmaA hme hmeq b (2 * k) k le_rfl
  refine ⟨2 ^ k * (C0 + C1), M0 + M1 + k, min ν0 ν1, lt_min hν0 hν1, ?_⟩
  intro ν hν tr htr s hs η
  have hνpos : 0 < ν := hν.1
  have hνle0 : ν ≤ ν0 := le_trans hν.2 (min_le_left _ _)
  have hνle1 : ν ≤ ν1 := le_trans hν.2 (min_le_right _ _)
  have hu1 : 1 ≤ ν⁻¹ := by
    rw [one_le_inv₀ hνpos]; exact le_trans hνle0 hν0le
  have hf0 := H0 ν hνpos hνle0 tr htr s hs η
  have hf1 := H1 ν hνpos hνle1 tr htr s hs η
  simp only [pow_zero, one_mul] at hf0
  set X := iteratedDeriv b (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η with hX
  have h1s : 0 < 1 + s := by linarith
  have hE : 0 ≤ η ^ (2 * k) := by rw [pow_mul]; positivity
  have hA0 : ν⁻¹ ^ M0 ≤ ν⁻¹ ^ (M0 + M1 + k) := pow_le_pow_right₀ hu1 (by omega)
  have hA1 : ν⁻¹ ^ M1 ≤ ν⁻¹ ^ (M0 + M1 + k) := pow_le_pow_right₀ hu1 (by omega)
  have hs' : (1 + s) ^ k ≤ (1 + s) ^ (M0 + M1 + k) := pow_le_pow_right₀ (by linarith) (by omega)
  have hu0 : (0 : ℝ) ≤ ν⁻¹ := by linarith
  have t0 : C0 * ν⁻¹ ^ M0 * (1 + s) ^ k ≤ C0 * ν⁻¹ ^ (M0 + M1 + k) * (1 + s) ^ (M0 + M1 + k) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA0 hC0) hs' (pow_nonneg h1s.le k)
      (mul_nonneg hC0 (pow_nonneg hu0 _))
  have t1 : C1 * ν⁻¹ ^ M1 * (1 + s) ^ k ≤ C1 * ν⁻¹ ^ (M0 + M1 + k) * (1 + s) ^ (M0 + M1 + k) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA1 hC1) hs' (pow_nonneg h1s.le k)
      (mul_nonneg hC1 (pow_nonneg hu0 _))
  calc (1 + η ^ 2) ^ k * |X|
      ≤ 2 ^ k * (1 + η ^ (2 * k)) * |X| := mul_le_mul_of_nonneg_right (mjb_pow_le k η) (abs_nonneg _)
    _ = 2 ^ k * (|X| + |η ^ (2 * k) * X|) := by rw [abs_mul, abs_of_nonneg hE]; ring
    _ ≤ 2 ^ k * (C0 * ν⁻¹ ^ M0 * (1 + s) ^ k + C1 * ν⁻¹ ^ M1 * (1 + s) ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add hf0 hf1) (by positivity)
    _ ≤ 2 ^ k * (C0 * ν⁻¹ ^ (M0 + M1 + k) * (1 + s) ^ (M0 + M1 + k)
          + C1 * ν⁻¹ ^ (M0 + M1 + k) * (1 + s) ^ (M0 + M1 + k)) :=
        mul_le_mul_of_nonneg_left (add_le_add t0 t1) (by positivity)
    _ = 2 ^ k * (C0 + C1) * ν⁻¹ ^ (M0 + M1 + k) * (1 + s) ^ (M0 + M1 + k) := by ring

end UnforcedLeray.Short.IIIa
