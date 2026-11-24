import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!


Helper for T03/T04 (used in SP 2247-2253 of `the November 2 reference manuscript`).

Target: `minkowski_lintegral_rpow`, for `1 ≤ p`, measurable `uncurry f`, and s-finite `μ, ν`:
`(∫⁻ a, (∫⁻ b, f a b ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ b, (∫⁻ a, f a b ^ p ∂μ) ^ (1 / p) ∂ν`.

Proof strategy (duality-free):
* `minkowski_core_le`: the truncated Hölder estimate, for measurable `H ≤ ∫⁻ F(·, y) dν`
  with `∫⁻ H^p < ∞`.
* `minkowski_finite_measure`: the case of a finite first measure, with truncation `min G n`.
* `minkowski_lintegral_rpow`: `p = 1` is Tonelli. For `p > 1` an s-finite `μ` is approximated
  from below by the finite partial sums `∑ k < N, sfiniteSeq μ k`, which increase to `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Core estimate: for a measurable `H ≤ ∫⁻ F(·, y) dν(y)` with `∫⁻ H^p < ∞` and `1 < p`,
`(∫⁻ H^p)^{1/p} ≤ ∫⁻ y, (∫⁻ F(·, y)^p)^{1/p} dν(y)`. -/
theorem minkowski_core_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [SFinite μ] [SFinite ν]
    {F : α → β → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) {p : ℝ} (hp : 1 < p)
    {H : α → ℝ≥0∞} (hH : Measurable H) (hHG : ∀ x, H x ≤ ∫⁻ y, F x y ∂ν)
    (hfin : ∫⁻ x, H x ^ p ∂μ ≠ ∞) :
    (∫⁻ x, H x ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set q : ℝ := Real.conjExponent p with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hqp : q.HolderConjugate p := hpq.symm
  set A : ℝ≥0∞ := ∫⁻ x, H x ^ p ∂μ with hA
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν with hR
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have h1q : 0 ≤ 1 / q := one_div_nonneg.mpr hqp.pos.le
  have h1p : 0 ≤ 1 / p := one_div_nonneg.mpr hp0.le
  have hFy : ∀ y, Measurable fun x => F x y := fun y => hF.of_uncurry_right
  have hFx : ∀ x, Measurable fun y => F x y := fun x => hF.of_uncurry_left
  have hpq_mul : (p - 1) * q = p := by
    rw [hq_def, Real.conjExponent]
    have : p - 1 ≠ 0 := by linarith
    field_simp
  have key : A ≤ A ^ (1 / q) * R := by
    calc A = ∫⁻ x, H x ^ (p - 1) * H x ∂μ := by
          refine lintegral_congr fun x => ?_
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ hp1 zero_le_one, ENNReal.rpow_one]
      _ ≤ ∫⁻ x, H x ^ (p - 1) * ∫⁻ y, F x y ∂ν ∂μ :=
          lintegral_mono fun x => mul_le_mul_right (hHG x) _
      _ = ∫⁻ x, ∫⁻ y, H x ^ (p - 1) * F x y ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul _ (hFx x)]
      _ = ∫⁻ y, ∫⁻ x, H x ^ (p - 1) * F x y ∂μ ∂ν := by
          apply lintegral_lintegral_swap
          exact (((hH.pow_const _).comp measurable_fst).mul hF).aemeasurable
      _ ≤ ∫⁻ y, A ^ (1 / q) * (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
          refine lintegral_mono fun y => ?_
          have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hqp
            (hH.pow_const (p - 1)).aemeasurable (hFy y).aemeasurable
          simp only [Pi.mul_apply] at h
          refine h.trans_eq ?_
          congr 2
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_mul, hpq_mul]
      _ = A ^ (1 / q) * R := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg h1q hfin)]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hsum : 1 / q + 1 / p = 1 := by
    rw [one_div, one_div]
    exact hqp.inv_add_inv_eq_one
  have hsplit : A ^ (1 / q) * A ^ (1 / p) = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ h1q h1p, hsum, ENNReal.rpow_one]
  have hq0 : A ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hfin).ne'
  have hqt : A ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg h1q hfin
  rw [← ENNReal.mul_le_mul_iff_right hq0 hqt, hsplit]
  exact key

/-- Minkowski's integral inequality for lower integrals, finite first measure. -/
theorem minkowski_finite_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {F : α → β → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, (∫⁻ y, F x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set G : α → ℝ≥0∞ := fun x => ∫⁻ y, F x y ∂ν with hG_def
  have hG : Measurable G := hF.lintegral_prod_right'
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν with hR
  have hp0 : 0 < p := by linarith
  let H : ℕ → α → ℝ≥0∞ := fun n x => min (G x) (n : ℝ≥0∞)
  have hHm : ∀ n, Measurable (H n) := fun n => hG.min measurable_const
  have hHG : ∀ n x, H n x ≤ G x := fun n x => min_le_left _ _
  have hfin : ∀ n, ∫⁻ x, H n x ^ p ∂μ ≠ ∞ := by
    intro n
    have hb : (∫⁻ _x, (n : ℝ≥0∞) ^ p ∂μ) ≠ ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top n))
        (measure_ne_top μ _)
    exact ne_top_of_le_ne_top hb
      (lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le)
  have hbound : ∀ n, ∫⁻ x, H n x ^ p ∂μ ≤ R ^ p := fun n => by
    have h := minkowski_core_le hF hp (hHm n) (hHG n) (hfin n)
    have := ENNReal.rpow_le_rpow h hp0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at this
  have hmono : Monotone H := by
    intro m n hmn x
    exact min_le_min_left _ (Nat.cast_le.2 hmn)
  have hsup : ∀ x, ⨆ n, H n x = G x := by
    intro x
    refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
    have hG_eq : G x = ⨆ n : ℕ, G x ⊓ (n : ℝ≥0∞) := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [hG_eq]
  have hGp : ∀ x, G x ^ p = ⨆ n, H n x ^ p := by
    intro x
    rw [← hsup x]
    exact Monotone.map_iSup_of_continuousAt (f := fun t : ℝ≥0∞ => t ^ p)
      ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hp0.le)
      (ENNReal.zero_rpow_of_pos hp0)
  have hint : ∫⁻ x, G x ^ p ∂μ ≤ R ^ p := by
    rw [lintegral_congr hGp, lintegral_iSup (fun n => (hHm n).pow_const p)
      (fun m n hmn x => ENNReal.rpow_le_rpow (hmono hmn x) hp0.le)]
    exact iSup_le hbound
  calc (∫⁻ x, G x ^ p ∂μ) ^ (1 / p) ≤ (R ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (one_div_nonneg.mpr hp0.le)
    _ = R := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **Minkowski's integral inequality for lower integrals** (`minkowski_lintegral_rpow`,
T02 of Part II-b). For `1 ≤ p` and s-finite `μ, ν`:
`(∫⁻ a, (∫⁻ b, f a b ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ b, (∫⁻ a, f a b ^ p ∂μ) ^ (1 / p) ∂ν`. -/
theorem minkowski_lintegral_rpow {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p)
    {f : α → β → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    (∫⁻ a, (∫⁻ b, f a b ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ b, (∫⁻ a, f a b ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp only [ENNReal.rpow_one, div_one]
    exact (lintegral_lintegral_swap hf.aemeasurable).le
  have hp0 : 0 < p := by linarith
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν with hR
  -- `∫⁻ g ∂μ` is the supremum over the finite partial sums of `sfiniteSeq μ`.
  have hsum : ∀ g : α → ℝ≥0∞, ∫⁻ a, g a ∂μ =
      ⨆ N : ℕ, ∫⁻ a, g a ∂(∑ k ∈ Finset.range N, sfiniteSeq μ k) := by
    intro g
    conv_lhs => rw [← sum_sfiniteSeq μ]
    rw [lintegral_sum_measure, ENNReal.tsum_eq_iSup_nat]
    refine iSup_congr fun N => ?_
    rw [lintegral_finsetSum_measure]
  have hle : ∀ (N : ℕ) (g : α → ℝ≥0∞),
      ∫⁻ a, g a ∂(∑ k ∈ Finset.range N, sfiniteSeq μ k) ≤ ∫⁻ a, g a ∂μ := by
    intro N g
    rw [hsum g]
    exact le_iSup (fun N => ∫⁻ a, g a ∂(∑ k ∈ Finset.range N, sfiniteSeq μ k)) N
  have hstep : ∀ N : ℕ,
      (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂(∑ k ∈ Finset.range N, sfiniteSeq μ k)) ^ (1 / p)
        ≤ R := by
    intro N
    refine (minkowski_finite_measure (μ := ∑ k ∈ Finset.range N, sfiniteSeq μ k)
      (ν := ν) hf hp1).trans ?_
    refine lintegral_mono fun y => ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hp0.le)
    exact hle N (fun x => f x y ^ p)
  have hbound : ∀ N : ℕ,
      ∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂(∑ k ∈ Finset.range N, sfiniteSeq μ k) ≤ R ^ p := by
    intro N
    have h := ENNReal.rpow_le_rpow (hstep N) hp0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at h
  have hL : ∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ ≤ R ^ p :=
    le_trans (le_of_eq (hsum (fun x => (∫⁻ y, f x y ∂ν) ^ p))) (iSup_le hbound)
  calc (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ (R ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hL (one_div_nonneg.mpr hp0.le)
    _ = R := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end UnforcedLeray.Short.IIb
