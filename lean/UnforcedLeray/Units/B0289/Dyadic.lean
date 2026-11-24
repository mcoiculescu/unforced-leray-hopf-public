import UnforcedLeray.Units.B0289.Periodize
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

/-!
# B0289: dyadic age windows

Unit B0289 (tex lines 4771–4775). The manuscript's summation step (tex lines 3801–3804):
"The weight `s^{r/2-5/2}` is comparable to its value at `a` on each such window. Summing the
`r`th powers over dyadic intervals, using their finite overlap, proves the global bound for
`ν s Δ b`."

* `W k = [2^k, 2^{k+1})`, the dyadic age windows, a partition of `(0,∞)` (`lintegral_Ioi_eq_tsum`);
  `E k = [2^k/2, 4·2^k)` the enlarged windows, covered by three `W`'s (`tsum_lintegral_E_le`);
* `rpow_window_le`, `rpow_source_le`: comparability of the age weight `s^{a_p}`,
  `a_p = p/2 - 5/2`, on windows (for `1 ≤ p < 3`, so `-2 ≤ a_p < 0`);
* `window_source`, `window_D2`: one window of the heat estimate, in `[0,∞]`-valued form;
* helpers: `eLpNorm_ofReal_rpow`, `ae_lt_top_of_eLpNorm`, `rpow_half_mul_le_add`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

/-! ## `[0,∞]` helpers -/

/-- `‖f‖_{L^p}^p = ∫ ‖f‖^p` for `0 < p < ∞`. -/
theorem eLpNorm_ofReal_rpow {α ε : Type*} [MeasurableSpace α] [ENorm ε] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) (f : α → ε) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- A `[0,∞]`-valued function with finite `L^p` norm (`0 < p`) is finite almost everywhere. -/
theorem ae_lt_top_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h : eLpNorm f (ENNReal.ofReal p) μ < ⊤) : ∀ᵐ x ∂μ, f x < ⊤ := by
  have h1 : ∫⁻ x, f x ^ p ∂μ ≠ ⊤ := by
    have e := eLpNorm_ofReal_rpow hp f (μ := μ)
    simp only [enorm_eq_self] at e
    rw [← e]
    exact (ENNReal.rpow_lt_top_of_nonneg hp.le h.ne).ne
  filter_upwards [ae_lt_top' (hf.pow_const p) h1] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).1 hx

/-- `(x y)^{1/2} ≤ x + y` in `[0,∞]`. -/
theorem rpow_half_mul_le_add (x y : ℝ≥0∞) : (x * y) ^ (1 / 2 : ℝ) ≤ x + y := by
  have hm : x * y ≤ max x y * max x y := mul_le_mul' (le_max_left _ _) (le_max_right _ _)
  calc (x * y) ^ (1 / 2 : ℝ) ≤ (max x y * max x y) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hm (by norm_num)
    _ = max x y := by
        rw [← sq, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ x + y := max_le le_self_add le_add_self

/-! ## Weight comparisons on windows -/

/-- On `[a, 2a)`: `s^{a_p} s^p ≤ 8 a^{a_p + p}`. -/
theorem rpow_window_le {p a s : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) (ha : 0 < a)
    (hs : s ∈ Ico a (2 * a)) :
    s ^ (p / 2 - 5 / 2) * s ^ p ≤ 8 * a ^ (p / 2 - 5 / 2 + p) := by
  have hs0 : 0 < s := ha.trans_le hs.1
  have h1 : s ^ (p / 2 - 5 / 2) ≤ a ^ (p / 2 - 5 / 2) :=
    Real.rpow_le_rpow_of_nonpos ha hs.1 (by linarith)
  have h2 : s ^ p ≤ (2 * a) ^ p := Real.rpow_le_rpow hs0.le hs.2.le (by linarith)
  have h3 : (2 * a) ^ p ≤ 8 * a ^ p := by
    rw [Real.mul_rpow (by norm_num) ha.le]
    have h4 : (2 : ℝ) ^ p ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3.le
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h8] at h4
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ha.le _)
  rw [Real.rpow_add ha]
  calc s ^ (p / 2 - 5 / 2) * s ^ p ≤ a ^ (p / 2 - 5 / 2) * (8 * a ^ p) :=
        mul_le_mul h1 (h2.trans h3) (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg ha.le _)
    _ = 8 * (a ^ (p / 2 - 5 / 2) * a ^ p) := by ring

/-- On `[a/2, 4a)`: `a^{a_p} ≤ 16 t^{a_p}`. -/
theorem rpow_source_le {p a t : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) (ha : 0 < a)
    (ht : t ∈ Ico (a / 2) (4 * a)) :
    a ^ (p / 2 - 5 / 2) ≤ 16 * t ^ (p / 2 - 5 / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le (half_pos ha) ht.1
  have h1 : (4 * a) ^ (p / 2 - 5 / 2) ≤ t ^ (p / 2 - 5 / 2) :=
    Real.rpow_le_rpow_of_nonpos ht0 ht.2.le (by linarith)
  have h2 : (4 * a) ^ (p / 2 - 5 / 2) = 4 ^ (p / 2 - 5 / 2) * a ^ (p / 2 - 5 / 2) :=
    Real.mul_rpow (by norm_num) ha.le
  have h3 : (1 / 16 : ℝ) ≤ 4 ^ (p / 2 - 5 / 2) := by
    have h5 : (4 : ℝ) ^ (-2 : ℝ) ≤ 4 ^ (p / 2 - 5 / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (4 : ℝ) ^ (-2 : ℝ) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    linarith
  have ha' : 0 ≤ a ^ (p / 2 - 5 / 2) := Real.rpow_nonneg ha.le _
  nlinarith [mul_le_mul_of_nonneg_right h3 ha']

/-! ## Dyadic windows -/

/-- The dyadic age window `[2^k, 2^{k+1})`. -/
def W (k : ℤ) : Set ℝ := Ico ((2 : ℝ) ^ k) (2 ^ (k + 1))

/-- The enlarged window `[2^k/2, 4·2^k)` carrying the cutoff source. -/
def E (k : ℤ) : Set ℝ := Ico ((2 : ℝ) ^ k / 2) (4 * 2 ^ k)

theorem measurableSet_W (k : ℤ) : MeasurableSet (W k) := measurableSet_Ico

theorem W_subset_Ioi (k : ℤ) : W k ⊆ Ioi 0 := fun _ hs =>
  lt_of_lt_of_le (zpow_pos two_pos k) hs.1

theorem W_eq (k : ℤ) : W k = Ico ((2 : ℝ) ^ k) (2 * 2 ^ k) := by
  rw [W, zpow_add_one₀ two_ne_zero, mul_comm]

theorem W_disjoint : Pairwise (Function.onFun Disjoint W) := by
  have key : ∀ k l : ℤ, k < l → Disjoint (W k) (W l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    rintro s ⟨_, h1⟩ ⟨h2, _⟩
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := zpow_le_zpow_right₀ one_le_two (by omega)
    linarith
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact key k l h
  · exact (key l k h).symm

/-- The dyadic index `⌊log₂ s⌋`. -/
def dyIdx (s : ℝ) : ℤ := ⌊Real.logb 2 s⌋

theorem measurable_dyIdx : Measurable dyIdx := by
  unfold dyIdx Real.logb
  exact (Real.measurable_log.div_const _).floor

theorem mem_W_dyIdx {s : ℝ} (hs : 0 < s) : s ∈ W (dyIdx s) := by
  have hL : (2 : ℝ) ^ (Real.logb 2 s) = s := Real.rpow_logb two_pos (by norm_num) hs
  constructor
  · calc (2 : ℝ) ^ (dyIdx s) = (2 : ℝ) ^ ((dyIdx s : ℤ) : ℝ) := (Real.rpow_intCast _ _).symm
      _ ≤ 2 ^ (Real.logb 2 s) := Real.rpow_le_rpow_of_exponent_le one_le_two (Int.floor_le _)
      _ = s := hL
  · calc s = 2 ^ (Real.logb 2 s) := hL.symm
      _ < (2 : ℝ) ^ (((dyIdx s + 1 : ℤ)) : ℝ) := by
          refine Real.rpow_lt_rpow_of_exponent_lt one_lt_two ?_
          push_cast
          exact Int.lt_floor_add_one _
      _ = (2 : ℝ) ^ (dyIdx s + 1) := Real.rpow_intCast _ _

theorem dyIdx_eq {s : ℝ} {k : ℤ} (h : s ∈ W k) : dyIdx s = k := by
  by_contra hne
  have hs : 0 < s := W_subset_Ioi k h
  exact Set.disjoint_left.1 (W_disjoint hne) (mem_W_dyIdx hs) h

theorem iUnion_W : ⋃ k, W k = Ioi 0 := by
  ext s
  simp only [mem_iUnion, mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩
    exact W_subset_Ioi k hk
  · intro hs
    exact ⟨dyIdx s, mem_W_dyIdx hs⟩

theorem lintegral_Ioi_eq_tsum (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi 0, f s = ∑' k, ∫⁻ s in W k, f s := by
  rw [← iUnion_W, lintegral_iUnion measurableSet_W W_disjoint]

theorem E_subset (k : ℤ) : E k ⊆ W (k - 1) ∪ W k ∪ W (k + 1) := by
  intro t ht
  have h1 : (2 : ℝ) ^ (k - 1) = 2 ^ k / 2 := by
    rw [zpow_sub_one₀ two_ne_zero, div_eq_mul_inv]
  have h2 : (2 : ℝ) ^ (k - 1 + 1) = 2 ^ k := by rw [sub_add_cancel]
  have h3 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [zpow_add_one₀ two_ne_zero, mul_comm]
  have h4 : (2 : ℝ) ^ (k + 1 + 1) = 4 * 2 ^ k := by
    rw [zpow_add_one₀ two_ne_zero, zpow_add_one₀ two_ne_zero]
    ring
  simp only [E, mem_Ico] at ht
  simp only [W, mem_union, mem_Ico, h1, h2, h3, h4]
  by_cases hA : t < 2 ^ k
  · exact Or.inl (Or.inl ⟨ht.1, hA⟩)
  · by_cases hB : t < 2 * 2 ^ k
    · exact Or.inl (Or.inr ⟨not_lt.1 hA, hB⟩)
    · exact Or.inr ⟨not_lt.1 hB, ht.2⟩

/-- The enlarged windows overlap at most three times. -/
theorem tsum_lintegral_E_le (f : ℝ → ℝ≥0∞) :
    ∑' k, ∫⁻ t in E k, f t ≤ 3 * ∫⁻ t in Ioi 0, f t := by
  have h1 : ∀ k, ∫⁻ t in E k, f t ≤
      (∫⁻ t in W (k - 1), f t) + (∫⁻ t in W k, f t) + ∫⁻ t in W (k + 1), f t := by
    intro k
    calc ∫⁻ t in E k, f t ≤ ∫⁻ t in W (k - 1) ∪ W k ∪ W (k + 1), f t :=
          lintegral_mono_set (E_subset k)
      _ ≤ (∫⁻ t in W (k - 1) ∪ W k, f t) + ∫⁻ t in W (k + 1), f t := lintegral_union_le _ _ _
      _ ≤ (∫⁻ t in W (k - 1), f t) + (∫⁻ t in W k, f t) + ∫⁻ t in W (k + 1), f t :=
          add_le_add_left (lintegral_union_le _ _ _) _
  have e1 : ∑' k : ℤ, ∫⁻ t in W (k - 1), f t = ∑' k, ∫⁻ t in W k, f t :=
    (Equiv.subRight (1 : ℤ)).tsum_eq (fun k => ∫⁻ t in W k, f t)
  have e2 : ∑' k : ℤ, ∫⁻ t in W (k + 1), f t = ∑' k, ∫⁻ t in W k, f t :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => ∫⁻ t in W k, f t)
  calc ∑' k, ∫⁻ t in E k, f t
      ≤ ∑' k, ((∫⁻ t in W (k - 1), f t) + (∫⁻ t in W k, f t) + ∫⁻ t in W (k + 1), f t) :=
        ENNReal.tsum_le_tsum h1
    _ = (∑' k, ∫⁻ t in W (k - 1), f t) + (∑' k, ∫⁻ t in W k, f t) +
          ∑' k, ∫⁻ t in W (k + 1), f t := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ = 3 * ∫⁻ t in Ioi 0, f t := by
        rw [e1, e2, ← lintegral_Ioi_eq_tsum]
        ring

/-- Summation over dyadic windows. -/
theorem lintegral_Ioi_le_of_windows {Φ Ψ : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ k : ℤ, ∫⁻ s in W k, Φ s ≤ C * ∫⁻ t in E k, Ψ t) :
    ∫⁻ s in Ioi 0, Φ s ≤ 3 * C * ∫⁻ t in Ioi 0, Ψ t := by
  rw [lintegral_Ioi_eq_tsum]
  calc ∑' k, ∫⁻ s in W k, Φ s ≤ ∑' k, C * ∫⁻ t in E k, Ψ t := ENNReal.tsum_le_tsum h
    _ = C * ∑' k, ∫⁻ t in E k, Ψ t := ENNReal.tsum_mul_left
    _ ≤ C * (3 * ∫⁻ t in Ioi 0, Ψ t) := by
        gcongr
        exact tsum_lintegral_E_le Ψ
    _ = 3 * C * ∫⁻ t in Ioi 0, Ψ t := by ring

/-! ## One window of the heat estimate -/

/-- The source window: if `Y(t) ≤ 1_{[a/2,4a)}(t) a^{-1} Z(t)`, then
`a^{a_p+p} ∫ Y^p ≤ 16 ∫_{[a/2,4a)} t^{a_p} Z^p`. -/
theorem window_source {p a : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) (ha : 0 < a) {Y Z : ℝ → ℝ≥0∞}
    (hY : ∀ t, Y t ≤ (Ico (a / 2) (4 * a)).indicator (fun t => ENNReal.ofReal a⁻¹ * Z t) t) :
    ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) * ∫⁻ t in Ioi 0, Y t ^ p ≤
      16 * ∫⁻ t in Ico (a / 2) (4 * a), ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p := by
  have hp0 : 0 < p := by linarith
  have hYp : ∀ t, Y t ^ p ≤
      (Ico (a / 2) (4 * a)).indicator (fun t => (ENNReal.ofReal a⁻¹ * Z t) ^ p) t := by
    intro t
    have h := hY t
    by_cases ht : t ∈ Ico (a / 2) (4 * a)
    · rw [Set.indicator_of_mem ht] at h ⊢
      exact ENNReal.rpow_le_rpow h hp0.le
    · rw [Set.indicator_of_notMem ht] at h ⊢
      rw [nonpos_iff_eq_zero.1 h, ENNReal.zero_rpow_of_pos hp0]
  have hcoef : ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) * ENNReal.ofReal a⁻¹ ^ p =
      ENNReal.ofReal (a ^ (p / 2 - 5 / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 ha.le) hp0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), Real.inv_rpow ha.le,
      ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
    congr 2
    ring
  calc ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) * ∫⁻ t in Ioi 0, Y t ^ p
      ≤ ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) *
          ∫⁻ t, (Ico (a / 2) (4 * a)).indicator
            (fun t => (ENNReal.ofReal a⁻¹ * Z t) ^ p) t := by
        exact mul_le_mul_of_nonneg_left
          ((setLIntegral_le_lintegral _ _).trans (lintegral_mono hYp)) zero_le
    _ = ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) *
          ∫⁻ t in Ico (a / 2) (4 * a), (ENNReal.ofReal a⁻¹ * Z t) ^ p := by
        rw [lintegral_indicator measurableSet_Ico]
    _ = ∫⁻ t in Ico (a / 2) (4 * a), ENNReal.ofReal (a ^ (p / 2 - 5 / 2)) * Z t ^ p := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun t => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← mul_assoc, hcoef]
    _ ≤ ∫⁻ t in Ico (a / 2) (4 * a), 16 * (ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p) := by
        refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
        have h16 : ENNReal.ofReal (a ^ (p / 2 - 5 / 2)) ≤
            16 * ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) := by
          calc ENNReal.ofReal (a ^ (p / 2 - 5 / 2))
              ≤ ENNReal.ofReal (16 * t ^ (p / 2 - 5 / 2)) :=
                ENNReal.ofReal_le_ofReal (rpow_source_le hp1 hp3 ha ht)
            _ = 16 * ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) := by
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h16 zero_le
    _ = 16 * ∫⁻ t in Ico (a / 2) (4 * a), ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p := by
        rw [lintegral_const_mul' _ _ (by norm_num)]

/-- One window of the weighted heat estimate (tex lines 3797–3801): from the maximal-regularity
bound `∫ (ν X)^p ≤ C^p ∫ Y^p` and the source bound `Y ≤ 1_{[a/2,4a)} a^{-1} Z`,
`∫_{[a,2a)} s^{a_p} (ν s X)^p ≤ 128 C^p ∫_{[a/2,4a)} t^{a_p} Z^p`. -/
theorem window_D2 {p a ν : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) (ha : 0 < a) (hν : 0 < ν)
    {X Y Z : ℝ → ℝ≥0∞} {CM : ℝ≥0∞}
    (hmr : ∫⁻ s in Ioi 0, (ENNReal.ofReal ν * X s) ^ p ≤ CM ^ p * ∫⁻ t in Ioi 0, Y t ^ p)
    (hY : ∀ t, Y t ≤ (Ico (a / 2) (4 * a)).indicator (fun t => ENNReal.ofReal a⁻¹ * Z t) t) :
    ∫⁻ s in Ico a (2 * a), ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
        (ENNReal.ofReal (ν * s) * X s) ^ p ≤
      128 * CM ^ p * ∫⁻ t in Ico (a / 2) (4 * a), ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p := by
  have hp0 : 0 < p := by linarith
  have hsub : Ico a (2 * a) ⊆ Ioi 0 := fun s hs => ha.trans_le hs.1
  calc ∫⁻ s in Ico a (2 * a), ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
          (ENNReal.ofReal (ν * s) * X s) ^ p
      ≤ ∫⁻ s in Ico a (2 * a), 8 * ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) *
          (ENNReal.ofReal ν * X s) ^ p := by
        refine setLIntegral_mono' measurableSet_Ico fun s hs => ?_
        have hs0 : 0 < s := ha.trans_le hs.1
        have e1 : ENNReal.ofReal (ν * s) * X s = ENNReal.ofReal s * (ENNReal.ofReal ν * X s) := by
          rw [ENNReal.ofReal_mul hν.le]
          ring
        rw [e1, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← mul_assoc,
          ENNReal.ofReal_rpow_of_nonneg hs0.le hp0.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        calc ENNReal.ofReal (s ^ (p / 2 - 5 / 2) * s ^ p)
            ≤ ENNReal.ofReal (8 * a ^ (p / 2 - 5 / 2 + p)) :=
              ENNReal.ofReal_le_ofReal (rpow_window_le hp1 hp3 ha hs)
          _ = 8 * ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ = 8 * ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) *
          ∫⁻ s in Ico a (2 * a), (ENNReal.ofReal ν * X s) ^ p := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
    _ ≤ 8 * ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) *
          ∫⁻ s in Ioi 0, (ENNReal.ofReal ν * X s) ^ p := by
        exact mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
    _ ≤ 8 * ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) * (CM ^ p * ∫⁻ t in Ioi 0, Y t ^ p) := by
        gcongr
    _ = 8 * CM ^ p * (ENNReal.ofReal (a ^ (p / 2 - 5 / 2 + p)) * ∫⁻ t in Ioi 0, Y t ^ p) := by
        ring
    _ ≤ 8 * CM ^ p * (16 * ∫⁻ t in Ico (a / 2) (4 * a),
          ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p) := by
        exact mul_le_mul_of_nonneg_left (window_source hp1 hp3 ha hY) zero_le
    _ = 128 * CM ^ p * ∫⁻ t in Ico (a / 2) (4 * a),
          ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p := by
        ring

end UnforcedLeray.B0289
