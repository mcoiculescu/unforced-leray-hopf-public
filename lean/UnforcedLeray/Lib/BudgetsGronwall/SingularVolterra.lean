import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Uniqueness for the square-root singular Volterra inequality (INF30, target T30.3a)


§5, Level 5, target T30.3a; bypass B14 (no general Henry inequality).

B0296 (`unlabeled:5039`, tex 5033–5053) and B0679 (`unlabeled:5678`, tex 5678–5682): if a
continuous `h ≥ 0` on `[s₀, T]` satisfies
`h(t) ≤ K ∫_{s₀}^t (t - r)^{-1/2} h(r) dr`,
then `h ≡ 0` ("on a sufficiently short interval the multiplier is strictly smaller than one;
iterating proves uniqueness on every finite interval"). The proof follows B14: on a window
`[a, a + δ]` after the last point where `h` is known to vanish, the maximum `M` of `h` satisfies
`M ≤ 2 K √δ M`, so `M = 0` once `2 K √δ < 1`; finitely many windows cover `[s₀, T]`.

Junk values. `(t - r)^{-1/2}` is the real power; at `r = t` it is `0^{-1/2} = 0`, a single
point, and for `r < t` it is the genuine value. The integrand is integrable on `[s₀, t]`
(`intervalIntegrable_kernel_mul`), so the hypothesis is the manuscript's inequality and not a
statement about a junk integral. `K` may have any sign.

`integral_kernel` is copied from the draft

-/

set_option autoImplicit false

open Set Filter Topology intervalIntegral MeasureTheory

namespace UnforcedLeray.Gronwall

/-- The unweighted kernel integral `∫_s^τ (τ - r)^{-1/2} dr = 2 (τ - s)^{1/2}` (copied from the
draft `Infra/VolterraEvolution/Kernel.lean`, `integral_kernel`). -/
theorem integral_kernel_rpow {s τ : ℝ} :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) = 2 * (τ - s) ^ (1 / 2 : ℝ) := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) (a := s) (b := τ) τ
  simp only [sub_self] at hsub
  rw [hsub, integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num)]
  ring

/-- The kernel `r ↦ (t - r)^{-1/2}` is integrable on every bounded interval. -/
theorem intervalIntegrable_kernel (t a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => (t - r) ^ (-(1 / 2 : ℝ))) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := t - b)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t
  simpa only [sub_sub_cancel] using h

/-- The kernel times a function continuous on `[a, b]` is integrable on `[a, b]`. -/
theorem intervalIntegrable_kernel_mul {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (uIcc a b))
    (t : ℝ) : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-(1 / 2 : ℝ)) * h r) volume a b :=
  (intervalIntegrable_kernel t a b).mul_continuousOn hh

/-- One window of the iteration: if `h` vanishes on `[s₀, a]`, then it vanishes on
`[s₀, min (a + δ) T]` whenever `2 K⁺ √δ < 1`. -/
theorem singular_volterra_step {h : ℝ → ℝ} {s₀ T K δ : ℝ} (hh : ContinuousOn h (Icc s₀ T))
    (h0 : ∀ t ∈ Icc s₀ T, 0 ≤ h t) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hsmall : 2 * K * Real.sqrt δ < 1)
    (hineq : ∀ t ∈ Icc s₀ T, h t ≤ K * ∫ r in s₀..t, (t - r) ^ (-(1 / 2 : ℝ)) * h r)
    {a : ℝ} (ha : a ∈ Icc s₀ T) (hzero : ∀ t ∈ Icc s₀ a, h t = 0) :
    ∀ t ∈ Icc s₀ (min (a + δ) T), h t = 0 := by
  set b := min (a + δ) T with hbdef
  have hab : a ≤ b := le_min (by linarith) ha.2
  have hbT : b ≤ T := min_le_right _ _
  have hbδ : b ≤ a + δ := min_le_left _ _
  -- the maximum of `h` on `[a, b]`
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab)
    (hh.mono (Icc_subset_Icc ha.1 hbT))
  have ht₀I : t₀ ∈ Icc s₀ T := ⟨ha.1.trans ht₀.1, ht₀.2.trans hbT⟩
  set M := h t₀ with hMdef
  have hM0 : 0 ≤ M := h0 t₀ ht₀I
  have hcont : ∀ {c d : ℝ}, s₀ ≤ c → c ≤ d → d ≤ T → ContinuousOn h (uIcc c d) :=
    fun hc hcd hd => hh.mono (by rw [uIcc_of_le hcd]; exact Icc_subset_Icc hc hd)
  have hint1 : IntervalIntegrable (fun r => (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r) volume s₀ a :=
    intervalIntegrable_kernel_mul (hcont le_rfl ha.1 ha.2) t₀
  have hint2 : IntervalIntegrable (fun r => (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r) volume a t₀ :=
    intervalIntegrable_kernel_mul (hcont ha.1 ht₀.1 ht₀I.2) t₀
  -- the integral over `[s₀, a]` vanishes
  have hfirst : ∫ r in s₀..a, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r = 0 := by
    have : ∫ r in s₀..a, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r = ∫ r in s₀..a, (0 : ℝ) := by
      refine integral_congr fun r hr => ?_
      rw [uIcc_of_le ha.1] at hr
      simp [hzero r hr]
    rw [this, intervalIntegral.integral_zero]
  -- the integral over `[a, t₀]` is at most `2 √δ M`
  have hsecond : ∫ r in a..t₀, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r ≤ 2 * Real.sqrt δ * M := by
    have hmono : ∫ r in a..t₀, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r ≤
        ∫ r in a..t₀, (t₀ - r) ^ (-(1 / 2 : ℝ)) * M := by
      refine integral_mono_on ht₀.1 hint2 ((intervalIntegrable_kernel t₀ a t₀).mul_const M)
        fun r hr => ?_
      have hk : 0 ≤ (t₀ - r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [hr.2]) _
      exact mul_le_mul_of_nonneg_left (hmax ⟨hr.1, hr.2.trans ht₀.2⟩) hk
    rw [intervalIntegral.integral_mul_const, integral_kernel_rpow] at hmono
    have hsq : (t₀ - a) ^ (1 / 2 : ℝ) ≤ Real.sqrt δ := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt (by linarith [ht₀.2])
    calc _ ≤ 2 * (t₀ - a) ^ (1 / 2 : ℝ) * M := hmono
      _ ≤ 2 * Real.sqrt δ * M := by gcongr
  have hsplit := integral_add_adjacent_intervals hint1 hint2
  have hMle : M ≤ K * (2 * Real.sqrt δ * M) := by
    calc M ≤ K * ∫ r in s₀..t₀, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r := hineq t₀ ht₀I
      _ = K * ∫ r in a..t₀, (t₀ - r) ^ (-(1 / 2 : ℝ)) * h r := by
          rw [← hsplit, hfirst, zero_add]
      _ ≤ K * (2 * Real.sqrt δ * M) := mul_le_mul_of_nonneg_left hsecond hK
  have hMz : M = 0 := by
    have : M * (1 - 2 * K * Real.sqrt δ) ≤ 0 := by nlinarith
    have hpos : 0 < 1 - 2 * K * Real.sqrt δ := by linarith
    nlinarith
  intro t ht
  rcases le_or_gt t a with hta | hta
  · exact hzero t ⟨ht.1, hta⟩
  · have htI : t ∈ Icc s₀ T := ⟨ht.1, ht.2.trans hbT⟩
    exact le_antisymm (hMz ▸ hmax ⟨hta.le, ht.2⟩) (h0 t htI)

/-- **Uniqueness for the singular Volterra inequality** (T30.3a; B0296 tex 5033–5053,
B0679 tex 5678–5682). If `h` is continuous and nonnegative on `[s₀, T]` and
`h(t) ≤ K ∫_{s₀}^t (t - r)^{-1/2} h(r) dr` for `t ∈ [s₀, T]`, then `h = 0` on `[s₀, T]`. -/
theorem eq_zero_of_singular_volterra {h : ℝ → ℝ} {s₀ T K : ℝ} (hh : ContinuousOn h (Icc s₀ T))
    (h0 : ∀ t ∈ Icc s₀ T, 0 ≤ h t)
    (hineq : ∀ t ∈ Icc s₀ T, h t ≤ K * ∫ r in s₀..t, (t - r) ^ (-(1 / 2 : ℝ)) * h r) :
    ∀ t ∈ Icc s₀ T, h t = 0 := by
  intro t ht
  have hs₀T : s₀ ≤ T := ht.1.trans ht.2
  -- replace `K` by `K⁺ = max K 0`
  set K' := max K 0 with hK'def
  have hK' : 0 ≤ K' := le_max_right _ _
  have hineq' : ∀ t ∈ Icc s₀ T, h t ≤ K' * ∫ r in s₀..t, (t - r) ^ (-(1 / 2 : ℝ)) * h r := by
    intro t ht
    have hI : 0 ≤ ∫ r in s₀..t, (t - r) ^ (-(1 / 2 : ℝ)) * h r :=
      integral_nonneg ht.1 fun r hr =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (h0 r ⟨hr.1, hr.2.trans ht.2⟩)
    exact (hineq t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hI)
  -- the window length
  set c : ℝ := 1 / (2 * (K' + 1)) with hcdef
  have hc : 0 < c := by positivity
  set δ : ℝ := c ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hsqrtδ : Real.sqrt δ = c := Real.sqrt_sq hc.le
  have hsmall : 2 * K' * Real.sqrt δ < 1 := by
    rw [hsqrtδ, hcdef]
    rw [show 2 * K' * (1 / (2 * (K' + 1))) = K' / (K' + 1) by field_simp]
    rw [div_lt_one (by linarith)]
    linarith
  -- the starting point
  have hs₀ : h s₀ = 0 := by
    have := hineq' s₀ ⟨le_rfl, hs₀T⟩
    rw [integral_same, mul_zero] at this
    exact le_antisymm this (h0 s₀ ⟨le_rfl, hs₀T⟩)
  -- induction over windows
  have hind : ∀ n : ℕ, ∀ u ∈ Icc s₀ (min (s₀ + n * δ) T), h u = 0 := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have hu2 : u ≤ s₀ + ((0 : ℕ) : ℝ) * δ :=
        hu.2.trans (min_le_left (s₀ + ((0 : ℕ) : ℝ) * δ) T)
      have hu3 : u ≤ s₀ := by
        rw [Nat.cast_zero, zero_mul, add_zero] at hu2
        exact hu2
      have : u = s₀ := le_antisymm hu3 hu.1
      rw [this, hs₀]
    | succ n ih =>
      set a := min (s₀ + n * δ) T with hadef
      have h1 : s₀ ≤ s₀ + n * δ := by
        have : (0 : ℝ) ≤ n * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
        linarith
      have ha : a ∈ Icc s₀ T := ⟨le_min h1 hs₀T, min_le_right _ _⟩
      have hstep := singular_volterra_step hh h0 hK' hδ.le hsmall hineq' ha ih
      intro u hu
      refine hstep u ⟨hu.1, hu.2.trans ?_⟩
      rcases le_total (s₀ + n * δ) T with hle | hle
      · rw [hadef, min_eq_left hle]
        apply min_le_min _ le_rfl
        push_cast; linarith
      · rw [hadef, min_eq_right hle]
        exact (min_le_right (s₀ + ((n + 1 : ℕ) : ℝ) * δ) T).trans
          (le_min (by linarith [hδ.le]) le_rfl)
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - s₀) / δ)
  have hnT : T ≤ s₀ + n * δ := by
    rw [div_lt_iff₀ hδ] at hn; linarith
  exact hind n t ⟨ht.1, by rw [min_eq_right hnT]; exact ht.2⟩

end UnforcedLeray.Gronwall
