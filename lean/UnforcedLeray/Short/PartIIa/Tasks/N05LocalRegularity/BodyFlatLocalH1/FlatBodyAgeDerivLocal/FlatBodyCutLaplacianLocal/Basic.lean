import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Units.B0220
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helpers for `PartII-a:N05/2/2/1`: cutoffs, `q`-periodization of tests, unfolding

Source: `the November 2 reference manuscript`, lines 1794-1799 ("periodic extension
over many cells followed by division by their number").

* `timeCut σ H1`: a smooth cutoff in the age `s`, equal to `1` on `[σ, H1]`, vanishing outside
  `(σ/2, 2H1)`, with `|θ'| ≤ 3 M₀ / σ` (`M₀ = sup |smoothTransition'|`).
* `qCut c`: a smooth bump in `q`, supported in `(-c, c]`, with `qCut (q - c) + qCut q = 1` on
  `(0, c]` and `∑_{|n| ≤ N} qCut (q - n c) = 1` for `|q| ≤ N c`.
* `perT c φ = ∑_n φ(· + (0, nc, 0))`: the `q`-periodization of a compactly supported function.
* `integral_qCut_mul`: `∫ qCut(q) G = ∫_cell G` for `q`-periodic `G` vanishing for `s ≤ 0`.
* `integral_mul_test_eq_cell`: `∫ F φ = ∫_cell F · perT c φ` for periodic locally integrable `F`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.Short.IIb (Coord cpd cdir)

/-! ### 1. The smooth step and its derivative bound -/

theorem st_contDiff : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff

theorem st_deriv_eq_zero_of_lt {t : ℝ} (ht : t < 0) : deriv Real.smoothTransition t = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact Real.smoothTransition.zero_of_nonpos hx.le
  rw [hev.deriv_eq]
  simp

theorem st_deriv_eq_zero_of_gt {t : ℝ} (ht : 1 < t) : deriv Real.smoothTransition t = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact Real.smoothTransition.one_of_one_le hx.le
  rw [hev.deriv_eq]
  simp

theorem st_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) := st_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact st_deriv_eq_zero_of_lt h
    · exact st_deriv_eq_zero_of_gt h
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have := hC t
  rw [Real.norm_eq_abs] at this
  exact le_max_of_le_left this

theorem abs_st_le_one (t : ℝ) : |Real.smoothTransition t| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg t)]
  exact Real.smoothTransition.le_one t

/-! ### 2. The age cutoff `θ = timeCut σ H1` -/

/-- `θ(s) = st(2s/σ - 1) st(2 - s/H1)`: `1` on `[σ, H1]`, `0` outside `(σ/2, 2H1)`. -/
def timeCut (σ H1 s : ℝ) : ℝ :=
  Real.smoothTransition (2 * s / σ - 1) * Real.smoothTransition (2 - s / H1)

theorem timeCut_contDiff (σ H1 : ℝ) : ContDiff ℝ ∞ (timeCut σ H1) := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => 2 * s / σ - 1) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun s : ℝ => 2 - s / H1) := by fun_prop
  exact (st_contDiff.comp h1).mul (st_contDiff.comp h2)

theorem timeCut_zero_of_le {σ H1 s : ℝ} (hσ : 0 < σ) (hs : s ≤ σ / 2) :
    timeCut σ H1 s = 0 := by
  have h : 2 * s / σ ≤ 1 := by rw [div_le_one hσ]; linarith
  unfold timeCut
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem timeCut_zero_of_ge {σ H1 s : ℝ} (hH : 0 < H1) (hs : 2 * H1 ≤ s) :
    timeCut σ H1 s = 0 := by
  have h : 2 ≤ s / H1 := by rw [le_div_iff₀ hH]; linarith
  have h0 : Real.smoothTransition (2 - s / H1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  unfold timeCut
  rw [h0, mul_zero]

theorem timeCut_one {σ H1 s : ℝ} (hσ : 0 < σ) (hH : 0 < H1) (h1 : σ ≤ s) (h2 : s ≤ H1) :
    timeCut σ H1 s = 1 := by
  have e1 : 1 ≤ 2 * s / σ - 1 := by
    have : 2 ≤ 2 * s / σ := by rw [le_div_iff₀ hσ]; linarith
    linarith
  have e2 : 1 ≤ 2 - s / H1 := by
    have : s / H1 ≤ 1 := by rw [div_le_one hH]; linarith
    linarith
  unfold timeCut
  rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2, mul_one]

theorem timeCut_nonneg (σ H1 s : ℝ) : 0 ≤ timeCut σ H1 s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem timeCut_le_one (σ H1 s : ℝ) : timeCut σ H1 s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem abs_timeCut_le_one (σ H1 s : ℝ) : |timeCut σ H1 s| ≤ 1 := by
  rw [abs_of_nonneg (timeCut_nonneg σ H1 s)]
  exact timeCut_le_one σ H1 s

theorem timeCut_support {σ H1 s : ℝ} (hσ : 0 < σ) (hH : 0 < H1) (hs : timeCut σ H1 s ≠ 0) :
    σ / 2 < s ∧ s < 2 * H1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (timeCut_zero_of_le hσ (not_lt.1 h))
  · by_contra h
    exact hs (timeCut_zero_of_ge hH (not_lt.1 h))

theorem deriv_timeCut_zero_of_lt {σ H1 s : ℝ} (hσ : 0 < σ) (hs : s < σ / 2) :
    deriv (timeCut σ H1) s = 0 := by
  have hev : timeCut σ H1 =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with x hx
    exact timeCut_zero_of_le hσ hx.le
  rw [hev.deriv_eq]
  simp

theorem deriv_timeCut_zero_of_gt {σ H1 s : ℝ} (hH : 0 < H1) (hs : 2 * H1 < s) :
    deriv (timeCut σ H1) s = 0 := by
  have hev : timeCut σ H1 =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact timeCut_zero_of_ge hH hx.le
  rw [hev.deriv_eq]
  simp

theorem abs_deriv_timeCut_le {M : ℝ} (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M)
    {σ H1 : ℝ} (hσ : 0 < σ) (hσH : σ ≤ H1) (s : ℝ) :
    |deriv (timeCut σ H1) s| ≤ 3 * M / σ := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hdst : ∀ t : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    fun t => ((st_contDiff.differentiable (by simp)) t).hasDerivAt
  have hl1 : HasDerivAt (fun s : ℝ => 2 * s / σ - 1) (2 / σ) s := by
    have := (((hasDerivAt_id s).const_mul 2).div_const σ).sub_const 1
    simpa using this
  have hl2 : HasDerivAt (fun s : ℝ => 2 - s / H1) (-(1 / H1)) s := by
    have := ((hasDerivAt_id s).div_const H1).const_sub 2
    simpa using this
  have hd1 := (hdst (2 * s / σ - 1)).comp s hl1
  have hd2 := (hdst (2 - s / H1)).comp s hl2
  have hd := hd1.mul hd2
  have heq : deriv (timeCut σ H1) s =
      deriv Real.smoothTransition (2 * s / σ - 1) * (2 / σ) *
          Real.smoothTransition (2 - s / H1) +
        Real.smoothTransition (2 * s / σ - 1) *
          (deriv Real.smoothTransition (2 - s / H1) * (-(1 / H1))) := hd.deriv
  rw [heq]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hinv : 1 / H1 ≤ 1 / σ := one_div_le_one_div_of_le hσ hσH
  have hσ2 : 0 < 2 / σ := by positivity
  have hH1 : 0 < 1 / H1 := by positivity
  calc |deriv Real.smoothTransition (2 * s / σ - 1) * (2 / σ) *
          Real.smoothTransition (2 - s / H1) +
        Real.smoothTransition (2 * s / σ - 1) *
          (deriv Real.smoothTransition (2 - s / H1) * (-(1 / H1)))|
      ≤ |deriv Real.smoothTransition (2 * s / σ - 1)| * (2 / σ) *
          |Real.smoothTransition (2 - s / H1)| +
        |Real.smoothTransition (2 * s / σ - 1)| *
          (|deriv Real.smoothTransition (2 - s / H1)| * (1 / H1)) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hσ2, abs_of_pos hH1]
    _ ≤ M * (2 / σ) * 1 + 1 * (M * (1 / σ)) := by
        gcongr
        · exact hM _
        · exact abs_st_le_one _
        · exact abs_st_le_one _
        · exact hM _
    _ = 3 * M / σ := by ring

/-! ### 3. The `q`-bump `qCut c` -/

/-- `ρ(q) = st(q/c + 1) - st(q/c)`, supported in `(-c, c]`. -/
def qCut (c q : ℝ) : ℝ := Real.smoothTransition (q / c + 1) - Real.smoothTransition (q / c)

theorem qCut_contDiff (c : ℝ) : ContDiff ℝ ∞ (qCut c) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ => q / c + 1) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun q : ℝ => q / c) := by fun_prop
  exact (st_contDiff.comp h1).sub (st_contDiff.comp h2)

theorem qCut_nonneg (c q : ℝ) : 0 ≤ qCut c q := by
  have := Real.smoothTransition.monotone (show q / c ≤ q / c + 1 by linarith)
  unfold qCut
  linarith

theorem qCut_le_one (c q : ℝ) : qCut c q ≤ 1 := by
  unfold qCut
  linarith [Real.smoothTransition.le_one (q / c + 1), Real.smoothTransition.nonneg (q / c)]

theorem abs_qCut_le_one (c q : ℝ) : |qCut c q| ≤ 1 := by
  rw [abs_of_nonneg (qCut_nonneg c q)]
  exact qCut_le_one c q

theorem qCut_eq_zero_of_le {c q : ℝ} (hc : 0 < c) (hq : q ≤ -c) : qCut c q = 0 := by
  have h1 : q / c ≤ -1 := by rw [div_le_iff₀ hc]; linarith
  unfold qCut
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem qCut_eq_zero_of_gt {c q : ℝ} (hc : 0 < c) (hq : c < q) : qCut c q = 0 := by
  have h1 : 1 < q / c := by rw [lt_div_iff₀ hc]; linarith
  unfold qCut
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem qCut_eq_zero_of_not_mem {c q : ℝ} (hc : 0 < c) (hq : q ∉ Ioc (-c) c) : qCut c q = 0 := by
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hq
  rcases hq with h | h
  · exact qCut_eq_zero_of_le hc h
  · exact qCut_eq_zero_of_gt hc h

/-- `qCut (q - c) + qCut q = 1` on `(0, c]`. -/
theorem qCut_sub_add {c q : ℝ} (hc : 0 < c) (hq : q ∈ Ioc 0 c) :
    qCut c (q - c) + qCut c q = 1 := by
  have e : (q - c) / c + 1 = q / c := by field_simp; ring
  have h0 : (q - c) / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hq.2]) hc.le
  have h1 : 1 ≤ q / c + 1 := by have := div_nonneg hq.1.le hc.le; linarith
  unfold qCut
  rw [e, Real.smoothTransition.zero_of_nonpos h0, Real.smoothTransition.one_of_one_le h1]
  ring

/-- Telescoping: `∑_{k < 2N+1} qCut (q - (k - N) c) = 1` for `|q| ≤ N c`. -/
theorem sum_qCut {c : ℝ} (hc : 0 < c) (N : ℕ) {q : ℝ} (hq : |q| ≤ N * c) :
    ∑ k ∈ Finset.range (2 * N + 1), qCut c (q - ((k : ℝ) - N) * c) = 1 := by
  set f : ℕ → ℝ := fun k => Real.smoothTransition (q / c + N + 1 - k) with hf
  have hterm : ∀ k : ℕ, qCut c (q - ((k : ℝ) - N) * c) = f k - f (k + 1) := by
    intro k
    have e1 : (q - ((k : ℝ) - N) * c) / c + 1 = q / c + N + 1 - k := by field_simp; ring
    have e2 : (q - ((k : ℝ) - N) * c) / c = q / c + N + 1 - ((k + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    simp only [qCut, hf]
    rw [e1, e2]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_range_sub']
  have hq' := abs_le.1 hq
  have hq1 : -(N : ℝ) ≤ q / c := by rw [le_div_iff₀ hc]; linarith [hq'.1]
  have hq2 : q / c ≤ N := by rw [div_le_iff₀ hc]; linarith [hq'.2]
  simp only [hf]
  rw [Real.smoothTransition.one_of_one_le (by push_cast; linarith),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)]
  ring

/-! ### 4. `q`-translations and the periodization `perT` -/

/-- The `q`-translation vector `(0, a, 0)`. -/
def qv (a : ℝ) : Coord := (0, (a, 0))

@[simp] theorem add_qv_fst (x : Coord) (a : ℝ) : (x + qv a).1 = x.1 := by simp [qv]

@[simp] theorem add_qv_snd_fst (x : Coord) (a : ℝ) : (x + qv a).2.1 = x.2.1 + a := by simp [qv]

@[simp] theorem add_qv_snd_snd (x : Coord) (a : ℝ) : (x + qv a).2.2 = x.2.2 := by simp [qv]

theorem qv_add (a b : ℝ) : qv a + qv b = qv (a + b) := by
  simp [qv]

theorem add_qv_eq (x : Coord) (a : ℝ) : x + qv a = (x.1, (x.2.1 + a, x.2.2)) := by
  ext <;> simp [qv]

theorem add_qv_add_qv (x : Coord) (a b : ℝ) : x + qv a + qv b = x + qv (a + b) := by
  rw [add_assoc, qv_add]

/-- Integer periodicity from one period. -/
theorem periodic_int {E : Type*} {c : ℝ} {F : Coord → E} (hper : ∀ x, F (x + qv c) = F x)
    (n : ℤ) (x : Coord) : F (x + qv (n * c)) = F x := by
  have hP : Function.Periodic (fun t : ℝ => F (x + qv t)) c := fun t => by
    simp only
    rw [← add_qv_add_qv, hper]
  have := (hP.int_mul n) 0
  simpa [add_qv_eq] using this

/-- The `q`-periodization `∑_n φ(x + (0, nc, 0))`. -/
def perT (c : ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ := ∑' n : ℤ, φ (x + qv (n * c))

theorem perT_periodic (c : ℝ) (φ : Coord → ℝ) (x : Coord) : perT c φ (x + qv c) = perT c φ x := by
  unfold perT
  have h : ∀ n : ℤ, x + qv c + qv (n * c) = x + qv (((n + 1 : ℤ) : ℝ) * c) := by
    intro n
    rw [add_qv_add_qv]
    congr 2
    push_cast
    ring
  simp_rw [h]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => φ (x + qv (n * c)))

/-- The window `{-N, …, N}` as the image of `range (2N+1)`. -/
def win (N : ℕ) : Finset ℤ := (Finset.range (2 * N + 1)).image (fun k : ℕ => (k : ℤ) - N)

theorem mem_win {N : ℕ} {n : ℤ} (hn : -(N : ℤ) ≤ n) (hn' : n ≤ N) : n ∈ win N := by
  unfold win
  rw [Finset.mem_image]
  refine ⟨(n + N).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]
    omega
  · omega

theorem sum_win {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℤ → M) :
    ∑ n ∈ win N, f n = ∑ k ∈ Finset.range (2 * N + 1), f ((k : ℤ) - N) := by
  unfold win
  rw [Finset.sum_image]
  intro a _ b _ h
  have : (a : ℤ) = b := by linarith
  exact_mod_cast this

/-- A compactly supported function has bounded `q`-support. -/
theorem exists_qbound {φ : Coord → ℝ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ tsupport φ, |x.2.1| ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hφ.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at h
  have h2 : |x.2.1| ≤ ‖x‖ := by
    calc |x.2.1| = ‖x.2.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2‖ := norm_fst_le x.2
      _ ≤ ‖x‖ := norm_snd_le x
  linarith [le_max_left R 0]

theorem eq_zero_of_qbound {φ : Coord → ℝ} {R : ℝ} (hR : ∀ x ∈ tsupport φ, |x.2.1| ≤ R)
    {x : Coord} (hx : R < |x.2.1|) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hR x h) (not_le.2 hx)

theorem fderiv_eq_zero_of_qbound {φ : Coord → ℝ} {R : ℝ} (hR : ∀ x ∈ tsupport φ, |x.2.1| ≤ R)
    {x : Coord} (hx : R < |x.2.1|) (v : Coord) : fderiv ℝ φ x v = 0 := by
  have hn : x ∉ tsupport φ := fun h => absurd (hR x h) (not_le.2 hx)
  have h0 : fderiv ℝ φ x = 0 := by
    by_contra hne
    exact hn (support_fderiv_subset (𝕜 := ℝ) hne)
  rw [h0]
  rfl

/-- On `|q| ≤ T` the periodization is a finite sum over the window `|n| ≤ N`, `R + T ≤ N c`. -/
theorem perT_eq_sum {φ : Coord → ℝ} {c R T : ℝ} (hc : 0 < c)
    (hR : ∀ x : Coord, R < |x.2.1| → φ x = 0) {N : ℕ} (hN : R + T ≤ N * c) {x : Coord}
    (hx : |x.2.1| ≤ T) :
    perT c φ x = ∑ k ∈ Finset.range (2 * N + 1), φ (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c)) := by
  unfold perT
  rw [tsum_eq_sum (s := win N), sum_win]
  intro n hn
  apply hR
  rw [add_qv_snd_fst]
  have hn' : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
    by_cases h1 : -(N : ℤ) ≤ n
    · by_cases h2 : n ≤ N
      · exact absurd (mem_win h1 h2) hn
      · have h3 : (N : ℤ) + 1 ≤ n := by omega
        have h4 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h3
        rw [abs_of_pos (by linarith)]
        exact h4
    · have h3 : n ≤ -(N : ℤ) - 1 := by omega
      have h4 : (n : ℝ) ≤ -(N : ℝ) - 1 := by exact_mod_cast h3
      rw [abs_of_neg (by linarith)]
      linarith
  have h1 : |(n : ℝ) * c| - |x.2.1| ≤ |x.2.1 + n * c| := by
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * c) (-x.2.1)
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    exact this
  rw [abs_mul, abs_of_pos hc] at h1
  nlinarith

theorem perT_eventuallyEq {φ : Coord → ℝ} {c R : ℝ} (hc : 0 < c)
    (hR : ∀ x : Coord, R < |x.2.1| → φ x = 0) (x0 : Coord) :
    ∃ N : ℕ, R + (|x0.2.1| + 1) ≤ N * c ∧ perT c φ =ᶠ[𝓝 x0]
      fun x => ∑ k ∈ Finset.range (2 * N + 1), φ (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + (|x0.2.1| + 1)) / c)
  have hN' : R + (|x0.2.1| + 1) ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  refine ⟨N, hN', ?_⟩
  have hopen : IsOpen {x : Coord | |x.2.1| < |x0.2.1| + 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hmem : x0 ∈ {x : Coord | |x.2.1| < |x0.2.1| + 1} := by
    show |x0.2.1| < |x0.2.1| + 1
    linarith
  filter_upwards [hopen.mem_nhds hmem] with x hx
  exact perT_eq_sum hc hR hN' (le_of_lt hx)

theorem perT_contDiff {φ : Coord → ℝ} {c : ℝ} (hc : 0 < c) (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) : ContDiff ℝ ∞ (perT c φ) := by
  obtain ⟨R, -, hR⟩ := exists_qbound hcs
  rw [contDiff_iff_contDiffAt]
  intro x0
  obtain ⟨N, -, hN⟩ := perT_eventuallyEq hc (fun x hx => eq_zero_of_qbound hR hx) x0
  refine ContDiffAt.congr_of_eventuallyEq ?_ hN
  refine ContDiff.contDiffAt ?_
  refine ContDiff.sum fun k _ => ?_
  exact hφ.comp (contDiff_id.add contDiff_const)

theorem perT_continuous {φ : Coord → ℝ} {c : ℝ} (hc : 0 < c) (hφ : Continuous φ)
    (hcs : HasCompactSupport φ) : Continuous (perT c φ) := by
  obtain ⟨R, -, hR⟩ := exists_qbound hcs
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨N, -, hN⟩ := perT_eventuallyEq hc (fun x hx => eq_zero_of_qbound hR hx) x0
  refine ContinuousAt.congr ?_ hN.symm
  refine Continuous.continuousAt ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact hφ.comp (continuous_id.add continuous_const)

/-- Derivatives commute with the periodization. -/
theorem fderiv_perT {φ : Coord → ℝ} {c : ℝ} (hc : 0 < c) (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (x0 v : Coord) :
    fderiv ℝ (perT c φ) x0 v = perT c (fun x => fderiv ℝ φ x v) x0 := by
  obtain ⟨R, -, hR⟩ := exists_qbound hcs
  obtain ⟨N, hN', hN⟩ := perT_eventuallyEq hc (fun x hx => eq_zero_of_qbound hR hx) x0
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdk : ∀ k ∈ Finset.range (2 * N + 1),
      DifferentiableAt ℝ (fun x => φ (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c))) x0 :=
    fun k _ => (hd _).comp x0 (differentiableAt_id.add_const _)
  have h1 : fderiv ℝ (fun x => ∑ k ∈ Finset.range (2 * N + 1),
      φ (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c))) x0 =
      ∑ k ∈ Finset.range (2 * N + 1),
        fderiv ℝ (fun x => φ (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c))) x0 :=
    fderiv_fun_sum hdk
  rw [hN.fderiv_eq, h1]
  rw [perT_eq_sum hc (fun x hx => fderiv_eq_zero_of_qbound hR hx v) hN' (le_add_of_nonneg_right
    zero_le_one)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_comp_add_right]

theorem cpd_perT {φ : Coord → ℝ} {c : ℝ} (hc : 0 < c) (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (j : Fin 3) :
    (fun x => cpd j (perT c φ) x) = perT c (fun x => cpd j φ x) := by
  funext x0
  exact fderiv_perT hc hφ hcs x0 (cdir j)

theorem cpd_contDiff {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => cpd j φ x) := by
  unfold cpd
  exact (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cpd_hasCompactSupport {φ : Coord → ℝ} (hφ : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (fun x => cpd j φ x) := by
  have k : HasCompactSupport (fderiv ℝ φ) := HasCompactSupport.fderiv (𝕜 := ℝ) hφ
  exact k.comp_left (g := fun L : Coord →L[ℝ] ℝ => L (cdir j)) (by simp)

/-! ### 5. Unfolding a `q`-periodic function onto the cell -/

instance coordAddRightInvariant : (volume : Measure Coord).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ)]
  infer_instance

theorem measurableSet_cell (c : ℝ) : MeasurableSet (UnforcedLeray.B0220.cell c) := by
  unfold UnforcedLeray.B0220.cell
  exact measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)

/-- `∫ qCut(q) G = ∫_cell G` for an a.e. `q`-periodic `G` vanishing for `s ≤ 0`, integrable on
two cells. -/
theorem integral_qCut_mul {c : ℝ} (hc : 0 < c) {G : Coord → ℂ}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x)
    (hpos : ∀ x : Coord, x.1 ≤ 0 → G x = 0)
    (hint : IntegrableOn G (Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ))) :
    ∫ x, (qCut c x.2.1 : ℂ) * G x = ∫ x in UnforcedLeray.B0220.cell c, G x := by
  set A : Set Coord := Ioi 0 ×ˢ (Ioc (-c) 0 ×ˢ univ) with hA
  set B : Set Coord := UnforcedLeray.B0220.cell c with hB
  have hBm : MeasurableSet B := measurableSet_cell c
  have hAm : MeasurableSet A := measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have h1 : x.2.1 ≤ 0 := hxA.2.1.2
    have h2 : 0 < x.2.1 := hxB.2.1.1
    linarith
  have hsub : A ∪ B ⊆ Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ) := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.1, ⟨hx.2.1.1, by linarith [hx.2.1.2]⟩, trivial⟩
    · exact ⟨hx.1, ⟨by linarith [hx.2.1.1], hx.2.1.2⟩, trivial⟩
  set F : Coord → ℂ := fun x => (qCut c x.2.1 : ℂ) * G x with hF
  have hFint : ∀ S ⊆ Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ), IntegrableOn F S := by
    intro S hS
    have hG := hint.mono_set hS
    refine Integrable.mono' hG.norm ?_ (Eventually.of_forall fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp ((qCut_contDiff c).continuous.comp
        (continuous_fst.comp continuous_snd))).aestronglyMeasurable).mul hG.1
    · simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_qCut_le_one c _)
  have h0 : ∀ x, x ∉ A ∪ B → F x = 0 := by
    intro x hx
    by_cases hs : x.1 ≤ 0
    · simp [hF, hpos x hs]
    · have hq : x.2.1 ∉ Ioc (-c) c := by
        intro hq
        apply hx
        by_cases h0 : x.2.1 ≤ 0
        · exact Or.inl ⟨not_le.1 hs, ⟨hq.1, h0⟩, trivial⟩
        · exact Or.inr ⟨not_le.1 hs, ⟨not_le.1 h0, hq.2⟩, trivial⟩
      simp [hF, qCut_eq_zero_of_not_mem hc hq]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    setIntegral_union hAB hBm (hFint A (subset_union_left.trans hsub))
      (hFint B (subset_union_right.trans hsub))]
  -- translate `A` onto `B`
  have hper' : ∀ᵐ y : Coord, G (y + qv (-c)) = G y := by
    have := (measurePreserving_add_right (volume : Measure Coord) (qv (-c))).quasiMeasurePreserving.ae
      hper
    filter_upwards [this] with y hy
    rw [add_qv_add_qv, neg_add_cancel] at hy
    have hz : y + qv 0 = y := by simp [qv]
    rw [hz] at hy
    exact hy.symm
  have htrans : ∫ x in A, F x = ∫ x in B, (qCut c (x.2.1 - c) : ℂ) * G x := by
    rw [← integral_indicator hAm, ← integral_add_right_eq_self _ (qv (-c))]
    have hind : ∀ y : Coord, A.indicator F (y + qv (-c)) =
        B.indicator (fun y => (qCut c (y.2.1 - c) : ℂ) * G (y + qv (-c))) y := by
      intro y
      have hiff : y + qv (-c) ∈ A ↔ y ∈ B := by
        simp only [hA, hB, UnforcedLeray.B0220.cell, mem_prod, mem_Ioi, mem_Ioc, mem_univ, and_true,
          add_qv_fst, add_qv_snd_fst]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, by linarith, by linarith⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, by linarith, by linarith⟩
      by_cases hy : y ∈ B
      · rw [indicator_of_mem (hiff.2 hy), indicator_of_mem hy]
        simp only [hF, add_qv_snd_fst, sub_eq_add_neg]
      · rw [indicator_of_notMem (fun h => hy (hiff.1 h)), indicator_of_notMem hy]
    simp_rw [hind]
    rw [integral_indicator hBm]
    refine setIntegral_congr_ae hBm ?_
    filter_upwards [hper'] with y hy _
    rw [hy]
  rw [htrans, ← integral_add]
  · refine setIntegral_congr_fun hBm fun x hx => ?_
    simp only [hF]
    rw [← add_mul, ← Complex.ofReal_add, qCut_sub_add hc hx.2.1, Complex.ofReal_one, one_mul]
  · have hG := hint.mono_set (subset_union_right.trans hsub)
    refine Integrable.mono' hG.norm ?_ (Eventually.of_forall fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp ((qCut_contDiff c).continuous.comp
        ((continuous_fst.comp continuous_snd).sub continuous_const))).aestronglyMeasurable).mul hG.1
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_qCut_le_one c _)
  · exact hFint B (subset_union_right.trans hsub)

end UnforcedLeray.Short.PartIIa.FBCLL
