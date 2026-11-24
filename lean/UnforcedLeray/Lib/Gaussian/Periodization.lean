import UnforcedLeray.Lib.Gaussian.LatticeSum
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Order.CompletePartialOrder

/-!
# The periodization operator (INF22 G7, part 1)


target G7; decision D1 (cylinder fields are `c`-periodic functions on `ℝ × ℝ`) and D14 (G7 is the
periodization used by INF13 CY09). Units B0140 (tex 2045–2057, 2131–2151), B0146 (tex
2196–2216), B0314/B0352/B0638 (tex 6037–6045, 6645–6653, 12572–12582), B0812 (i), (iv)
(tex 11843–11876), B0147 (tex 2217–2234).

`periodize c f (q, η) = ∑_{n∈ℤ} f(q - nc, η)` (the operator `P_c` of tex 6037–6045).

Main results:
* `summable_periodize` (lemma 1): absolute convergence under a translate bound
  `‖f(q,η)‖ ≤ C(1+|q|)^{-s}`, `s > 1` (weaker than the scoping's `(1+‖z‖)^{-2-δ}`, since only
  the decay in the periodized variable matters);
* `periodize_add_period`, `periodic_periodize` (lemma 2): `c`-periodicity in `q`;
* `iteratedFDeriv_periodize`, `contDiff_periodize` (lemma 3, B0812 (i), (iv), B0146 "termwise
  differentiation"): if `f` is `C^N` and each derivative of order `k ≤ N` satisfies the translate
  bound, then `periodize c f` is `C^N` and every iterated derivative is the periodization of the
  iterated derivative. The convergence is only locally uniform (on strips `|q - q₀| < 1`), so the
  proof re-runs Mathlib's `iteratedFDeriv_tsum` with `hasFDerivAt_tsum_of_isPreconnected`;
* `norm_periodize_le_of_gauss` (lemma 6, sup part; B0147): a Gaussian translate bound
  `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}` gives `‖periodize c f (q,η)‖ ≤ 10 A e^{-η²/(4a)}`, uniformly in
  `0 < a ≤ c²`.

The cell integral, moment invariance and the cell `L²` bound (lemmas 4–6) are in
`PeriodizationCell.lean`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real Set Metric Filter Topology

/-! ### Peetre-type inequality and translate sums -/

/-- `1 + |a + b| ≤ (1 + |a|)(1 + |b|)`. -/
theorem one_add_abs_add_le (a b : ℝ) : 1 + |a + b| ≤ (1 + |a|) * (1 + |b|) := by
  have h := abs_add_le a b
  have : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  nlinarith

/-- Peetre's inequality with a negative power: `(1+|x|)^{-s} ≤ (1+|y|)^s (1+|x+y|)^{-s}` for
`s ≥ 0`. -/
theorem one_add_abs_rpow_neg_le {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    (1 + |x|) ^ (-s) ≤ (1 + |y|) ^ s * (1 + |x + y|) ^ (-s) := by
  have hx : 0 < 1 + |x| := by positivity
  have hy : 0 < 1 + |y| := by positivity
  have hxy : 0 < 1 + |x + y| := by positivity
  have h := one_add_abs_add_le x y
  -- (1+|x+y|)^{-s} ≥ ((1+|x|)(1+|y|))^{-s}
  have h1 : ((1 + |x|) * (1 + |y|)) ^ (-s) ≤ (1 + |x + y|) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hxy h (by linarith)
  rw [Real.mul_rpow hx.le hy.le] at h1
  have hys : (1 + |y|) ^ s * (1 + |y|) ^ (-s) = 1 := by
    rw [← Real.rpow_add hy]; simp
  calc (1 + |x|) ^ (-s) = (1 + |y|) ^ s * ((1 + |x|) ^ (-s) * (1 + |y|) ^ (-s)) := by
        rw [mul_left_comm, hys, mul_one]
    _ ≤ (1 + |y|) ^ s * (1 + |x + y|) ^ (-s) := by gcongr

/-- `∑_{n∈ℤ} (1+|n|)^{-s}` converges for `s > 1`. -/
theorem summable_one_add_abs_int_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-s)) := by
  refine Summable.of_norm_bounded_eventually (summable_abs_int_rpow hs) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  exact Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)

/-- `∑_{n∈ℤ} (1+|q - nc|)^{-s}` converges for `s > 1`, `c ≠ 0`. -/
theorem summable_translate {s c : ℝ} (hs : 1 < s) (hc : c ≠ 0) (q : ℝ) :
    Summable (fun n : ℤ => (1 + |q - n * c|) ^ (-s)) := by
  set m : ℝ := min 1 |c| with hm
  have hm0 : 0 < m := lt_min one_pos (abs_pos.2 hc)
  set K : ℝ := m / (1 + |q|) with hK
  have hK0 : 0 < K := by positivity
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_one_add_abs_int_rpow hs).mul_left (K ^ (-s)))
  -- 1 + |q - nc| ≥ K (1 + |n|)
  have h1 : m * (1 + |(n : ℝ)|) ≤ 1 + |(n : ℝ) * c| := by
    rw [abs_mul]
    have := min_le_left 1 |c|
    have := min_le_right 1 |c|
    have hn : 0 ≤ |(n : ℝ)| := abs_nonneg _
    nlinarith
  have h2 : 1 + |(n : ℝ) * c| ≤ (1 + |q|) * (1 + |q - n * c|) := by
    have := one_add_abs_add_le q (-(q - n * c))
    rw [abs_neg, show q + -(q - n * c) = n * c by ring] at this
    exact this
  have h3 : K * (1 + |(n : ℝ)|) ≤ 1 + |q - n * c| := by
    rw [hK, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc (1 + |q - n * c|) ^ (-s) ≤ (K * (1 + |(n : ℝ)|)) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)
    _ = K ^ (-s) * (1 + |(n : ℝ)|) ^ (-s) := Real.mul_rpow hK0.le (by positivity)

/-- On a strip `|y - q₀| < 1`: `(1+|y - nc|)^{-s} ≤ 2^s (1+|q₀ - nc|)^{-s}`. -/
theorem translate_rpow_le_on_strip {s : ℝ} (hs : 0 ≤ s) {q₀ y : ℝ} (hy : |y - q₀| < 1)
    (t : ℝ) : (1 + |y - t|) ^ (-s) ≤ 2 ^ s * (1 + |q₀ - t|) ^ (-s) := by
  have h := one_add_abs_rpow_neg_le hs (y - t) (q₀ - y)
  rw [show y - t + (q₀ - y) = q₀ - t by ring] at h
  refine h.trans ?_
  gcongr
  rw [abs_sub_comm]; linarith

/-! ### Definition, summability, periodicity -/

section Def

variable {E : Type*} [NormedAddCommGroup E]

/-- **G7.** The periodization `P_c f(q,η) = ∑_{n∈ℤ} f(q - nc, η)` (tex 6037–6045). -/
def periodize (c : ℝ) (f : ℝ × ℝ → E) (z : ℝ × ℝ) : E := ∑' n : ℤ, f (z.1 - n * c, z.2)

/-- The lattice translation vector `(nc, 0)`. -/
def shiftVec (c : ℝ) (n : ℤ) : ℝ × ℝ := ((n : ℝ) * c, 0)

theorem sub_shiftVec (c : ℝ) (n : ℤ) (z : ℝ × ℝ) : z - shiftVec c n = (z.1 - n * c, z.2) := by
  ext <;> simp [shiftVec]

theorem periodize_eq (c : ℝ) (f : ℝ × ℝ → E) (z : ℝ × ℝ) :
    periodize c f z = ∑' n : ℤ, f (z - shiftVec c n) := by
  unfold periodize; simp_rw [sub_shiftVec]

/-- **G7, lemma 2.** Periodicity: `P_c f(q + c, η) = P_c f(q, η)`. -/
theorem periodize_add_period (c : ℝ) (f : ℝ × ℝ → E) (q η : ℝ) :
    periodize c f (q + c, η) = periodize c f (q, η) := by
  unfold periodize
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  congr 1; funext n
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  congr 2; ring

theorem periodic_periodize (c : ℝ) (f : ℝ × ℝ → E) (η : ℝ) :
    Function.Periodic (fun q => periodize c f (q, η)) c :=
  fun q => periodize_add_period c f q η

end Def

section Summable

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **G7, lemma 1.** Absolute convergence of the periodization under a translate bound. -/
theorem summable_norm_periodize {f : ℝ × ℝ → E} {C s c : ℝ} (hs : 1 < s) (hc : c ≠ 0)
    (hf : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    Summable (fun n : ℤ => ‖f (z.1 - n * c, z.2)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hf _)
    ((summable_translate hs hc z.1).mul_left C)

theorem summable_periodize {f : ℝ × ℝ → E} {C s c : ℝ} (hs : 1 < s) (hc : c ≠ 0)
    (hf : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    Summable (fun n : ℤ => f (z.1 - n * c, z.2)) :=
  (summable_norm_periodize hs hc hf z).of_norm

end Summable

/-! ### Smoothness and termwise differentiation -/

/-- The open strip `|q - q₀| < 1`. -/
def strip (q₀ : ℝ) : Set (ℝ × ℝ) := Prod.fst ⁻¹' ball q₀ 1

theorem isOpen_strip (q₀ : ℝ) : IsOpen (strip q₀) := isOpen_ball.preimage continuous_fst

theorem isPreconnected_strip (q₀ : ℝ) : IsPreconnected (strip q₀) :=
  ((convex_ball q₀ 1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)).isPreconnected

theorem mem_strip_self (z : ℝ × ℝ) : z ∈ strip z.1 := by simp [strip]

theorem abs_sub_lt_of_mem_strip {q₀ : ℝ} {y : ℝ × ℝ} (hy : y ∈ strip q₀) : |y.1 - q₀| < 1 := by
  simpa [strip, Real.dist_eq] using hy

section Smooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- From a translate bound on `g`, a summable bound for the translates on a strip. -/
theorem translates_bound_on_strip {g : ℝ × ℝ → F} {C s c : ℝ} (hs : 1 < s) (hc : c ≠ 0)
    (hg : ∀ z, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-s)) (q₀ : ℝ) :
    Summable (fun n : ℤ => C * 2 ^ s * (1 + |q₀ - n * c|) ^ (-s)) ∧
      ∀ (n : ℤ) (y : ℝ × ℝ), y ∈ strip q₀ →
        ‖g (y - shiftVec c n)‖ ≤ C * 2 ^ s * (1 + |q₀ - n * c|) ^ (-s) := by
  have hC : 0 ≤ C := by
    have h := hg 0
    simp only [Prod.fst_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨(summable_translate hs hc q₀).mul_left _, fun n y hy => ?_⟩
  rw [sub_shiftVec]
  refine (hg _).trans ?_
  have := translate_rpow_le_on_strip (by linarith : (0 : ℝ) ≤ s) (abs_sub_lt_of_mem_strip hy)
    (n * c)
  calc C * (1 + |y.1 - n * c|) ^ (-s) ≤ C * (2 ^ s * (1 + |q₀ - n * c|) ^ (-s)) :=
        mul_le_mul_of_nonneg_left this hC
    _ = C * 2 ^ s * (1 + |q₀ - n * c|) ^ (-s) := by ring

/-- Termwise differentiation of a sum of translates, with locally uniform bounds. -/
theorem hasFDerivAt_tsum_translates {g : ℝ × ℝ → F} (hg : Differentiable ℝ g)
    {C₀ C₁ s c : ℝ} (hs : 1 < s) (hc : c ≠ 0)
    (h₀ : ∀ z, ‖g z‖ ≤ C₀ * (1 + |z.1|) ^ (-s))
    (h₁ : ∀ z, ‖fderiv ℝ g z‖ ≤ C₁ * (1 + |z.1|) ^ (-s)) (x : ℝ × ℝ) :
    HasFDerivAt (fun y => ∑' n : ℤ, g (y - shiftVec c n))
      (∑' n : ℤ, fderiv ℝ (fun y => g (y - shiftVec c n)) x) x := by
  obtain ⟨hu, hb⟩ := translates_bound_on_strip hs hc h₁ x.1
  obtain ⟨hu₀, hb₀⟩ := translates_bound_on_strip hs hc h₀ x.1
  refine hasFDerivAt_tsum_of_isPreconnected hu (isOpen_strip x.1) (isPreconnected_strip x.1)
    (fun n y _ => ?_) (fun n y hy => ?_) (mem_strip_self x) ?_ (mem_strip_self x)
  · exact ((hg.comp (differentiable_id.sub_const _)) y).hasFDerivAt
  · rw [fderiv_comp_sub]
    exact hb n y hy
  · exact Summable.of_norm_bounded hu₀ fun n => hb₀ n x (mem_strip_self x)

/-- Continuity of a sum of translates, with locally uniform bounds. -/
theorem continuous_tsum_translates {g : ℝ × ℝ → F} (hg : Continuous g) {C s c : ℝ} (hs : 1 < s)
    (hc : c ≠ 0) (h₀ : ∀ z, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-s)) :
    Continuous (fun y => ∑' n : ℤ, g (y - shiftVec c n)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨hu, hb⟩ := translates_bound_on_strip hs hc h₀ x.1
  have hcont : ContinuousOn (fun y => ∑' n : ℤ, g (y - shiftVec c n)) (strip x.1) :=
    continuousOn_tsum (fun n => (hg.comp (continuous_id.sub continuous_const)).continuousOn) hu
      (fun n y hy => hb n y hy)
  exact hcont.continuousAt ((isOpen_strip x.1).mem_nhds (mem_strip_self x))

variable {f : ℝ × ℝ → F} {s c : ℝ} {N : ℕ∞}

/-- **G7, lemma 3 (B0812 (iv), B0146).** Iterated derivatives commute with periodization:
`D^m (P_c f) = P_c (D^m f)` for `m ≤ N`, when `f` is `C^N` and every derivative of order
`≤ N` obeys a translate bound `C_k (1+|q|)^{-s}`, `s > 1`. -/
theorem iteratedFDeriv_periodize (hs : 1 < s) (hc : c ≠ 0) (hf : ContDiff ℝ N f)
    (hD : ∀ k : ℕ, (k : ℕ∞) ≤ N → ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ C * (1 + |z.1|) ^ (-s))
    {m : ℕ} (hm : (m : ℕ∞) ≤ N) :
    iteratedFDeriv ℝ m (periodize c f) =
      fun x => ∑' n : ℤ, iteratedFDeriv ℝ m f (x - shiftVec c n) := by
  induction m with
  | zero =>
    ext1 x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, periodize_eq]
    exact (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hm
    obtain ⟨C₀, hC₀⟩ := hD k h'k.le
    obtain ⟨C₁, hC₁⟩ := hD (k + 1) hm
    have h₁ : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖ ≤ C₁ * (1 + |z.1|) ^ (-s) := by
      intro z; rw [norm_fderiv_iteratedFDeriv]; exact hC₁ z
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast h'k)
    ext1 x
    rw [iteratedFDeriv_succ_eq_comp_left, IH h'k.le, Function.comp_apply,
      (hasFDerivAt_tsum_translates hdiff hs hc hC₀ h₁ x).fderiv]
    have e1 : ∀ n : ℤ, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × ℝ) F).symm
        (fderiv ℝ (fun y => iteratedFDeriv ℝ k f (y - shiftVec c n)) x) =
        iteratedFDeriv ℝ (k + 1) f (x - shiftVec c n) := by
      intro n
      rw [← iteratedFDeriv_comp_sub' k (shiftVec c n),
        ← iteratedFDeriv_comp_sub (k + 1) (shiftVec c n) x, iteratedFDeriv_succ_eq_comp_left,
        Function.comp_apply]
    simp_rw [← e1]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × ℝ) F).symm
      |>.toContinuousLinearEquiv.map_tsum

/-- **G7, lemma 3 (B0812 (i)).** The periodization of a `C^N` function with translate-bounded
derivatives is `C^N`. -/
theorem contDiff_periodize (hs : 1 < s) (hc : c ≠ 0) (hf : ContDiff ℝ N f)
    (hD : ∀ k : ℕ, (k : ℕ∞) ≤ N → ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ C * (1 + |z.1|) ^ (-s)) :
    ContDiff ℝ N (periodize c f) := by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_periodize hs hc hf hD hm]
    obtain ⟨C, hC⟩ := hD m hm
    exact continuous_tsum_translates (hf.continuous_iteratedFDeriv (by exact_mod_cast hm)) hs hc hC
  · intro m hm
    rw [iteratedFDeriv_periodize hs hc hf hD hm.le]
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hm
    obtain ⟨C₀, hC₀⟩ := hD m hm.le
    obtain ⟨C₁, hC₁⟩ := hD (m + 1) h'm
    have h₁ : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ m f) z‖ ≤ C₁ * (1 + |z.1|) ^ (-s) := by
      intro z; rw [norm_fderiv_iteratedFDeriv]; exact hC₁ z
    intro x
    exact (hasFDerivAt_tsum_translates (hf.differentiable_iteratedFDeriv (by exact_mod_cast hm))
      hs hc hC₀ h₁ x).differentiableAt

end Smooth

/-! ### Gaussian translate bounds: the sup bound -/

section Gauss

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **G7, lemma 6 (sup part; B0147, tex 2217–2234).** If `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}` and
`0 < a ≤ c²`, then `‖P_c f(q,η)‖ ≤ 10 A e^{-η²/(4a)}`, uniformly in `c`, `a` and `q`. -/
theorem norm_periodize_le_of_gauss {f : ℝ × ℝ → E} {A a c : ℝ} (ha : 0 < a) (hac : a ≤ c ^ 2)
    (hf : ∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) (z : ℝ × ℝ) :
    ‖periodize c f z‖ ≤ 10 * A * Real.exp (-z.2 ^ 2 / (4 * a)) := by
  have hA : 0 ≤ A := by
    have h := hf 0
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    norm_num at h
    exact (norm_nonneg _).trans h
  have hsplit : ∀ n : ℤ, A * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * a)) =
      A * Real.exp (-z.2 ^ 2 / (4 * a)) * Real.exp (-(z.1 - n * c) ^ 2 / (4 * a)) := by
    intro n; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hsum := summable_gauss_shift ha hac z.1
  have hmaj : Summable fun n : ℤ => A * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * a)) := by
    simp_rw [hsplit]; exact hsum.mul_left _
  have hnorm : Summable fun n : ℤ => ‖f (z.1 - n * c, z.2)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hf _) hmaj
  unfold periodize
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (hnorm.tsum_le_tsum (fun n => hf _) hmaj).trans ?_
  simp_rw [hsplit]
  rw [tsum_mul_left]
  have h10 := tsum_gauss_shift_le ha hac z.1
  have hpos : 0 ≤ A * Real.exp (-z.2 ^ 2 / (4 * a)) := mul_nonneg hA (Real.exp_pos _).le
  calc A * Real.exp (-z.2 ^ 2 / (4 * a)) * ∑' n : ℤ, Real.exp (-(z.1 - n * c) ^ 2 / (4 * a))
      ≤ A * Real.exp (-z.2 ^ 2 / (4 * a)) * 10 := mul_le_mul_of_nonneg_left h10 hpos
    _ = 10 * A * Real.exp (-z.2 ^ 2 / (4 * a)) := by ring

end Gauss

end UnforcedLeray.Gaussian
