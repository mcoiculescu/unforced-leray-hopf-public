import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Periodic partition of unity on `ℝ` (helper for `FlatEqCellStream`, task `PartII-b:T11/1`)

For `c > 0` there is a smooth compactly supported `θ : ℝ → ℝ`, supported in `(-c, c)`, with
`∑ₙ θ(q - n c) = 1` for every `q` (each sum is finite locally), and with every derivative of order
`≥ 1` having zero periodization. Construction: `θ = χ / P`, where `χ` is a bump on `(-c, c)` and
`P(q) = ∑ₙ χ(q - n c) > 0` is `c`-periodic and smooth.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.CellPart

/-- The `c`-periodization `q ↦ ∑ₙ f(q - n c)` of a function on the line. -/
def per (c : ℝ) (f : ℝ → ℝ) (q : ℝ) : ℝ := ∑' n : ℤ, f (q - n * c)

/-- Integers `n` with `|n| c < M` lie in a fixed finite window. -/
theorem mem_window {c M : ℝ} (hc : 0 < c) {n : ℤ} (h : |(n : ℝ)| * c < M) :
    n ∈ Finset.Icc (-⌈M / c⌉) ⌈M / c⌉ := by
  have h1 : |(n : ℝ)| < M / c := by
    rw [lt_div_iff₀ hc]; exact h
  have h2 : M / c ≤ ((⌈M / c⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h3 : |(n : ℝ)| < ((⌈M / c⌉ : ℤ) : ℝ) := lt_of_lt_of_le h1 h2
  have h4 : (n : ℝ) < ((⌈M / c⌉ : ℤ) : ℝ) := lt_of_le_of_lt (le_abs_self _) h3
  have h5 : -(n : ℝ) < ((⌈M / c⌉ : ℤ) : ℝ) := lt_of_le_of_lt (neg_le_abs _) h3
  have h4' : n < ⌈M / c⌉ := by exact_mod_cast h4
  have h5' : -n < ⌈M / c⌉ := by exact_mod_cast h5
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- Off the window `[-N, N]`, `N = ⌈(|q₀| + 3c)/c⌉`, the terms `f(q - n c)` vanish when `|q - q₀| ≤ c`. -/
theorem term_zero_of_not_mem {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : ∀ x, f x ≠ 0 → |x| ≤ c)
    {q₀ q : ℝ} (hq : |q - q₀| ≤ c) {n : ℤ}
    (hn : n ∉ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉) :
    f (q - n * c) = 0 := by
  by_contra hne
  have h1 : |q - n * c| ≤ c := hf _ hne
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  obtain ⟨h2a, h2b⟩ := abs_le.mp h1
  have hA : |q| ≤ |q₀| + c := by
    rw [abs_le]; constructor <;> linarith [le_abs_self q₀, neg_abs_le q₀]
  have hB : |(n : ℝ) * c| ≤ |q| + c := by
    rw [abs_le]; constructor <;> linarith [le_abs_self q, neg_abs_le q]
  have hC : |(n : ℝ)| * c < |q₀| + 3 * c := by
    have : |(n : ℝ) * c| = |(n : ℝ)| * c := by rw [abs_mul, abs_of_pos hc]
    linarith [le_abs_self q₀, neg_abs_le q₀]
  exact hn (mem_window hc hC)

/-- For `f` supported in `[-c, c]`, the periodization is a finite sum near every point. -/
theorem hasSum_per {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : ∀ x, f x ≠ 0 → |x| ≤ c) (q : ℝ) :
    HasSum (fun n : ℤ => f (q - n * c)) (per c f q) := by
  have hz : ∀ n ∉ Finset.Icc (-⌈(|q| + 3 * c) / c⌉) ⌈(|q| + 3 * c) / c⌉,
      f (q - n * c) = 0 := fun n hn =>
    term_zero_of_not_mem hc hf (q₀ := q) (q := q) (by rw [sub_self, abs_zero]; exact hc.le) hn
  have hper : per c f q =
      ∑ n ∈ Finset.Icc (-⌈(|q| + 3 * c) / c⌉) ⌈(|q| + 3 * c) / c⌉, f (q - n * c) :=
    tsum_eq_sum hz
  rw [hper]
  exact hasSum_sum_of_ne_finset_zero hz

/-- A smooth bump supported in `(-c, c)`. -/
def bump (c : ℝ) (hc : 0 < c) : ContDiffBump (0 : ℝ) :=
  { rIn := c / 2, rOut := c, rIn_pos := by linarith, rIn_lt_rOut := by linarith }

/-- The bump function `χ` on `ℝ`. -/
def chi (c : ℝ) (hc : 0 < c) : ℝ → ℝ := fun x => bump c hc x

theorem chi_contDiff (c : ℝ) (hc : 0 < c) : ContDiff ℝ ∞ (chi c hc) :=
  (bump c hc).contDiff

theorem chi_hasCompactSupport (c : ℝ) (hc : 0 < c) : HasCompactSupport (chi c hc) :=
  (bump c hc).hasCompactSupport

theorem chi_nonneg (c : ℝ) (hc : 0 < c) (x : ℝ) : 0 ≤ chi c hc x :=
  (bump c hc).nonneg

theorem chi_ne_imp {c : ℝ} (hc : 0 < c) (x : ℝ) (hx : chi c hc x ≠ 0) : |x| < c := by
  have hm : x ∈ Function.support (bump c hc) := hx
  rw [ContDiffBump.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hm
  exact hm

theorem chi_pos {c : ℝ} (hc : 0 < c) (x : ℝ) (hx : |x| < c) : 0 < chi c hc x := by
  apply (bump c hc).pos_of_mem_ball
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  exact hx

/-- The periodization of the bump is smooth. -/
theorem per_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (per c (chi c hc)) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  have hfin : ContDiff ℝ ∞ (fun q => ∑ n ∈ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉,
      chi c hc (q - n * c)) :=
    ContDiff.sum fun n _ => (chi_contDiff c hc).comp (contDiff_id.sub contDiff_const)
  apply hfin.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds q₀ hc] with q hq
  have hq' : |q - q₀| ≤ c := by
    rw [Metric.mem_ball, Real.dist_eq] at hq; exact hq.le
  unfold per
  apply tsum_eq_sum
  intro n hn
  exact term_zero_of_not_mem hc (fun x hx => (chi_ne_imp hc x hx).le) hq' hn

/-- The periodization of the bump is positive. -/
theorem per_pos {c : ℝ} (hc : 0 < c) (q : ℝ) : 0 < per c (chi c hc) q := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊q / c + 1 / 2⌋ := ⟨_, rfl⟩
  have h1 : (n : ℝ) ≤ q / c + 1 / 2 := by rw [hn]; exact Int.floor_le _
  have h2 : q / c + 1 / 2 < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hq : q / c * c = q := div_mul_cancel₀ q hc.ne'
  have e1 : (q / c + 1 / 2) * c = q + c / 2 := by rw [add_mul, hq]; ring
  have e2 : ((n : ℝ) + 1) * c = (n : ℝ) * c + c := by ring
  have k1 := mul_le_mul_of_nonneg_right h1 hc.le
  have k2 := mul_lt_mul_of_pos_right h2 hc
  have hlt : |q - n * c| < c := by
    rw [abs_lt]; constructor <;> linarith
  have hs := hasSum_per hc (f := chi c hc) (fun x hx => (chi_ne_imp hc x hx).le) q
  have hpos : 0 < chi c hc (q - n * c) := chi_pos hc _ hlt
  have hle : chi c hc (q - n * c) ≤ per c (chi c hc) q :=
    le_hasSum hs n (fun j _ => chi_nonneg c hc _)
  linarith

/-- Periodization is invariant under integer shifts. -/
theorem per_sub_int {c : ℝ} (f : ℝ → ℝ) (q : ℝ) (k : ℤ) :
    per c f (q - k * c) = per c f q := by
  unfold per
  refine (tsum_congr fun n => ?_).trans ((Equiv.addLeft k).tsum_eq (fun m : ℤ => f (q - m * c)))
  congr 1
  simp only [Equiv.coe_addLeft, Int.cast_add]
  ring

/-- The normalized bump `θ = χ / P`. -/
def theta (c : ℝ) (hc : 0 < c) : ℝ → ℝ := fun x => chi c hc x * (per c (chi c hc) x)⁻¹

theorem theta_hasSum (c : ℝ) (hc : 0 < c) (q : ℝ) :
    HasSum (fun n : ℤ => theta c hc (q - n * c)) 1 := by
  have h := (hasSum_per hc (f := chi c hc) (fun x hx => (chi_ne_imp hc x hx).le) q).mul_right
    (per c (chi c hc) q)⁻¹
  rw [mul_inv_cancel₀ (per_pos hc q).ne'] at h
  have e : (fun n : ℤ => theta c hc (q - n * c)) =
      fun n : ℤ => chi c hc (q - n * c) * (per c (chi c hc) q)⁻¹ := by
    funext n
    simp only [theta]
    rw [per_sub_int (chi c hc) q n]
  rw [e]
  exact h

theorem theta_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (theta c hc) :=
  (chi_contDiff c hc).mul ((per_contDiff hc).inv fun x => (per_pos hc x).ne')

theorem theta_hasCompactSupport {c : ℝ} (hc : 0 < c) : HasCompactSupport (theta c hc) := by
  have h : HasCompactSupport (chi c hc * fun x => (per c (chi c hc) x)⁻¹) :=
    (chi_hasCompactSupport c hc).mul_right
  exact h

theorem theta_supp {c : ℝ} (hc : 0 < c) (x : ℝ) (hx : theta c hc x ≠ 0) : |x| < c :=
  chi_ne_imp hc x (fun h => hx (by simp [theta, h]))

/-- A support bound `|x| ≤ c` passes to the derivative. -/
theorem supp_deriv {c : ℝ} {g : ℝ → ℝ} (hg : ∀ x, g x ≠ 0 → |x| ≤ c) :
    ∀ x, deriv g x ≠ 0 → |x| ≤ c := by
  intro x hx
  have hsub : tsupport g ⊆ Metric.closedBall (0 : ℝ) c := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hg y hy
  have h1 : x ∈ tsupport (deriv g) := subset_tsupport _ hx
  have h2 := hsub (tsupport_deriv_subset h1)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
  exact h2

/-- Derivative of a periodization: termwise differentiation on a finite window. -/
theorem hasDerivAt_per {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hfd : ContDiff ℝ 1 f)
    (hf : ∀ x, f x ≠ 0 → |x| ≤ c) (hdf : ∀ x, deriv f x ≠ 0 → |x| ≤ c) (q₀ : ℝ) :
    HasDerivAt (per c f) (per c (deriv f) q₀) q₀ := by
  have hsum : HasDerivAt
      (fun q => ∑ n ∈ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉, f (q - n * c))
      (∑ n ∈ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉, deriv f (q₀ - n * c)) q₀ := by
    apply HasDerivAt.fun_sum
    intro n _
    have hd : DifferentiableAt ℝ f (q₀ - n * c) :=
      (hfd.differentiable (by norm_num)).differentiableAt
    exact hd.hasDerivAt.comp_sub_const q₀ (n * c)
  have heq : per c f =ᶠ[𝓝 q₀] (fun q =>
      ∑ n ∈ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉, f (q - n * c)) := by
    filter_upwards [Metric.ball_mem_nhds q₀ hc] with q hq
    have hq' : |q - q₀| ≤ c := by
      rw [Metric.mem_ball, Real.dist_eq] at hq; exact hq.le
    unfold per
    apply tsum_eq_sum
    intro n hn
    exact term_zero_of_not_mem hc hf hq' hn
  have hder : per c (deriv f) q₀ =
      ∑ n ∈ Finset.Icc (-⌈(|q₀| + 3 * c) / c⌉) ⌈(|q₀| + 3 * c) / c⌉, deriv f (q₀ - n * c) := by
    unfold per
    apply tsum_eq_sum
    intro n hn
    exact term_zero_of_not_mem hc hdf (q₀ := q₀) (q := q₀)
      (by rw [sub_self, abs_zero]; exact hc.le) hn
  rw [hder]
  exact hsum.congr_of_eventuallyEq heq

/-- Support bound for all iterated derivatives. -/
theorem iter_supp {c : ℝ} {θ : ℝ → ℝ} (hs : ∀ x, θ x ≠ 0 → |x| ≤ c) :
    ∀ k : ℕ, ∀ x, deriv^[k] θ x ≠ 0 → |x| ≤ c := by
  intro k
  induction k with
  | zero => intro x hx; exact hs x hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact supp_deriv ih

/-- Vanishing of the periodized higher derivatives of a periodic partition. -/
theorem iter_deriv_zero {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hs : ∀ x, θ x ≠ 0 → |x| ≤ c) (hper : ∀ q, per c θ q = 1) :
    ∀ k : ℕ, ∀ q : ℝ, per c (deriv^[k + 1] θ) q = 0 := by
  intro k
  induction k with
  | zero =>
    intro q
    have hd := hasDerivAt_per hc (f := θ) (hθ.of_le (by norm_num)) hs (supp_deriv hs) q
    have hfun : per c θ = fun _ => (1 : ℝ) := funext hper
    rw [hfun] at hd
    have h0 := hd.unique (hasDerivAt_const q (1 : ℝ))
    rw [zero_add, Function.iterate_one]
    exact h0
  | succ k ih =>
    intro q
    have hg : ContDiff ℝ 1 (deriv^[k + 1] θ) :=
      (ContDiff.iterate_deriv (k + 1) hθ).of_le (by norm_num)
    have hd := hasDerivAt_per hc hg (iter_supp hs (k + 1)) (supp_deriv (iter_supp hs (k + 1))) q
    have hfun : per c (deriv^[k + 1] θ) = fun _ => (0 : ℝ) := funext ih
    rw [hfun] at hd
    have h0 := hd.unique (hasDerivAt_const q (0 : ℝ))
    rw [Function.iterate_succ_apply']
    exact h0

/-- **Periodic partition of unity with vanishing periodized derivatives.** For `c > 0` there is
`θ ∈ C_c^∞(ℝ)` supported in `(-c, c)` with `∑ₙ θ(q - n c) = 1` and `∑ₙ θ^{(k)}(q - n c) = 0`
for every `k ≥ 1`. -/
theorem exists_partition_of_derivs {c : ℝ} (hc : 0 < c) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ (∀ x, θ x ≠ 0 → |x| < c) ∧
      (∀ q : ℝ, HasSum (fun n : ℤ => θ (q - n * c)) 1) ∧
      (∀ k : ℕ, ∀ q : ℝ, HasSum (fun n : ℤ => iteratedDeriv (k + 1) θ (q - n * c)) 0) := by
  have hs : ∀ x, theta c hc x ≠ 0 → |x| ≤ c := fun x hx => (theta_supp hc x hx).le
  have hper1 : ∀ q, per c (theta c hc) q = 1 := fun q => (theta_hasSum c hc q).tsum_eq
  refine ⟨theta c hc, theta_contDiff hc, theta_hasCompactSupport hc, theta_supp hc,
    theta_hasSum c hc, ?_⟩
  intro k q
  rw [iteratedDeriv_eq_iterate]
  have hh := hasSum_per hc (iter_supp hs (k + 1)) q
  rw [iter_deriv_zero hc (theta_contDiff hc) hs hper1 k q] at hh
  exact hh

end UnforcedLeray.Short.IIb.CellPart
