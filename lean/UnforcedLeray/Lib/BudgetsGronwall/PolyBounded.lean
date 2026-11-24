import Mathlib

/-!
# Polynomial budgets in `ν⁻¹` and their absorption (INF29, target T29.1)


§5, Level 4, target T29.1; decision D13 of `scoping/README.md` §3.

The manuscript writes `P_ν` for "a polynomial in `ν⁻¹` (and `c`, and the analytic budgets) whose
degree is fixed before `ε` and the later windows" (B0281 `background:eq:2.1`, tex 5070–5080;
B0549 `eq:stress-setup:3.0`, tex 8701–8720; B0625, tex 11129–11132). Following decision D13
(quantifier order instead of a budget framework), such a bound is the predicate
`PolyBoundedOn S k X`: there are `C` and `ν₀ > 0` with `|X ν p| ≤ C ν^{-k}` for every
`ν ∈ (0, ν₀)` and every parameter `p ∈ S`. The degree `k` is a natural number fixed before `C`
and `ν₀`, and `C, ν₀` do not depend on `ν` or `p`; this is the formal content of "degree fixed
first, uniformly on the parameter set".

When `c = ν^{-ρ}` (B0281) or `c = ν^{-2}` (B0549), a polynomial in `c` and `ν⁻¹` is such a bound
(`polyBoundedOn_rpow_neg`, closure under `add`, `mul`, `pow`).

Absorption (B0682 `background:eq:2.41`, tex 5660–5669; B0822, tex 11999–12019; B0993, B0995,
tex 13507–13606): a `PolyBoundedOn` factor times `e^{-κ/ν}` (`κ > 0`), times `e^{m/ν} e^{-κ/ν}`
(`m < κ`), times the Gaussian seam factor `e^{C/ν - b ν^{-2ρ}}` (`ρ > 1/2`), times the
logarithmic-square tail `e^{-b log² ν}`, or times `e^{-g/√ν}` tends to zero as `ν → 0⁺`,
uniformly on `S` (`PolyBoundedOn.tendsto_mul_exp_neg` and its siblings).

Risk 4 of the scoping note (§6): with `S = ε^{-b}` and `ε = C_* ν^r e^{-d₀/ν}`, the window factor
`(1 + S)^D` is an *exponential* loss `e^{b D d₀/ν}` times a polynomial; it is not itself a
`PolyBoundedOn` quantity. `window_pow_le`, `one_add_rpow_neg_pow_le_lateEps` and
`polyBoundedOn_window_mul_exp` keep the two parts apart.

Junk values. All statements are restricted to `ν ∈ (0, ν₀)`, where `ν⁻¹`, `ν^{-ρ}`, `log ν` and
`e^{-κ/ν}` have their mathematical meaning; nothing is claimed at `ν ≤ 0`. The parameter `ε` of
the window lemmas is assumed positive, so `ε^{-b}` is the genuine real power.
-/

set_option autoImplicit false

open Set Filter Topology

namespace UnforcedLeray.Budget

variable {P : Type*}

/-- **Polynomial bound in `ν⁻¹`, uniform on a parameter set** (INF29 T29.1; B0281, B0549, B0625).
`PolyBoundedOn S k X` holds when there are a constant `C` and a threshold `ν₀ > 0`, chosen
before `ν` and `p`, with `|X ν p| ≤ C ν^{-k}` for every `ν ∈ (0, ν₀)` and every `p ∈ S`. -/
def PolyBoundedOn (S : Set P) (k : ℕ) (X : ℝ → P → ℝ) : Prop :=
  ∃ C ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ p ∈ S, |X ν p| ≤ C * ν⁻¹ ^ k

/-- An eventual statement in `𝓝[>] 0` holds on an interval `(0, ε)`. -/
theorem exists_Ioo_of_eventually {Q : ℝ → Prop} (h : ∀ᶠ ν in 𝓝[>] (0 : ℝ), Q ν) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Ioo 0 ε, Q ν := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun ν hν => hsub hν⟩

/-- For `ν ∈ (0, 1)`, `1 ≤ ν⁻¹`. -/
theorem one_le_inv_of_mem {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : 1 ≤ ν⁻¹ :=
  one_le_inv₀ hν |>.2 hν1

namespace PolyBoundedOn

variable {S S' : Set P} {k k' : ℕ} {X Y : ℝ → P → ℝ}

/-- Normal form: the constant may be taken nonnegative and the threshold at most one. -/
theorem exists_nonneg (h : PolyBoundedOn S k X) :
    ∃ C ν₀ : ℝ, 0 ≤ C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ p ∈ S, |X ν p| ≤ C * ν⁻¹ ^ k := by
  obtain ⟨C, ν₀, hν₀, h⟩ := h
  refine ⟨|C|, min ν₀ 1, abs_nonneg C, lt_min hν₀ one_pos, min_le_right _ _,
    fun ν hν p hp => ?_⟩
  have hν' : ν ∈ Ioo 0 ν₀ := ⟨hν.1, hν.2.trans_le (min_le_left _ _)⟩
  have h0 : 0 < ν := hν.1
  exact (h ν hν' p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

/-- Restriction to a smaller parameter set. -/
theorem mono_set (h : PolyBoundedOn S k X) (hS : S' ⊆ S) : PolyBoundedOn S' k X := by
  obtain ⟨C, ν₀, hν₀, h⟩ := h
  exact ⟨C, ν₀, hν₀, fun ν hν p hp => h ν hν p (hS hp)⟩

/-- Raising the degree. -/
theorem mono (h : PolyBoundedOn S k X) (hk : k ≤ k') : PolyBoundedOn S k' X := by
  obtain ⟨C, ν₀, hC, hν₀, hν₀1, h⟩ := h.exists_nonneg
  refine ⟨C, ν₀, hν₀, fun ν hν p hp => (h ν hν p hp).trans ?_⟩
  have h1 : 1 ≤ ν⁻¹ := one_le_inv_of_mem hν.1 (hν.2.le.trans hν₀1)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) hC

/-- Domination: a quantity eventually below a `PolyBoundedOn` one in absolute value is again
`PolyBoundedOn` of the same degree. -/
theorem of_abs_le (h : PolyBoundedOn S k X)
    (hY : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ∀ p ∈ S, |Y ν p| ≤ |X ν p|) : PolyBoundedOn S k Y := by
  obtain ⟨C, ν₀, hν₀, h⟩ := h
  obtain ⟨ε, hε, hY⟩ := exists_Ioo_of_eventually hY
  refine ⟨C, min ν₀ ε, lt_min hν₀ hε, fun ν hν p hp => ?_⟩
  exact (hY ν ⟨hν.1, hν.2.trans_le (min_le_right _ _)⟩ p hp).trans
    (h ν ⟨hν.1, hν.2.trans_le (min_le_left _ _)⟩ p hp)

/-- Constants have degree zero. -/
theorem const (S : Set P) (K : ℝ) : PolyBoundedOn S 0 (fun _ _ => K) :=
  ⟨|K|, 1, one_pos, fun ν _ p _ => by rw [pow_zero, mul_one]⟩

/-- `ν⁻¹` has degree one. -/
theorem inv (S : Set P) : PolyBoundedOn S 1 (fun ν _ => ν⁻¹) :=
  ⟨1, 1, one_pos, fun ν hν p _ => by
    rw [abs_of_pos (inv_pos.2 hν.1), pow_one, one_mul]⟩

/-- Closure under addition (degree: the maximum). -/
theorem add (hX : PolyBoundedOn S k X) (hY : PolyBoundedOn S k' Y) :
    PolyBoundedOn S (max k k') (fun ν p => X ν p + Y ν p) := by
  obtain ⟨C₁, ν₁, hν₁, h₁⟩ := hX.mono (le_max_left k k')
  obtain ⟨C₂, ν₂, hν₂, h₂⟩ := hY.mono (le_max_right k k')
  refine ⟨C₁ + C₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν p hp => ?_⟩
  have a := h₁ ν ⟨hν.1, hν.2.trans_le (min_le_left _ _)⟩ p hp
  have b := h₂ ν ⟨hν.1, hν.2.trans_le (min_le_right _ _)⟩ p hp
  calc |X ν p + Y ν p| ≤ |X ν p| + |Y ν p| := abs_add_le _ _
    _ ≤ (C₁ + C₂) * ν⁻¹ ^ max k k' := by rw [add_mul]; exact add_le_add a b

/-- Negation. -/
theorem neg (hX : PolyBoundedOn S k X) : PolyBoundedOn S k (fun ν p => -X ν p) := by
  obtain ⟨C, ν₀, hν₀, h⟩ := hX
  exact ⟨C, ν₀, hν₀, fun ν hν p hp => by rw [abs_neg]; exact h ν hν p hp⟩

/-- Closure under subtraction. -/
theorem sub (hX : PolyBoundedOn S k X) (hY : PolyBoundedOn S k' Y) :
    PolyBoundedOn S (max k k') (fun ν p => X ν p - Y ν p) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

/-- Closure under multiplication (degrees add). -/
theorem mul (hX : PolyBoundedOn S k X) (hY : PolyBoundedOn S k' Y) :
    PolyBoundedOn S (k + k') (fun ν p => X ν p * Y ν p) := by
  obtain ⟨C₁, ν₁, hC₁, hν₁, -, h₁⟩ := hX.exists_nonneg
  obtain ⟨C₂, ν₂, hC₂, hν₂, -, h₂⟩ := hY.exists_nonneg
  refine ⟨C₁ * C₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν p hp => ?_⟩
  have a := h₁ ν ⟨hν.1, hν.2.trans_le (min_le_left _ _)⟩ p hp
  have b := h₂ ν ⟨hν.1, hν.2.trans_le (min_le_right _ _)⟩ p hp
  rw [abs_mul, pow_add]
  calc |X ν p| * |Y ν p| ≤ (C₁ * ν⁻¹ ^ k) * (C₂ * ν⁻¹ ^ k') :=
        mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
    _ = C₁ * C₂ * (ν⁻¹ ^ k * ν⁻¹ ^ k') := by ring

/-- Multiplication by a constant does not change the degree. -/
theorem const_mul (hX : PolyBoundedOn S k X) (K : ℝ) :
    PolyBoundedOn S k (fun ν p => K * X ν p) := by
  simpa using (const S K).mul hX

/-- Closure under natural powers (degree `n k`). -/
theorem pow (hX : PolyBoundedOn S k X) (n : ℕ) :
    PolyBoundedOn S (n * k) (fun ν p => X ν p ^ n) := by
  induction n with
  | zero => simpa using const S 1
  | succ n ih =>
    have h := ih.mul hX
    simpa [pow_succ, Nat.succ_mul] using h

/-- Closure under finite sums with a common degree. -/
theorem sum {ι : Type*} (s : Finset ι) {Z : ι → ℝ → P → ℝ}
    (h : ∀ i ∈ s, PolyBoundedOn S k (Z i)) :
    PolyBoundedOn S k (fun ν p => ∑ i ∈ s, Z i ν p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const S 0).mono (Nat.zero_le k)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1.add h2

/-- Closure under finite sums, with degree the largest degree. -/
theorem sum_sup {ι : Type*} (s : Finset ι) {Z : ι → ℝ → P → ℝ} (d : ι → ℕ)
    (h : ∀ i ∈ s, PolyBoundedOn S (d i) (Z i)) :
    PolyBoundedOn S (s.sup d) (fun ν p => ∑ i ∈ s, Z i ν p) :=
  sum s fun i hi => (h i hi).mono (Finset.le_sup hi)

end PolyBoundedOn

/-- `ν^{-ρ}` (for instance `c = ν^{-ρ}` in B0281, tex 5072) has degree `⌈ρ⌉₊`. -/
theorem polyBoundedOn_rpow_neg (S : Set P) (ρ : ℝ) :
    PolyBoundedOn S ⌈ρ⌉₊ (fun ν _ => ν ^ (-ρ)) := by
  refine ⟨1, 1, one_pos, fun ν hν p _ => ?_⟩
  have h0 : 0 < ν := hν.1
  rw [abs_of_pos (Real.rpow_pos_of_pos h0 _), one_mul]
  have h1 : ν ^ (-ρ) ≤ ν ^ (-(⌈ρ⌉₊ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge h0 hν.2.le (by linarith [Nat.le_ceil ρ])
  rwa [Real.rpow_neg h0.le (⌈ρ⌉₊ : ℝ), Real.rpow_natCast, ← inv_pow] at h1

/-- For `0 < ν ≤ 1`, `|log ν| ≤ ν⁻¹`. -/
theorem abs_log_le_inv {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : |Real.log ν| ≤ ν⁻¹ := by
  have h := Real.abs_log_mul_self_lt ν hν hν1
  rw [abs_mul, abs_of_pos hν] at h
  have h' : |Real.log ν| < 1 / ν := (lt_div_iff₀ hν).2 h
  rw [one_div] at h'
  exact h'.le

/-- **The bin count of Lemma 3-6** (tex 10711–10713, B0725): for the late family
`ε = C_* ν^r e^{-d₀/ν}` with `C_*` in a positive compact interval and `r`, `d₀` bounded,
`1 + |log ε|` has degree one, uniformly on the family. -/
theorem polyBoundedOn_one_add_abs_log_lateEps {S : Set P} {Cs r d : P → ℝ} {Cmin Cmax R D : ℝ}
    (hCmin : 0 < Cmin) (hC : ∀ p ∈ S, Cs p ∈ Icc Cmin Cmax) (hr : ∀ p ∈ S, |r p| ≤ R)
    (hd : ∀ p ∈ S, |d p| ≤ D) :
    PolyBoundedOn S 1
      (fun ν p => 1 + |Real.log (Cs p * ν ^ r p * Real.exp (-d p / ν))|) := by
  refine ⟨1 + (|Real.log Cmin| + |Real.log Cmax|) + R + D, 1, one_pos, fun ν hν p hp => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.le
  have hCp : 0 < Cs p := hCmin.trans_le (hC p hp).1
  have hinv : 1 ≤ ν⁻¹ := one_le_inv_of_mem hν0 hν1
  have hlogν : |Real.log ν| ≤ ν⁻¹ := abs_log_le_inv hν0 hν1
  have hR : 0 ≤ R := (abs_nonneg _).trans (hr p hp)
  have hD : 0 ≤ D := (abs_nonneg _).trans (hd p hp)
  have hlog : Real.log (Cs p * ν ^ r p * Real.exp (-d p / ν)) =
      Real.log (Cs p) + r p * Real.log ν + -d p / ν := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hCp.ne'
      (Real.rpow_pos_of_pos hν0 _).ne', Real.log_rpow hν0, Real.log_exp]
  have hlogC : |Real.log (Cs p)| ≤ |Real.log Cmin| + |Real.log Cmax| := by
    have h1 : Real.log Cmin ≤ Real.log (Cs p) := Real.log_le_log hCmin (hC p hp).1
    have h2 : Real.log (Cs p) ≤ Real.log Cmax := Real.log_le_log hCp (hC p hp).2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log Cmin), abs_nonneg (Real.log Cmax)]
    · linarith [le_abs_self (Real.log Cmax), abs_nonneg (Real.log Cmin)]
  have hrl : |r p * Real.log ν| ≤ R * ν⁻¹ := by
    rw [abs_mul]; exact mul_le_mul (hr p hp) hlogν (abs_nonneg _) hR
  have hdl : |-d p / ν| ≤ D * ν⁻¹ := by
    rw [neg_div, abs_neg, abs_div, abs_of_pos hν0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hd p hp) (inv_nonneg.2 hν0.le)
  dsimp only
  rw [hlog, pow_one]
  have htri : |Real.log (Cs p) + r p * Real.log ν + -d p / ν| ≤
      |Real.log (Cs p)| + |r p * Real.log ν| + |-d p / ν| := by
    have e1 := abs_add_le (Real.log (Cs p) + r p * Real.log ν) (-d p / ν)
    have e2 := abs_add_le (Real.log (Cs p)) (r p * Real.log ν)
    linarith
  have hL : 0 ≤ |Real.log Cmin| + |Real.log Cmax| := by positivity
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-! ## Scalar limits as `ν → 0⁺` -/

/-- `ν^{-k} e^{-κ/ν} → 0` as `ν → 0⁺` for `κ > 0`. -/
theorem tendsto_inv_pow_mul_exp_neg (k : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ν : ℝ => ν⁻¹ ^ k * Real.exp (-κ / ν)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) κ hκ).comp
    tendsto_inv_nhdsGT_zero
  refine h.congr fun ν => ?_
  simp only [Function.comp, Real.rpow_natCast, div_eq_mul_inv, neg_mul]

/-- Gaussian seam factor: `ν^{-k} e^{C/ν - b ν^{-2ρ}} → 0` for `ρ > 1/2`, `b > 0`
(B0241, tex 4166–4169; B0822, tex 11999–12019; B0995, tex 13593–13606). -/
theorem tendsto_inv_pow_mul_exp_gauss (k : ℕ) {ρ b C : ℝ} (hρ : 1 / 2 < ρ) (hb : 0 < b) :
    Tendsto (fun ν : ℝ => ν⁻¹ ^ k * Real.exp (C / ν - b * ν ^ (-(2 * ρ)))) (𝓝[>] 0)
      (𝓝 0) := by
  have hexp : 0 < 2 * ρ - 1 := by linarith
  -- the statement in the variable `x = ν⁻¹ → ∞`
  have key : Tendsto (fun x : ℝ => x ^ k * Real.exp (C * x - b * x ^ (2 * ρ))) atTop (𝓝 0) := by
    have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have hev1 : ∀ᶠ x : ℝ in atTop, (C + 1) / b ≤ x ^ (2 * ρ - 1) :=
      (tendsto_rpow_atTop hexp).eventually_ge_atTop _
    have hev2 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [hev2] with x hx
      have : 0 < x := by linarith
      positivity
    · filter_upwards [hev1, hev2] with x h1 h2
      have hx : 0 < x := by linarith
      have hsplit : x ^ (2 * ρ) = x ^ (2 * ρ - 1) * x := by
        rw [← Real.rpow_add_one hx.ne']; ring_nf
      have hbx : C + 1 ≤ b * x ^ (2 * ρ - 1) := by
        rwa [div_le_iff₀ hb, mul_comm] at h1
      have hE : C * x - b * x ^ (2 * ρ) ≤ -x := by
        rw [hsplit]; nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE) (by positivity)
  have h := key.comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hν0 : 0 < ν := hν
  simp only [Function.comp]
  rw [Real.inv_rpow hν0.le, Real.rpow_neg hν0.le, div_eq_mul_inv, mul_comm C]

/-- Logarithmic-square tail: `ν^{-k} e^{-b log² ν} → 0` for `b > 0` (`T_ν = log²(1/ν)`,
B0995, tex 13593–13606). -/
theorem tendsto_inv_pow_mul_exp_neg_logsq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ν : ℝ => ν⁻¹ ^ k * Real.exp (-b * Real.log ν ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have key : Tendsto (fun y : ℝ => Real.exp (k * y - b * y ^ 2)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      Real.tendsto_exp_neg_atTop_nhds_zero (Eventually.of_forall fun y => (Real.exp_pos _).le) ?_
    filter_upwards [eventually_ge_atTop ((k + 1) / b), eventually_ge_atTop (0 : ℝ)] with y h1 h2
    apply Real.exp_le_exp.2
    have : (k : ℝ) + 1 ≤ b * y := by rwa [div_le_iff₀ hb, mul_comm] at h1
    nlinarith
  have hlog : Tendsto (fun ν : ℝ => -Real.log ν) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine (key.comp hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hν0 : 0 < ν := hν
  simp only [Function.comp]
  have h1 : ν⁻¹ ^ k = Real.exp (k * -Real.log ν) := by
    rw [Real.exp_nat_mul, ← Real.log_inv, Real.exp_log (inv_pos.2 hν0)]
  rw [h1, ← Real.exp_add]
  congr 1
  ring

/-- Square-root tail: `ν^{-k} e^{-g/√ν} → 0` for `g > 0` (B0867, tex 13047–13059). -/
theorem tendsto_inv_pow_mul_exp_neg_sqrt (k : ℕ) {g : ℝ} (hg : 0 < g) :
    Tendsto (fun ν : ℝ => ν⁻¹ ^ k * Real.exp (-g / Real.sqrt ν)) (𝓝[>] 0) (𝓝 0) := by
  have key := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * k : ℕ) : ℝ) g hg
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Real.continuous_sqrt.tendsto 0
      rw [Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ν hν
      exact Real.sqrt_pos.2 hν
  refine ((key.comp tendsto_inv_nhdsGT_zero).comp hsqrt).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hν0 : 0 < ν := hν
  simp only [Function.comp, Real.rpow_natCast]
  have hs : ((Real.sqrt ν)⁻¹) ^ (2 * k) = ν⁻¹ ^ k := by
    rw [pow_mul, inv_pow, Real.sq_sqrt hν0.le, inv_pow]
  rw [hs, div_eq_mul_inv, neg_mul]

/-! ## Uniform absorption on the parameter set -/

namespace PolyBoundedOn

variable {S : Set P} {k : ℕ} {X : ℝ → P → ℝ}

/-- **Master absorption lemma.** If `|X| ≤ C ν^{-k}` on `S` and `|Y ν p| ≤ g ν` with
`ν^{-k} g ν → 0`, then `X Y → 0` uniformly on `S` as `ν → 0⁺`. -/
theorem tendstoUniformlyOn_mul (hX : PolyBoundedOn S k X) {Y : ℝ → P → ℝ} {g : ℝ → ℝ}
    (hYg : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ∀ p ∈ S, |Y ν p| ≤ g ν)
    (hg : Tendsto (fun ν => ν⁻¹ ^ k * g ν) (𝓝[>] 0) (𝓝 0)) :
    TendstoUniformlyOn (fun ν p => X ν p * Y ν p) 0 (𝓝[>] 0) S := by
  obtain ⟨C, ν₀, hC, hν₀, -, hX⟩ := hX.exists_nonneg
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  have h1 : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Ioo 0 ν₀ := Ioo_mem_nhdsGT hν₀
  have h2 : ∀ᶠ ν in 𝓝[>] (0 : ℝ), |ν⁻¹ ^ k * g ν| < ε / (C + 1) := by
    have := (Metric.tendsto_nhds.1 hg) (ε / (C + 1)) (div_pos hε hC1)
    simpa [Real.dist_eq] using this
  filter_upwards [h1, h2, hYg] with ν hν h2 hY p hp
  rw [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_mul]
  have hYp := hY p hp
  have hg0 : 0 ≤ g ν := (abs_nonneg _).trans hYp
  have hpos : 0 ≤ ν⁻¹ ^ k := by have := hν.1; positivity
  have hxg : ν⁻¹ ^ k * g ν < ε / (C + 1) := (le_abs_self _).trans_lt h2
  calc |X ν p| * |Y ν p| ≤ (C * ν⁻¹ ^ k) * g ν :=
        mul_le_mul (hX ν hν p hp) hYp (abs_nonneg _) (by positivity)
    _ ≤ (C + 1) * (ν⁻¹ ^ k * g ν) := by nlinarith [mul_nonneg hpos hg0]
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hxg hC1
    _ = ε := by field_simp

/-- `P_ν e^{-κ/ν} → 0` uniformly on `S` for `κ > 0` (B0682, tex 5660–5669; (t00629), (t00630)). -/
theorem tendsto_mul_exp_neg (hX : PolyBoundedOn S k X) {κ : ℝ} (hκ : 0 < κ) :
    TendstoUniformlyOn (fun ν p => X ν p * Real.exp (-κ / ν)) 0 (𝓝[>] 0) S :=
  hX.tendstoUniformlyOn_mul (g := fun ν => Real.exp (-κ / ν))
    (Eventually.of_forall fun _ _ _ => (abs_of_pos (Real.exp_pos _)).le)
    (tendsto_inv_pow_mul_exp_neg k hκ)

/-- `P_ν e^{m/ν} e^{-κ/ν} → 0` uniformly on `S` whenever `m < κ` (B0675, B0678, B0945). -/
theorem tendsto_mul_exp_sub (hX : PolyBoundedOn S k X) {m κ : ℝ} (h : m < κ) :
    TendstoUniformlyOn (fun ν p => X ν p * (Real.exp (m / ν) * Real.exp (-κ / ν))) 0
      (𝓝[>] 0) S :=
  hX.tendstoUniformlyOn_mul (g := fun ν => Real.exp (-(κ - m) / ν))
    (Eventually.of_forall fun _ _ _ => by
      rw [abs_of_pos (by positivity), ← Real.exp_add]
      exact le_of_eq (by congr 1; ring))
    (tendsto_inv_pow_mul_exp_neg k (by linarith))

/-- Gaussian seam: `P_ν e^{C/ν - b ν^{-2ρ}} → 0` uniformly on `S` for `ρ > 1/2`, `b > 0`
(B0241, B0822, B0995). -/
theorem tendsto_mul_exp_gauss (hX : PolyBoundedOn S k X) {ρ b C : ℝ} (hρ : 1 / 2 < ρ)
    (hb : 0 < b) :
    TendstoUniformlyOn (fun ν p => X ν p * Real.exp (C / ν - b * ν ^ (-(2 * ρ)))) 0
      (𝓝[>] 0) S :=
  hX.tendstoUniformlyOn_mul (g := fun ν => Real.exp (C / ν - b * ν ^ (-(2 * ρ))))
    (Eventually.of_forall fun _ _ _ => (abs_of_pos (Real.exp_pos _)).le)
    (tendsto_inv_pow_mul_exp_gauss k hρ hb)

/-- Logarithmic-square tail: `P_ν e^{-b log² ν} → 0` uniformly on `S` for `b > 0` (B0995). -/
theorem tendsto_mul_exp_neg_logsq (hX : PolyBoundedOn S k X) {b : ℝ} (hb : 0 < b) :
    TendstoUniformlyOn (fun ν p => X ν p * Real.exp (-b * Real.log ν ^ 2)) 0 (𝓝[>] 0) S :=
  hX.tendstoUniformlyOn_mul (g := fun ν => Real.exp (-b * Real.log ν ^ 2))
    (Eventually.of_forall fun _ _ _ => (abs_of_pos (Real.exp_pos _)).le)
    (tendsto_inv_pow_mul_exp_neg_logsq k hb)

/-- Square-root tail: `P_ν e^{-g/√ν} → 0` uniformly on `S` for `g > 0` (B0867). -/
theorem tendsto_mul_exp_neg_sqrt (hX : PolyBoundedOn S k X) {g : ℝ} (hg : 0 < g) :
    TendstoUniformlyOn (fun ν p => X ν p * Real.exp (-g / Real.sqrt ν)) 0 (𝓝[>] 0) S :=
  hX.tendstoUniformlyOn_mul (g := fun ν => Real.exp (-g / Real.sqrt ν))
    (Eventually.of_forall fun _ _ _ => (abs_of_pos (Real.exp_pos _)).le)
    (tendsto_inv_pow_mul_exp_neg_sqrt k hg)

/-- Smallness form of absorption: for every `η > 0` there is `ν₁ > 0` with
`|X ν p| e^{-κ/ν} < η` for all `ν ∈ (0, ν₁)` and `p ∈ S`. -/
theorem exists_abs_mul_exp_neg_lt (hX : PolyBoundedOn S k X) {κ : ℝ} (hκ : 0 < κ) {η : ℝ}
    (hη : 0 < η) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioo 0 ν₁, ∀ p ∈ S, |X ν p| * Real.exp (-κ / ν) < η := by
  have h := Metric.tendstoUniformlyOn_iff.1 (hX.tendsto_mul_exp_neg hκ) η hη
  obtain ⟨ν₁, hν₁, h⟩ := exists_Ioo_of_eventually h
  refine ⟨ν₁, hν₁, fun ν hν p hp => ?_⟩
  have := h ν hν p hp
  rwa [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)] at this

end PolyBoundedOn

/-! ## Window factors: an exponential loss plus a polynomial (scoping §6, risk 4) -/

/-- `(1 + ε^{-b})^D ≤ 2^D ε^{-bD}` for `0 < ε ≤ 1`, `b ≥ 0` (B0620 `eq:st18-t00623`,
tex 10723–10736; the source of the `b D_S` terms in (t00625)–(t00626)). -/
theorem window_pow_le {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b) (D : ℕ) :
    (1 + ε ^ (-b)) ^ D ≤ 2 ^ D * ε ^ (-(b * D)) := by
  have h1 : 1 ≤ ε ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have h2 : 1 + ε ^ (-b) ≤ 2 * ε ^ (-b) := by linarith
  calc (1 + ε ^ (-b)) ^ D ≤ (2 * ε ^ (-b)) ^ D := pow_le_pow_left₀ (by positivity) h2 D
    _ = 2 ^ D * ε ^ (-(b * D)) := by
        rw [mul_pow, ← Real.rpow_natCast (ε ^ (-b)), ← Real.rpow_mul hε.le, neg_mul]

/-- `(1 + S)^D ≤ 2^D (1 + S^D)` for `S ≥ 0`. -/
theorem one_add_pow_le (D : ℕ) {S : ℝ} (hS : 0 ≤ S) : (1 + S) ^ D ≤ 2 ^ D * (1 + S ^ D) := by
  rcases le_total S 1 with h | h
  · calc (1 + S) ^ D ≤ 2 ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
      _ ≤ 2 ^ D * (1 + S ^ D) := by
          have : 0 ≤ S ^ D := pow_nonneg hS D
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) D]
  · calc (1 + S) ^ D ≤ (2 * S) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
      _ = 2 ^ D * S ^ D := mul_pow _ _ _
      _ ≤ 2 ^ D * (1 + S ^ D) := by
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) D]

/-- The late ring scale `ε = C_* ν^r e^{-d₀/ν}` (B0549, tex 8701–8720; B0726, tex 10778–10815). -/
noncomputable def lateEps (Cs r d₀ ν : ℝ) : ℝ := Cs * ν ^ r * Real.exp (-d₀ / ν)

theorem lateEps_pos {Cs r d₀ ν : ℝ} (hCs : 0 < Cs) (hν : 0 < ν) : 0 < lateEps Cs r d₀ ν := by
  unfold lateEps; positivity

/-- `ε^{-y} = C_*^{-y} ν^{-r y} e^{y d₀/ν}` for the late ring scale. -/
theorem lateEps_rpow_neg {Cs r d₀ ν : ℝ} (hCs : 0 < Cs) (hν : 0 < ν) (y : ℝ) :
    lateEps Cs r d₀ ν ^ (-y) = Cs ^ (-y) * ν ^ (-(r * y)) * Real.exp (y * d₀ / ν) := by
  unfold lateEps
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, Real.mul_rpow hCs.le (by positivity),
    ← Real.rpow_mul hν.le, ← Real.exp_mul]
  congr 2
  · ring_nf
  · ring

/-- **The window factor** (scoping §6, risk 4): with `S = ε^{-b}` and `ε = C_* ν^r e^{-d₀/ν}`,
`(1 + S)^D ≤ 2^D (1 + C_*^{-bD} ν^{-rbD} e^{bDd₀/ν})`: an exponential loss `b D d₀/ν` plus a
polynomial. No smallness of `ε` is assumed. -/
theorem one_add_rpow_neg_pow_le_lateEps {Cs r d₀ ν b : ℝ} (hCs : 0 < Cs) (hν : 0 < ν)
    (D : ℕ) :
    (1 + lateEps Cs r d₀ ν ^ (-b)) ^ D ≤
      2 ^ D * (1 + Cs ^ (-(b * D)) * ν ^ (-(r * (b * D))) * Real.exp (b * D * d₀ / ν)) := by
  have hε := lateEps_pos (r := r) (d₀ := d₀) hCs hν
  have h := one_add_pow_le D (Real.rpow_nonneg hε.le (-b))
  have hpow : (lateEps Cs r d₀ ν ^ (-b)) ^ D = lateEps Cs r d₀ ν ^ (-(b * D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, neg_mul]
  rw [hpow, lateEps_rpow_neg hCs hν (b * D)] at h
  exact h

/-- **Window factor with its exponential loss removed is a viscosity polynomial**, uniformly
for `C_* ∈ [Cmin, Cmax]` with `Cmin > 0`, `|r| ≤ R`, `d₀ ≥ 0`, `b ≥ 0`: the function
`(1 + ε^{-b})^D e^{-bDd₀/ν}` has degree `⌈R b D⌉₊`. -/
theorem polyBoundedOn_window_mul_exp {S : Set P} {Cs r : P → ℝ} {Cmin Cmax R d₀ b : ℝ}
    (hCmin : 0 < Cmin) (hC : ∀ p ∈ S, Cs p ∈ Icc Cmin Cmax) (hr : ∀ p ∈ S, |r p| ≤ R)
    (hd₀ : 0 ≤ d₀) (hb : 0 ≤ b) (D : ℕ) :
    PolyBoundedOn S ⌈R * b * D⌉₊
      (fun ν p => (1 + lateEps (Cs p) (r p) d₀ ν ^ (-b)) ^ D *
        Real.exp (-(b * D * d₀) / ν)) := by
  refine ⟨2 ^ D * (1 + Cmin ^ (-(b * D))), 1, one_pos, fun ν hν p hp => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.le
  have hCp : 0 < Cs p := hCmin.trans_le (hC p hp).1
  have hR : 0 ≤ R := (abs_nonneg _).trans (hr p hp)
  have hbD : 0 ≤ b * D := mul_nonneg hb (Nat.cast_nonneg D)
  have hn : 1 ≤ ν⁻¹ ^ ⌈R * b * D⌉₊ := one_le_pow₀ (one_le_inv_of_mem hν0 hν1)
  -- the three factors of the polynomial part
  have hCpow : Cs p ^ (-(b * D)) ≤ Cmin ^ (-(b * D)) := by
    rw [Real.rpow_neg hCp.le, Real.rpow_neg hCmin.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hCmin _)
      (Real.rpow_le_rpow hCmin.le (hC p hp).1 hbD)
  have hνpow : ν ^ (-(r p * (b * D))) ≤ ν⁻¹ ^ ⌈R * b * D⌉₊ := by
    have h1 : ν ^ (-(r p * (b * D))) ≤ ν ^ (-((⌈R * b * D⌉₊ : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hν0 hν1
      have : r p * (b * D) ≤ R * b * D := by
        have := mul_le_mul_of_nonneg_right ((le_abs_self (r p)).trans (hr p hp)) hbD
        linarith
      linarith [Nat.le_ceil (R * b * D)]
    rwa [Real.rpow_neg hν0.le ((⌈R * b * D⌉₊ : ℕ) : ℝ), Real.rpow_natCast, ← inv_pow] at h1
  have hexp : Real.exp (-(b * D * d₀) / ν) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hν0.le
  have hexp_cancel : Real.exp (b * D * d₀ / ν) * Real.exp (-(b * D * d₀) / ν) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  have hmain := one_add_rpow_neg_pow_le_lateEps (r := r p) (d₀ := d₀) (b := b) hCp hν0 D
  have hε := lateEps_pos (r := r p) (d₀ := d₀) hCp hν0
  have hlhs0 : 0 ≤ (1 + lateEps (Cs p) (r p) d₀ ν ^ (-b)) ^ D *
      Real.exp (-(b * D * d₀) / ν) := by positivity
  rw [abs_of_nonneg hlhs0]
  have hE0 : 0 < Real.exp (-(b * D * d₀) / ν) := Real.exp_pos _
  calc (1 + lateEps (Cs p) (r p) d₀ ν ^ (-b)) ^ D * Real.exp (-(b * D * d₀) / ν)
      ≤ 2 ^ D * (1 + Cs p ^ (-(b * D)) * ν ^ (-(r p * (b * D))) *
          Real.exp (b * D * d₀ / ν)) * Real.exp (-(b * D * d₀) / ν) :=
        mul_le_mul_of_nonneg_right hmain hE0.le
    _ = 2 ^ D * (Real.exp (-(b * D * d₀) / ν) + Cs p ^ (-(b * D)) * ν ^ (-(r p * (b * D))) *
          (Real.exp (b * D * d₀ / ν) * Real.exp (-(b * D * d₀) / ν))) := by ring
    _ = 2 ^ D * (Real.exp (-(b * D * d₀) / ν) + Cs p ^ (-(b * D)) *
          ν ^ (-(r p * (b * D)))) := by rw [hexp_cancel, mul_one]
    _ ≤ 2 ^ D * (1 * ν⁻¹ ^ ⌈R * b * D⌉₊ + Cmin ^ (-(b * D)) * ν⁻¹ ^ ⌈R * b * D⌉₊) := by
        gcongr
        · linarith
    _ = 2 ^ D * (1 + Cmin ^ (-(b * D))) * ν⁻¹ ^ ⌈R * b * D⌉₊ := by ring

end UnforcedLeray.Budget
