import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.SqrtLift
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets

/-!
# All-order inverse-distance decay of the inlet columns (helper for `PartII-b:S2/3`)

Source of record: `the November 2 reference manuscript`, lines 2543-2551 (the inlet
source in the large-radius region; "The inlet cutoff vanishes near the axis"), 2607-2608.

`E_i(τ) = N_v(ringStreamProfile R φ_i)`, `φ_i = χ(s)ψ_i` (`Params.inlet`, `Params.inletProfile`).
The jets of `φ_i` of every order are bounded by `C e^{-κ|η|/c}` (`cutStreamJets`) and vanish for
`s > H/2` (`ageCutoff_eq_zero`).  On `s ≤ H`, `nvDecayFar` gives
`(1+|y|)|D^kE_i| ≤ C (1+|η|)^{k+2} e^{-κ|η|/c} ≤ C'`; on `s > H` all jets of `φ_i` vanish at the
chart point.  No smallness of `ν` beyond `c ≥ 1` is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RawAndInletL4

open UnforcedLeray UnforcedLeray.Short.IIb

/-- `(1+t)^n e^{-at} ≤ M` for `t ≥ 0`. -/
theorem pow_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ n * Real.exp (-(a * t)) ≤ M := by
  set m : ℝ := max 1 ((n + 1) / a) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm2 : (n + 1) / a ≤ m := le_max_right _ _
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hma : (n + 1 : ℝ) ≤ m * a := by
    have := (div_le_iff₀ ha).1 hm2
    linarith
  refine ⟨m ^ n, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ m * (1 + a * t / (n + 1)) := by
    have e : m * (1 + a * t / (n + 1)) = m + (m * a) * t / (n + 1) := by ring
    rw [e]
    have : t ≤ (m * a) * t / (n + 1) := by
      rw [le_div_iff₀ hn1]
      nlinarith
    linarith
  have h2 : 1 + a * t / (n + 1) ≤ Real.exp (a * t / (n + 1)) := by
    have := Real.add_one_le_exp (a * t / (n + 1))
    linarith
  have h3 : 1 + t ≤ m * Real.exp (a * t / (n + 1)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  have h4 : (1 + t) ^ n ≤ m ^ n * Real.exp (a * t) := by
    calc (1 + t) ^ n ≤ (m * Real.exp (a * t / (n + 1))) ^ n :=
          pow_le_pow_left₀ (by linarith) h3 n
      _ = m ^ n * Real.exp (n * (a * t / (n + 1))) := by
          rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ m ^ n * Real.exp (a * t) := by
          have hat : 0 ≤ a * t := by positivity
          have hle : (n : ℝ) * (a * t / (n + 1)) ≤ a * t := by
            rw [mul_div_assoc', div_le_iff₀ hn1]
            nlinarith
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by positivity)
  calc (1 + t) ^ n * Real.exp (-(a * t)) ≤ m ^ n * Real.exp (a * t) * Real.exp (-(a * t)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = m ^ n := by rw [mul_assoc, ← Real.exp_add]; simp

/-- A function vanishing near `x` has vanishing jets at `x`. -/
theorem iteratedFDeriv_eq_zero_of_eventually {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] fun _ => 0) (n : ℕ) : iteratedFDeriv ℝ n f x = 0 := by
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
  exact congrFun iteratedFDeriv_zero x

/-- **All-order inverse-distance decay of the inlet columns** (source 2543-2551, 2607-2608):
for a growing eigenpair `(λ, q)` and every order `k`, every parameter point with `p.mode = q`,
`1 ≤ c` and `1 ≤ R` has a constant `B` with `(1+|y|) ‖D^k E_i(τ, y)‖ ≤ B` off the axis, for all
`τ` and `i`. -/
theorem inletDecayAll (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile)
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) (k : ℕ)
    (p : UnforcedLeray.Cons.C03.Concrete.Params) (hmode : p.mode = q) (hc : 1 ≤ p.c)
    (hR : 1 ≤ p.R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : Fin 2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
      (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (p.inlet i τ) y‖ ≤ B := by
  obtain ⟨C3, κ, N, hC3, hκ, h3⟩ := cutStreamJets lam q hq (k + 1)
  obtain ⟨C, K, hC0, Hf⟩ := nvDecayFar k
  have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc
  have hH : 0 < p.H := p.H_pos
  obtain ⟨M, hM0, hM⟩ := pow_mul_exp_le (div_pos hκ hc0) (k + 2)
  set A : ℝ := C3 * (1 + p.H⁻¹) ^ (k + 1) * p.c ^ N with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨C * (1 + p.H + p.R) ^ (K + 2) * ((k + 2) * (A * M)), by positivity, ?_⟩
  intro i τ y hy
  obtain ⟨hsm, hjet⟩ := h3 p hmode hc hH i
  have hΦ : ContDiffOn ℝ ∞ (p.cutStream i) (Ioi 0 ×ˢ univ) := hsm.contDiffOn
  have hinl : p.inlet i τ = Axi.Nv p.R (Axi.ringStreamProfile p.R (p.cutStream i)) τ := rfl
  rw [hinl]
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR
  have hs : 0 < Axi.age p.R y := PartIIIb.Concrete.age_pos_of hR0 hy
  set η := |Axi.trans p.R y| with hη
  have hη0 : 0 ≤ η := abs_nonneg _
  have hB0 : 0 ≤ C * (1 + p.H + p.R) ^ (K + 2) * ((k + 2) * (A * M)) := by positivity
  by_cases hsH : Axi.age p.R y ≤ p.H
  · have h1 := Hf p.R p.H (p.cutStream i) hR hH.le hΦ τ y hy hsH
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    have hterm : ∀ l ∈ Finset.range (k + 2),
        (1 + η) ^ (k + 2) * ‖iteratedFDeriv ℝ l (p.cutStream i) (Axi.chart p.R τ y)‖ ≤ A * M := by
      intro l hl
      have hl' : l ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.1 hl)
      have hb := hjet l hl' (Axi.chart p.R τ y)
      have hchart : |(Axi.chart p.R τ y).2.2| = η := rfl
      rw [hchart] at hb
      have hexp : Real.exp (-(κ * η / p.c)) = Real.exp (-(κ / p.c * η)) := by
        congr 1; ring
      rw [hexp] at hb
      calc (1 + η) ^ (k + 2) * ‖iteratedFDeriv ℝ l (p.cutStream i) (Axi.chart p.R τ y)‖
          ≤ (1 + η) ^ (k + 2) * (A * Real.exp (-(κ / p.c * η))) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = A * ((1 + η) ^ (k + 2) * Real.exp (-(κ / p.c * η))) := by ring
        _ ≤ A * M := mul_le_mul_of_nonneg_left (hM η hη0) hA0
    calc ∑ l ∈ Finset.range (k + 2),
          (1 + η) ^ (k + 2) * ‖iteratedFDeriv ℝ l (p.cutStream i) (Axi.chart p.R τ y)‖
        ≤ ∑ l ∈ Finset.range (k + 2), A * M := Finset.sum_le_sum hterm
      _ = (k + 2) * (A * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  · push Not at hsH
    have hzero : ∀ l : ℕ, iteratedFDeriv ℝ l (p.cutStream i) (Axi.chart p.R τ y) = 0 := by
      intro l
      apply iteratedFDeriv_eq_zero_of_eventually
      have hopen : IsOpen {m : ℝ × (ℝ × ℝ) | p.H / 2 < m.1} :=
        isOpen_lt continuous_const continuous_fst
      have hmem : Axi.chart p.R τ y ∈ {m : ℝ × (ℝ × ℝ) | p.H / 2 < m.1} := by
        show p.H / 2 < Axi.age p.R y
        linarith
      filter_upwards [hopen.mem_nhds hmem] with m hm
      have hm' : p.H / 2 ≤ m.1 := le_of_lt hm
      show UnforcedLeray.Cons.C03.Concrete.ageCutoff p.H m.1 * p.frozenStream i m.2 = 0
      rw [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hm', zero_mul]
    have h1 := Hf p.R (Axi.age p.R y) (p.cutStream i) hR hs.le hΦ τ y hy le_rfl
    have hsum : ∑ l ∈ Finset.range (k + 2),
        ‖iteratedFDeriv ℝ l (p.cutStream i) (Axi.chart p.R τ y)‖ = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hzero l, norm_zero]
    rw [hsum, mul_zero, mul_zero] at h1
    exact h1.trans hB0

end UnforcedLeray.Short.IIb.RawAndInletL4
