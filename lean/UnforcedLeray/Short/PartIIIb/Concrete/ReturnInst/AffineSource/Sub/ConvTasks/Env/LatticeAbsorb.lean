import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import UnforcedLeray.Lib.Gaussian.LatticeSum

/-!
# `LatticeAbsorb`: the polynomial weight is absorbed into the lattice degree
(source 5040-5044): `(1+|η|)^M Σ_j W_N(x - jc) ≤ Σ_j W_{N+M}(x - jc)` for `α > 0`, `c ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1+|u|)^N e^{-β u²}` is bounded in `u` (for `β > 0`). -/
private lemma polyGaussBdd (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, ∀ u : ℝ, (1 + |u|) ^ N * Real.exp (-β * u ^ 2) ≤ K := by
  obtain ⟨C, hC, hCb⟩ := UnforcedLeray.Gaussian.pow_mul_exp_neg_half_le N
  refine ⟨Real.exp β * (C / β ^ N), fun u => ?_⟩
  set y : ℝ := 1 + |u| with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [abs_nonneg u]
  have hexp : Real.exp (-β * u ^ 2) ≤ Real.exp β * Real.exp (-(β * y ^ 2) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hy]
    nlinarith [mul_nonneg hβ.le (sq_nonneg (|u| - 1)), abs_nonneg u, sq_abs u]
  have hpow : (1 + |u|) ^ N ≤ y ^ (2 * N) :=
    pow_le_pow_right₀ hy1 (by omega)
  have hx0 : 0 ≤ β * y ^ 2 := by positivity
  have hH := hCb (β * y ^ 2) hx0
  have hbpow : (β * y ^ 2) ^ N = β ^ N * y ^ (2 * N) := by
    rw [mul_pow, pow_mul]
  have hβN : 0 < β ^ N := pow_pos hβ N
  have hy2 : y ^ (2 * N) * Real.exp (-(β * y ^ 2) / 2) ≤ C / β ^ N := by
    rw [le_div_iff₀ hβN]
    rw [hbpow] at hH
    nlinarith [hH]
  have hE0 : 0 ≤ Real.exp (-(β * y ^ 2) / 2) := (Real.exp_pos _).le
  calc (1 + |u|) ^ N * Real.exp (-β * u ^ 2)
      ≤ y ^ (2 * N) * (Real.exp β * Real.exp (-(β * y ^ 2) / 2)) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp β * (y ^ (2 * N) * Real.exp (-(β * y ^ 2) / 2)) := by ring
    _ ≤ Real.exp β * (C / β ^ N) :=
        mul_le_mul_of_nonneg_left hy2 (Real.exp_pos _).le

/-- The Gaussian-polynomial lattice series `Σ_j W_K(x.1 - jc, x.2)` is summable for `α > 0`,
`c > 0`. -/
private lemma latticeW_summable (α : ℝ) (hα : 0 < α) (K : ℕ) (c : ℝ) (hc : 0 < c) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => latticeW α K (x.1 - (j : ℝ) * c) x.2) := by
  obtain ⟨Kb, hKb⟩ := polyGaussBdd K (β := α / 2) (half_pos hα)
  have hG := gp_gauss_summable x.1 (α / 2) c (half_pos hα) hc
  have hKb0 : 0 ≤ Kb := le_trans (by simp) (hKb 0)
  have hB := hG.mul_left ((1 + |x.2|) ^ K * Kb)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hB
  · unfold latticeW
    positivity
  · unfold latticeW
    set u : ℝ := x.1 - (j : ℝ) * c with hu
    set η : ℝ := x.2 with hη
    have hE1 : 0 ≤ Real.exp (-(α / 2) * u ^ 2) := (Real.exp_pos _).le
    have h1 : (1 + |u| + |η|) ^ K ≤ (1 + |η|) ^ K * (1 + |u|) ^ K := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg u, abs_nonneg η, mul_nonneg (abs_nonneg u) (abs_nonneg η)]
    have hexpsplit : Real.exp (-α * (u ^ 2 + η ^ 2)) ≤
        Real.exp (-(α / 2) * u ^ 2) * Real.exp (-(α / 2) * u ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα.le (sq_nonneg η), sq_nonneg u]
    have h2 : (1 + |u|) ^ K * Real.exp (-(α / 2) * u ^ 2) ≤ Kb := hKb u
    calc (1 + |u| + |η|) ^ K * Real.exp (-α * (u ^ 2 + η ^ 2))
        ≤ ((1 + |η|) ^ K * (1 + |u|) ^ K) *
            (Real.exp (-(α / 2) * u ^ 2) * Real.exp (-(α / 2) * u ^ 2)) :=
          mul_le_mul h1 hexpsplit (Real.exp_pos _).le (by positivity)
      _ = (1 + |η|) ^ K * ((1 + |u|) ^ K * Real.exp (-(α / 2) * u ^ 2)) *
            Real.exp (-(α / 2) * u ^ 2) := by ring
      _ ≤ (1 + |η|) ^ K * Kb * Real.exp (-(α / 2) * u ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hE1
          exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem latticeAbsorb : LatticeAbsorb := by
  intro α hα M N c hc x
  have hc0 : 0 < c := by linarith
  unfold latticeS
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_)
    ((latticeW_summable α hα N c hc0 x).mul_left ((1 + |x.2|) ^ M))
    (latticeW_summable α hα (N + M) c hc0 x)
  unfold latticeW
  have hpw : (1 + |x.2|) ^ M ≤ (1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ M :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg (x.1 - (j : ℝ) * c)]) M
  have hN : 0 ≤ (1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ N := by positivity
  have hE : 0 ≤ Real.exp (-α * ((x.1 - (j : ℝ) * c) ^ 2 + x.2 ^ 2)) := (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right hpw (mul_nonneg hN hE)
  rw [pow_add]
  calc (1 + |x.2|) ^ M * ((1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ N *
          Real.exp (-α * ((x.1 - (j : ℝ) * c) ^ 2 + x.2 ^ 2)))
      ≤ (1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ M * ((1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ N *
          Real.exp (-α * ((x.1 - (j : ℝ) * c) ^ 2 + x.2 ^ 2))) := h
    _ = (1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ N * (1 + |x.1 - (j : ℝ) * c| + |x.2|) ^ M *
          Real.exp (-α * ((x.1 - (j : ℝ) * c) ^ 2 + x.2 ^ 2)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
