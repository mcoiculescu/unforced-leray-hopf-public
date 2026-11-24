import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Nat.Choose.Sum

/-!
# Cartesian angular-two functions (INF12 target P9)


§5, Level P, target **P9** (used by target O14, the Gaussian derivative bounds of the growing
mode). An angular-two function `h(r)e^{2iϑ}` with `h(r) = r² β(r²)` is, in Cartesian
coordinates `y ∈ ℂ = ℝ²`, the function `y ↦ y² β(|y|²)` (since `y² = r² e^{2iϑ}`). The
manuscript uses that the eigenvorticity `q = h(r)e^{2iϑ}` "is smooth, Gaussian-decaying with all
derivatives" (`paper/main.tex` line 698) and measures Cartesian derivatives of angular-two
functions (line 1864: "Cartesian differentiation can leave angular sector two").

Main declarations (namespace `UnforcedLeray.Planar`):
* `contDiff_angularTwo`: if `β` is `Cⁿ` (any `n`, including `∞` and analytic), so is
  `y ↦ y² β(|y|²)`;
* `norm_iteratedFDeriv_angularTwo_le`: for each `k` there are `C` and `N`, **independent of `β`**,
  such that for every `C^k` function `β` and every `y`,
  `‖D^k(y² β(|y|²))‖ ≤ C (1 + |y|)^N ∑_{m ≤ k} |β^{(m)}(|y|²)|`
  (the scoping note writes `⨆_{m ≤ k}`; the finite sum is equivalent up to the factor `k + 1`
  and avoids the junk-valued real supremum).

Proof: Faà di Bruno's bound `norm_iteratedFDeriv_comp_le` for `β ∘ |·|²` and Leibniz's bound
`norm_iteratedFDeriv_mul_le`; `y²` and `|y|² = Re(y ȳ)` are continuous bilinear expressions in
contractions, so all their iterated derivatives are `≤ 2ⁿ (1 + |y|)²`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace UnforcedLeray.Planar

/-- Iterated derivatives of a contraction `L` are bounded by `1 + |y|`. -/
theorem norm_iteratedFDeriv_clm_le (L : ℂ →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) (i : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ i (fun x => L x) y‖ ≤ 1 + ‖y‖ := by
  rcases i with _ | i
  · rw [norm_iteratedFDeriv_zero]
    calc ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
      _ ≤ 1 * ‖y‖ := by gcongr
      _ ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  · rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (fun x => L x) = fun _ => L := funext fun x => L.fderiv
    rw [hd]
    rcases i with _ | i
    · rw [norm_iteratedFDeriv_zero]
      linarith [norm_nonneg y]
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

/-- Iterated derivatives of `y ↦ B(L₁y, L₂y)` for contractions `L₁, L₂`. -/
theorem norm_iteratedFDeriv_bilin_le (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (L₁ L₂ : ℂ →L[ℝ] ℂ)
    (h₁ : ‖L₁‖ ≤ 1) (h₂ : ‖L₂‖ ≤ 1) (n : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ n (fun x => B (L₁ x) (L₂ x)) y‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖y‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := fun x => L₁ x) (g := fun x => L₂ x)
    (N := ⊤) L₁.contDiff L₂.contDiff y (n := n) le_top
  refine h.trans ?_
  gcongr
  calc ∑ i ∈ range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => L₁ x) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun x => L₂ x) y‖
      ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (1 + ‖y‖) * (1 + ‖y‖) := by
        gcongr with i hi
        · exact norm_iteratedFDeriv_clm_le L₁ h₁ i y
        · exact norm_iteratedFDeriv_clm_le L₂ h₂ _ y
    _ = 2 ^ n * (1 + ‖y‖) ^ 2 := by
        rw [← sum_mul, ← sum_mul]
        have hc : (∑ i ∈ range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [hc]
        ring

/-- `‖D^n(y²)‖ ≤ 2ⁿ (1 + |y|)²`. -/
theorem norm_iteratedFDeriv_sq_le (n : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ n (fun x : ℂ => x ^ 2) y‖ ≤ 2 ^ n * (1 + ‖y‖) ^ 2 := by
  have h := norm_iteratedFDeriv_bilin_le (ContinuousLinearMap.mul ℝ ℂ)
    (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℝ ℂ) ContinuousLinearMap.norm_id_le
    ContinuousLinearMap.norm_id_le n y
  have e : (fun x : ℂ => (ContinuousLinearMap.mul ℝ ℂ) ((ContinuousLinearMap.id ℝ ℂ) x)
      ((ContinuousLinearMap.id ℝ ℂ) x)) = fun x => x ^ 2 := by
    funext x
    simp [pow_two]
  rw [e] at h
  refine h.trans ?_
  have hm := ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  calc ‖ContinuousLinearMap.mul ℝ ℂ‖ * (2 ^ n * (1 + ‖y‖) ^ 2)
      ≤ 1 * (2 ^ n * (1 + ‖y‖) ^ 2) := by gcongr
    _ = 2 ^ n * (1 + ‖y‖) ^ 2 := one_mul _

/-- `‖D^n(|y|²)‖ ≤ 2ⁿ (1 + |y|)²` (`|y|² = Re(y ȳ)`). -/
theorem norm_iteratedFDeriv_normSq_le (n : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ n (fun x : ℂ => ‖x‖ ^ 2) y‖ ≤ 2 ^ n * (1 + ‖y‖) ^ 2 := by
  set g : ℂ → ℂ := fun x => (ContinuousLinearMap.mul ℝ ℂ) ((ContinuousLinearMap.id ℝ ℂ) x)
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ) x) with hg
  have e : (fun x : ℂ => ‖x‖ ^ 2) = Complex.reCLM ∘ g := by
    funext x
    simp only [Function.comp_apply, hg, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.id_apply, Complex.reCLM_apply]
    change ‖x‖ ^ 2 = (x * (starRingEnd ℂ) x).re
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hgc : ContDiff ℝ ⊤ g :=
    (ContinuousLinearMap.mul ℝ ℂ).isBoundedBilinearMap.contDiff.comp
      ((ContinuousLinearMap.id ℝ ℂ).contDiff.prodMk (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff)
  rw [e]
  refine (Complex.reCLM.norm_iteratedFDeriv_comp_left hgc.contDiffAt le_top).trans ?_
  rw [Complex.reCLM_norm, one_mul]
  refine (norm_iteratedFDeriv_bilin_le _ _ _ ContinuousLinearMap.norm_id_le
    Complex.conjCLE_norm.le n y).trans ?_
  have hm := ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  calc ‖ContinuousLinearMap.mul ℝ ℂ‖ * (2 ^ n * (1 + ‖y‖) ^ 2)
      ≤ 1 * (2 ^ n * (1 + ‖y‖) ^ 2) := by gcongr
    _ = 2 ^ n * (1 + ‖y‖) ^ 2 := one_mul _

/-- **Smoothness of Cartesian angular-two functions**: if `β` is `Cⁿ`, so is `y ↦ y² β(|y|²)`. -/
theorem contDiff_angularTwo {n : WithTop ℕ∞} {β : ℝ → ℂ} (hβ : ContDiff ℝ n β) :
    ContDiff ℝ n (fun y : ℂ => y ^ 2 * β (‖y‖ ^ 2)) := by
  have h1 : ContDiff ℝ n (fun y : ℂ => y ^ 2) := contDiff_id.pow 2
  have h2 : ContDiff ℝ n (fun y : ℂ => β (‖y‖ ^ 2)) := hβ.comp (contDiff_norm_sq ℝ)
  exact h1.mul h2

/-- Faà di Bruno for `β(|y|²)`: for `j ≤ k`,
`‖D^j β(|y|²)‖ ≤ j! (∑_{m ≤ k} |β^{(m)}(|y|²)|) (2(1+|y|)²)^j`. -/
theorem norm_iteratedFDeriv_comp_normSq_le {k : ℕ} {β : ℝ → ℂ} (hβ : ContDiff ℝ k β) {j : ℕ}
    (hj : j ≤ k) (y : ℂ) :
    ‖iteratedFDeriv ℝ j (fun x : ℂ => β (‖x‖ ^ 2)) y‖ ≤
      j.factorial * (∑ m ∈ range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖) *
        (2 * (1 + ‖y‖) ^ 2) ^ j := by
  have ha1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
  have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := β) (f := fun x : ℂ => ‖x‖ ^ 2)
    (N := k) hβ (contDiff_norm_sq ℝ) (n := j) (by exact_mod_cast hj) y
    (C := ∑ m ∈ range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖) (D := 2 * (1 + ‖y‖) ^ 2) ?_ ?_
  · exact h
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact single_le_sum (f := fun m => ‖iteratedDeriv m β (‖y‖ ^ 2)‖)
      (fun m _ => norm_nonneg _) (mem_range.2 (by omega))
  · intro i hi1 _
    refine (norm_iteratedFDeriv_normSq_le i y).trans ?_
    rw [mul_pow]
    gcongr
    exact le_self_pow₀ ha1 (by omega)

/-- **Derivative bounds for Cartesian angular-two functions**: for every `k` there are `C` and
`N` such that for every `C^k` profile `β` and every `y ∈ ℂ`,
`‖D^k(y² β(|y|²))‖ ≤ C (1 + |y|)^N ∑_{m ≤ k} |β^{(m)}(|y|²)|`. -/
theorem norm_iteratedFDeriv_angularTwo_le (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ β : ℝ → ℂ, ContDiff ℝ k β → ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k (fun y : ℂ => y ^ 2 * β (‖y‖ ^ 2)) y‖ ≤
        C * (1 + ‖y‖) ^ N * ∑ m ∈ range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖ := by
  refine ⟨4 ^ k * k.factorial, 2 * k + 2, fun β hβ y => ?_⟩
  set S : ℝ := ∑ m ∈ range (k + 1), ‖iteratedDeriv m β (‖y‖ ^ 2)‖ with hS
  set a : ℝ := 1 + ‖y‖ with ha
  have ha1 : 1 ≤ a := by linarith [norm_nonneg y]
  have ha0 : 0 ≤ a := by linarith
  have hS0 : 0 ≤ S := sum_nonneg fun m _ => norm_nonneg _
  have h1 : ContDiff ℝ k (fun y : ℂ => y ^ 2) := contDiff_id.pow 2
  have h2 : ContDiff ℝ k (fun y : ℂ => β (‖y‖ ^ 2)) := hβ.comp (contDiff_norm_sq ℝ)
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y : ℂ => y ^ 2)
    (g := fun y : ℂ => β (‖y‖ ^ 2)) (N := k) h1 h2 y (n := k) le_rfl
  refine h.trans ?_
  have hterm : ∀ i ∈ range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℂ => y ^ 2) y‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun y : ℂ => β (‖y‖ ^ 2)) y‖ ≤
      (k.choose i : ℝ) * (2 ^ k * k.factorial * a ^ (2 * k + 2) * S) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hp := norm_iteratedFDeriv_sq_le i y
    have hq := norm_iteratedFDeriv_comp_normSq_le hβ (j := k - i) (Nat.sub_le k i) y
    rw [← hS, ← ha] at hq
    rw [← ha] at hp
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hfac : ((k - i).factorial : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.factorial_le (Nat.sub_le k i)
    have hpow : a ^ 2 * (a ^ 2) ^ (k - i) ≤ a ^ (2 * k + 2) := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ ha1 (by omega)
    have h2k : (2 : ℝ) ^ i * 2 ^ (k - i) = 2 ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hik]
    calc ‖iteratedFDeriv ℝ i (fun y : ℂ => y ^ 2) y‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun y : ℂ => β (‖y‖ ^ 2)) y‖
        ≤ (2 ^ i * a ^ 2) * ((k - i).factorial * S * (2 * a ^ 2) ^ (k - i)) := by
          gcongr
      _ = (2 ^ i * 2 ^ (k - i)) * (k - i).factorial * (a ^ 2 * (a ^ 2) ^ (k - i)) * S := by
          rw [mul_pow]
          ring
      _ ≤ 2 ^ k * k.factorial * a ^ (2 * k + 2) * S := by
          rw [h2k]
          gcongr
  refine (sum_le_sum hterm).trans_eq ?_
  rw [← sum_mul]
  have hc : (∑ i ∈ range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hc, show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
  ring

end UnforcedLeray.Planar
