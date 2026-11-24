import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/8`: composition with a bounded-derivative profile (`TameCompBdd`)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`").

Target `TameCompBdd` (`Sub/R08_2.lean`): if `θ : ℝ → ℝ` is `C^∞` with every iterated derivative
bounded, and `q` is `FlatOn (flatRegion δ M) 0` (polynomial growth of its derivatives in `ϱ⁻¹`),
then `θ ∘ q` is `FlatOn (flatRegion δ M) 0`.

Proof. Smoothness off the axis is `ContDiff.comp_contDiffOn`. For the derivative bounds, the
pointwise Faà di Bruno estimate `tcb_faa` (Mathlib's `norm_iteratedFDerivWithin_comp_le` on the
open set `axisᶜ`, transported to `iteratedFDeriv`) bounds `‖D^n (θ ∘ q) y‖` by `n! C D^n`, where
`C` bounds the derivatives of `θ` up to order `n` and `D` bounds those of `q`. On the flat region
`ϱ < 1`, the bound `C_i / ϱ^{N_i}` for each `D^i q` is at most `C_i / ϱ^{M}` with `M = Σ N_i`,
so one choice `D = (1 + K) / ϱ^M` works for all orders `1 ≤ i ≤ n`, with `K = Σ |C_i|`. Then
`D^n = (1 + K)^n / ϱ^{M n}`, and the exponential factor is `exp(-0/ϱ²) = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Faà di Bruno on the open set `axisᶜ` (task `PartII-a:R08/2/8`, pointwise form): if the
derivatives of `θ` up to order `n` at `q y` are bounded by `C` and the `i`-th derivatives of `q`
at `y` are bounded by `D^i` for `1 ≤ i ≤ n`, then `‖D^n (θ ∘ q) y‖ ≤ n! C D^n`. -/
theorem tcb_faa (θ : ℝ → ℝ) (q : Space → ℝ) (y : Space) (n : ℕ) (C D : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hq : ContDiffOn ℝ ∞ q Axi.axisᶜ) (hy : y ∈ Axi.axisᶜ)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i θ (q y)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q y‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun z => θ (q z)) y‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  have hgS : ContDiffOn ℝ ∞ θ univ := hθ.contDiffOn
  have hC' : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i θ univ (q y)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    exact hC i hi
  have hD' : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i q Axi.axisᶜ y‖ ≤ D ^ i := by
    intro i h1 h2
    have eq : iteratedFDerivWithin ℝ i q Axi.axisᶜ y = iteratedFDeriv ℝ i q y :=
      iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hy
    rw [eq]
    exact hD i h1 h2
  have h := norm_iteratedFDerivWithin_comp_le hgS hq (by exact_mod_cast le_top)
    uniqueDiffOn_univ Axi.isOpen_compl_axis.uniqueDiffOn (mapsTo_univ _ _) hy hC' hD'
  have eC : iteratedFDerivWithin ℝ n (θ ∘ q) Axi.axisᶜ y = iteratedFDeriv ℝ n (θ ∘ q) y :=
    iteratedFDerivWithin_of_isOpen n Axi.isOpen_compl_axis hy
  rw [eC] at h
  exact h

/-- **Composition with a function with bounded derivatives** (task `PartII-a:R08/2/8`): if `θ`
is `C^∞` with every iterated derivative bounded and `q` is tame, then `θ ∘ q` is tame. -/
theorem tameCompBdd : TameCompBdd := by
  unfold TameCompBdd
  intro δ M θ hθ hθB q hq
  unfold FlatOn at hq ⊢
  obtain ⟨hqS, hqb⟩ := hq
  choose Cq Nq hCq using hqb
  choose B hB using hθB
  refine ⟨hθ.comp_contDiffOn hqS, fun n => ?_⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range (n + 1), |Cq i| := ⟨_, rfl⟩
  obtain ⟨Cθ, hCθ⟩ : ∃ c : ℝ, c = ∑ i ∈ Finset.range (n + 1), |B i| := ⟨_, rfl⟩
  obtain ⟨Mt, hMt⟩ : ∃ m : ℕ, m = ∑ i ∈ Finset.range (n + 1), Nq i := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hCθ0 : ∀ i, i ≤ n → |B i| ≤ Cθ := by
    intro i hi
    rw [hCθ]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (B k)) (Finset.mem_range.2 (by omega))
  have hKle : ∀ i, i ≤ n → |Cq i| ≤ K := by
    intro i hi
    rw [hK]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (Cq k)) (Finset.mem_range.2 (by omega))
  have hNle : ∀ i, i ≤ n → Nq i ≤ Mt := by
    intro i hi
    rw [hMt]
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (Nq k)) (Finset.mem_range.2 (by omega))
  refine ⟨(n.factorial : ℝ) * Cθ * (1 + K) ^ n, Mt * n, ?_⟩
  intro y hy
  have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy
  have hyS : y ∈ Axi.axisᶜ := hy'.1
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy'.1
  have hr1 : Axi.ϱ y ≤ 1 := hy'.2.1.le
  -- the derivatives of `q` on the flat region, with a common power `ϱ^Mt`
  have hqi : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i q y‖ ≤ |Cq i| / Axi.ϱ y ^ Mt := by
    intro i hi
    have h1 := hCq i y hy
    simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at h1
    calc ‖iteratedFDeriv ℝ i q y‖ ≤ Cq i / Axi.ϱ y ^ Nq i := h1
      _ ≤ |Cq i| / Axi.ϱ y ^ Nq i :=
          div_le_div_of_nonneg_right (le_abs_self _) (pow_nonneg hr.le _)
      _ ≤ |Cq i| / Axi.ϱ y ^ Mt :=
          div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hr _)
            (pow_le_pow_of_le_one hr.le hr1 (hNle i hi))
  -- the choice `D = (1 + K) / ϱ^Mt`
  have hD1 : 1 ≤ (1 + K) / Axi.ϱ y ^ Mt := by
    rw [one_le_div (pow_pos hr _)]
    have : Axi.ϱ y ^ Mt ≤ 1 := pow_le_one₀ hr.le hr1
    linarith
  have hDi : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q y‖ ≤ ((1 + K) / Axi.ϱ y ^ Mt) ^ i := by
    intro i h1 h2
    have hA : ‖iteratedFDeriv ℝ i q y‖ ≤ K / Axi.ϱ y ^ Mt :=
      (hqi i h2).trans (div_le_div_of_nonneg_right (hKle i h2) (pow_nonneg hr.le _))
    have hA' : K / Axi.ϱ y ^ Mt ≤ (1 + K) / Axi.ϱ y ^ Mt :=
      div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)
    exact hA.trans (hA'.trans (le_self_pow₀ hD1 (by omega)))
  -- the derivatives of `θ` up to order `n`
  have hCθi : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i θ (q y)‖ ≤ Cθ := by
    intro i hi
    exact (hB i (q y)).trans ((le_abs_self _).trans (hCθ0 i hi))
  have hmain := tcb_faa θ q y n Cθ ((1 + K) / Axi.ϱ y ^ Mt) hθ hqS hyS hCθi hDi
  have hDn : ((1 + K) / Axi.ϱ y ^ Mt) ^ n = (1 + K) ^ n / Axi.ϱ y ^ (Mt * n) := by
    rw [div_pow, ← pow_mul]
  rw [hDn] at hmain
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
  calc ‖iteratedFDeriv ℝ n (fun z => θ (q z)) y‖
      ≤ (n.factorial : ℝ) * Cθ * ((1 + K) ^ n / Axi.ϱ y ^ (Mt * n)) := hmain
    _ = (n.factorial : ℝ) * Cθ * (1 + K) ^ n / Axi.ϱ y ^ (Mt * n) := by ring

end UnforcedLeray.Short.PartIIa
