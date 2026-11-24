import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/9`: the exponential of a tame function is flat (`FlatExpOfTame`)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`";
"including smoothness at nonzero axis points").

Target `FlatExpOfTame` (`Sub/R08_2.lean`): if `g` is `FlatOn (flatRegion δ M) 0` and
`g y ≤ -κ/ϱ(y)²` on `flatRegion δ M`, then `y ↦ exp (g y)` is `FlatOn (flatRegion δ M) κ`.

Proof. Smoothness off the axis is `Real.contDiff_exp.comp_contDiffOn`. For the derivative bounds,
the outer function `exp` has `‖D^i exp (g y)‖ = exp (g y)` at the single point `g y`
(`feo_expNorm`, since `D^i exp = exp`), so the Faà di Bruno estimate `feo_faa` (Mathlib's
`norm_iteratedFDerivWithin_comp_le` on the open set `axisᶜ`, transported to `iteratedFDeriv`)
bounds `‖D^n (exp ∘ g) y‖` by `n! · exp (g y) · D^n`, where `D` bounds the `i`-th derivatives of
`g` for `1 ≤ i ≤ n`. On the flat region `ϱ < 1`, the bound `C_i / ϱ^{N_i}` for each `D^i g` is at
most `|C_i| / ϱ^{M}` with `M = Σ N_i`, so one choice `D = (1 + K) / ϱ^M` works for all orders
`1 ≤ i ≤ n`, with `K = Σ |C_i|`. Then `D^n = (1 + K)^n / ϱ^{M n}`, and `exp (g y) ≤ exp (-κ/ϱ²)`
by the hypothesis on `g`. The constants `n! (1 + K)^n` and the exponent `M n` do not depend on `y`.

Helper prefix: `feo*`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `‖D^i exp x‖ = e^x` for every order `i` (task `PartII-a:R08/2/9`). -/
theorem feo_expNorm (x : ℝ) (i : ℕ) : ‖iteratedFDeriv ℝ i Real.exp x‖ = Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_of_nonneg (Real.exp_pos x).le]

/-- Faà di Bruno on the open set `axisᶜ` for `exp ∘ g` (task `PartII-a:R08/2/9`, pointwise form):
if the derivatives of `exp` up to order `n` at `g y` are bounded by `C` and the `i`-th derivatives
of `g` at `y` are bounded by `D^i` for `1 ≤ i ≤ n`, then `‖D^n (exp ∘ g) y‖ ≤ n! C D^n`. -/
theorem feo_faa (g : Space → ℝ) (y : Space) (n : ℕ) (C D : ℝ)
    (hg : ContDiffOn ℝ ∞ g Axi.axisᶜ) (hy : y ∈ Axi.axisᶜ)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Real.exp (g y)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g y‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun z => Real.exp (g z)) y‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  have hexp : ContDiffOn ℝ ∞ Real.exp univ := Real.contDiff_exp.contDiffOn
  have hC' : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i Real.exp univ (g y)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    exact hC i hi
  have hD' : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i g Axi.axisᶜ y‖ ≤ D ^ i := by
    intro i h1 h2
    have eq : iteratedFDerivWithin ℝ i g Axi.axisᶜ y = iteratedFDeriv ℝ i g y :=
      iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hy
    rw [eq]
    exact hD i h1 h2
  have h := norm_iteratedFDerivWithin_comp_le hexp hg (by exact_mod_cast le_top)
    uniqueDiffOn_univ Axi.isOpen_compl_axis.uniqueDiffOn (mapsTo_univ _ _) hy hC' hD'
  have eC : iteratedFDerivWithin ℝ n (Real.exp ∘ g) Axi.axisᶜ y
      = iteratedFDeriv ℝ n (fun z => Real.exp (g z)) y :=
    iteratedFDerivWithin_of_isOpen n Axi.isOpen_compl_axis hy
  rw [eC] at h
  exact h

/-- **The exponential of a tame function bounded by `-κ/ϱ²` is flat** (task `PartII-a:R08/2/9`,
the Prop `FlatExpOfTame`). -/
theorem flatExpOfTame : FlatExpOfTame := by
  intro δ M κ g hg hgb
  unfold FlatOn at hg ⊢
  obtain ⟨hgS, hgb'⟩ := hg
  choose Cg Ng hCg using hgb'
  refine ⟨Real.contDiff_exp.comp_contDiffOn hgS, fun n => ?_⟩
  -- the constants: `K = Σ_{i ≤ n} |C_i|` and `M = Σ_{i ≤ n} N_i`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range (n + 1), |Cg i| := ⟨_, rfl⟩
  obtain ⟨Mt, hMt⟩ : ∃ m : ℕ, m = ∑ i ∈ Finset.range (n + 1), Ng i := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hKle : ∀ i, i ≤ n → |Cg i| ≤ K := by
    intro i hi
    rw [hK]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (Cg k)) (Finset.mem_range.2 (by omega))
  have hNle : ∀ i, i ≤ n → Ng i ≤ Mt := by
    intro i hi
    rw [hMt]
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (Ng k)) (Finset.mem_range.2 (by omega))
  refine ⟨(n.factorial : ℝ) * (1 + K) ^ n, Mt * n, ?_⟩
  intro y hy
  have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy
  have hyS : y ∈ Axi.axisᶜ := hy'.1
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy'.1
  have hr1 : Axi.ϱ y ≤ 1 := hy'.2.1.le
  have hK1 : 0 ≤ 1 + K := by linarith
  -- the derivatives of `g` on the flat region, with a common power `ϱ^Mt`
  have hqi : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g y‖ ≤ |Cg i| / Axi.ϱ y ^ Mt := by
    intro i hi
    have h1 := hCg i y hy
    simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at h1
    calc ‖iteratedFDeriv ℝ i g y‖ ≤ Cg i / Axi.ϱ y ^ Ng i := h1
      _ ≤ |Cg i| / Axi.ϱ y ^ Ng i :=
          div_le_div_of_nonneg_right (le_abs_self _) (pow_nonneg hr.le _)
      _ ≤ |Cg i| / Axi.ϱ y ^ Mt :=
          div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hr _)
            (pow_le_pow_of_le_one hr.le hr1 (hNle i hi))
  -- the choice `D = (1 + K) / ϱ^Mt`
  have hD1 : 1 ≤ (1 + K) / Axi.ϱ y ^ Mt := by
    rw [one_le_div (pow_pos hr _)]
    have : Axi.ϱ y ^ Mt ≤ 1 := pow_le_one₀ hr.le hr1
    linarith
  have hDi : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g y‖ ≤ ((1 + K) / Axi.ϱ y ^ Mt) ^ i := by
    intro i h1 h2
    have hA : ‖iteratedFDeriv ℝ i g y‖ ≤ K / Axi.ϱ y ^ Mt :=
      (hqi i h2).trans (div_le_div_of_nonneg_right (hKle i h2) (pow_nonneg hr.le _))
    have hA' : K / Axi.ϱ y ^ Mt ≤ (1 + K) / Axi.ϱ y ^ Mt :=
      div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)
    exact hA.trans (hA'.trans (le_self_pow₀ hD1 (by omega)))
  -- the outer derivatives of `exp` at the point `g y`
  have hCexp : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Real.exp (g y)‖ ≤ Real.exp (g y) :=
    fun i _ => (feo_expNorm (g y) i).le
  have hmain := feo_faa g y n (Real.exp (g y)) ((1 + K) / Axi.ϱ y ^ Mt) hgS hyS hCexp hDi
  have hDn : ((1 + K) / Axi.ϱ y ^ Mt) ^ n = (1 + K) ^ n / Axi.ϱ y ^ (Mt * n) := by
    rw [div_pow, ← pow_mul]
  rw [hDn] at hmain
  have hexp_le : Real.exp (g y) ≤ Real.exp (-κ / Axi.ϱ y ^ 2) :=
    Real.exp_le_exp.mpr (hgb y hy)
  have hpos : 0 ≤ (n.factorial : ℝ) * (1 + K) ^ n / Axi.ϱ y ^ (Mt * n) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hK1 n)) (pow_nonneg hr.le _)
  calc ‖iteratedFDeriv ℝ n (fun z => Real.exp (g z)) y‖
      ≤ (n.factorial : ℝ) * Real.exp (g y) * ((1 + K) ^ n / Axi.ϱ y ^ (Mt * n)) := hmain
    _ = ((n.factorial : ℝ) * (1 + K) ^ n / Axi.ϱ y ^ (Mt * n)) * Real.exp (g y) := by ring
    _ ≤ ((n.factorial : ℝ) * (1 + K) ^ n / Axi.ϱ y ^ (Mt * n)) * Real.exp (-κ / Axi.ϱ y ^ 2) :=
        mul_le_mul_of_nonneg_left hexp_le hpos
    _ = (n.factorial : ℝ) * (1 + K) ^ n / Axi.ϱ y ^ (Mt * n) * Real.exp (-κ / Axi.ϱ y ^ 2) := rfl

end UnforcedLeray.Short.PartIIa
