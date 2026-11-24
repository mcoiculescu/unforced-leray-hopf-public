import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/5`: the inverse radius `ϱ⁻¹` is tame

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("each
derivative costs `C/r`").

This file proves the Prop `TameInvRho` of `Sub/R08_2.lean`: for all `δ M`, the function `ϱ⁻¹` is
`C^∞` off the axis and `‖Dⁿ ϱ⁻¹(y)‖ ≤ C / ϱ(y)^N` on `flatRegion δ M` (here `κ = 0`, so the
exponential factor is `1`).

Method. `ϱ⁻¹ = h ∘ s` with `s y = y₀² + y₁²` and `h u = u^(-1/2)` (`tirInv_eq`). Faà di Bruno
(`norm_iteratedFDerivWithin_comp_le`) on the open set `axisᶜ`, with the outer set `Ioi 0`:

* the outer derivatives are `|descPochhammer_i(-1/2)| u^(-1/2-i)` (`Real.iter_deriv_rpow_const`),
  bounded by `tirK n * u^(-1/2-n)` for `0 < u ≤ 1` (`tirOuter_le`);
* the inner derivatives satisfy `‖Dⁱ s y‖ ≤ 4` for `i ≥ 1` when `ϱ y < 1`: `s` is a sum of squares
  of two coordinates, each coordinate square has `i`-th derivative bounded by `2` (`tirSq_iter_le`)
  and transported along the coordinate projection (`tirComp_le`), so `tirSq_D` holds.

With `u = ϱ²`, `u^(-1/2-n) = (ϱ^(1+2n))⁻¹` (`tirRpow`), which gives the exponent `N = 1 + 2n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The coordinate projection `y ↦ y c` of `Space`, as a continuous linear map. -/
abbrev tirProj (c : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj c

/-- A coordinate projection has operator norm at most `1`. -/
theorem tirProj_norm_le (c : Fin 3) : ‖tirProj c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
  rw [one_mul]
  exact PiLp.norm_apply_le y c

/-- Composition with a coordinate projection does not increase the `n`-th derivative. -/
theorem tirComp_le (c : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ n (fun w : Space => f (tirProj c w)) y‖ ≤
      ‖iteratedFDeriv ℝ n f (tirProj c y)‖ := by
  have hcomp : (fun w : Space => f (tirProj c w)) = f ∘ tirProj c := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n) (tirProj c) hf y
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _k : Fin n, ‖tirProj c‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => tirProj_norm_le c)
  calc ‖iteratedFDeriv ℝ n f (tirProj c y)‖ * ∏ _k : Fin n, ‖tirProj c‖
      ≤ ‖iteratedFDeriv ℝ n f (tirProj c y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n f (tirProj c y)‖ := mul_one _

/-- One-variable square: every derivative of order `i ≥ 1` is bounded by `2` on `|t| ≤ 1`. -/
theorem tirSq_iter_le (i : ℕ) (hi : 1 ≤ i) (t : ℝ) (ht : t ^ 2 ≤ 1) :
    ‖iteratedFDeriv ℝ i (fun x : ℝ => x ^ 2) t‖ ≤ 2 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_pow]
  have h1 : |t| ≤ 1 := (sq_le_one_iff_abs_le_one t).1 ht
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · interval_cases i
    · norm_num [Nat.descFactorial_one, abs_mul]
      linarith
    · norm_num [Nat.descFactorial_self]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 < i)]
    norm_num

/-- Positivity of `s y = y₀² + y₁²` off the axis. -/
theorem tirSq_pos (y : Space) (hy : y ∉ Axi.axis) : 0 < y 0 ^ 2 + y 1 ^ 2 := by
  rw [← Axi.ϱ_sq]
  exact pow_pos (Axi.ϱ_pos hy) 2

/-- Inner derivatives of `s y = y₀² + y₁²`: for `ϱ y < 1` and `i ≥ 1`, `‖Dⁱ s y‖ ≤ 4`. -/
theorem tirSq_D (y : Space) (hy : Axi.ϱ y < 1) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun w : Space => w 0 ^ 2 + w 1 ^ 2) y‖ ≤ 4 := by
  have hsq : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2) := by fun_prop
  have hA : ContDiff ℝ ∞ (fun w : Space => w 0 ^ 2) := by fun_prop
  have hB : ContDiff ℝ ∞ (fun w : Space => w 1 ^ 2) := by fun_prop
  have hAt : ContDiffAt ℝ i (fun w : Space => w 0 ^ 2) y :=
    hA.contDiffAt.of_le (by exact_mod_cast le_top)
  have hBt : ContDiffAt ℝ i (fun w : Space => w 1 ^ 2) y :=
    hB.contDiffAt.of_le (by exact_mod_cast le_top)
  have hsplit : (fun w : Space => w 0 ^ 2 + w 1 ^ 2) =
      (fun w : Space => w 0 ^ 2) + (fun w : Space => w 1 ^ 2) := rfl
  have hy0 : (tirProj 0 y) ^ 2 ≤ 1 := by
    have h : y 0 ^ 2 ≤ 1 := by
      nlinarith [Axi.ϱ_sq y, Axi.ϱ_nonneg y, sq_nonneg (y 1),
        mul_nonneg (Axi.ϱ_nonneg y) (sub_nonneg.2 hy.le)]
    exact h
  have hy1 : (tirProj 1 y) ^ 2 ≤ 1 := by
    have h : y 1 ^ 2 ≤ 1 := by
      nlinarith [Axi.ϱ_sq y, Axi.ϱ_nonneg y, sq_nonneg (y 0),
        mul_nonneg (Axi.ϱ_nonneg y) (sub_nonneg.2 hy.le)]
    exact h
  have hA' : ‖iteratedFDeriv ℝ i (fun w : Space => w 0 ^ 2) y‖ ≤ 2 :=
    (tirComp_le 0 hsq i y).trans (tirSq_iter_le i hi (tirProj 0 y) hy0)
  have hB' : ‖iteratedFDeriv ℝ i (fun w : Space => w 1 ^ 2) y‖ ≤ 2 :=
    (tirComp_le 1 hsq i y).trans (tirSq_iter_le i hi (tirProj 1 y) hy1)
  rw [hsplit, iteratedFDeriv_add_apply hAt hBt]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The constant `tirK n = ∑_{j ≤ n} |(descPochhammer j)(-1/2)|` of the outer Faà di Bruno bound. -/
def tirK (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), |(descPochhammer ℝ j).eval (-(1/2 : ℝ))|

/-- Outer derivatives of `t ↦ t^(-1/2)` on `Ioi 0`, at `u ∈ (0, 1]`, for orders `i ≤ n`. -/
theorem tirOuter_le (n : ℕ) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (i : ℕ) (hi : i ≤ n) :
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ (-(1/2 : ℝ))) (Ioi 0) u‖ ≤
      tirK n * u ^ (-(1/2 : ℝ) - (n : ℝ)) := by
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (show u ∈ Ioi 0 from hu0),
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
  have h1 : |(descPochhammer ℝ i).eval (-(1/2 : ℝ))| ≤ tirK n :=
    Finset.single_le_sum (f := fun j => |(descPochhammer ℝ j).eval (-(1/2 : ℝ))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hi' : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
  have h2 : u ^ (-(1/2 : ℝ) - (i : ℝ)) ≤ u ^ (-(1/2 : ℝ) - (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos hu0 _).le ((abs_nonneg _).trans h1)

/-- `ϱ⁻¹ = (y₀² + y₁²)^(-1/2)`. -/
theorem tirInv_eq (w : Space) : (Axi.ϱ w)⁻¹ = (w 0 ^ 2 + w 1 ^ 2) ^ (-(1/2 : ℝ)) := by
  unfold Axi.ϱ
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : (0:ℝ) ≤ w 0 ^ 2 + w 1 ^ 2)]

/-- `(ρ²)^(-1/2 - n) = (ρ^(1+2n))⁻¹` for `ρ > 0`. -/
theorem tirRpow (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    (ρ ^ 2) ^ (-(1/2 : ℝ) - (n : ℝ)) = (ρ ^ (1 + 2 * n))⁻¹ := by
  rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
  have h2 : ((2 : ℕ) : ℝ) * (-(1/2 : ℝ) - (n : ℝ)) = -((1 + 2 * n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h2, Real.rpow_neg hρ.le, Real.rpow_natCast]

/-- Pointwise Faà di Bruno bound for `ϱ⁻¹` off the axis, with `ϱ < 1`. -/
theorem tirPoint (n : ℕ) (y : Space) (hy : y ∉ Axi.axis) (hy1 : Axi.ϱ y < 1) :
    ‖iteratedFDeriv ℝ n (fun w : Space => (Axi.ϱ w)⁻¹) y‖ ≤
      (n.factorial : ℝ) * (tirK n * (y 0 ^ 2 + y 1 ^ 2) ^ (-(1/2 : ℝ) - (n : ℝ))) * 4 ^ n := by
  have hu0 : 0 < y 0 ^ 2 + y 1 ^ 2 := tirSq_pos y hy
  have hu1 : y 0 ^ 2 + y 1 ^ 2 ≤ 1 := by
    nlinarith [Axi.ϱ_sq y, Axi.ϱ_nonneg y, mul_nonneg (Axi.ϱ_nonneg y) (sub_nonneg.2 hy1.le)]
  have hsqC : ContDiff ℝ ∞ (fun w : Space => w 0 ^ 2 + w 1 ^ 2) := by fun_prop
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ (-(1/2 : ℝ))) (Ioi 0) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne (show (0:ℝ) < x from hx).ne').contDiffWithinAt
  have hyc : y ∈ Axi.axisᶜ := hy
  have hst : MapsTo (fun w : Space => w 0 ^ 2 + w 1 ^ 2) Axi.axisᶜ (Ioi 0) :=
    fun w hw => tirSq_pos w hw
  have hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ (-(1/2 : ℝ))) (Ioi 0)
      (y 0 ^ 2 + y 1 ^ 2)‖ ≤ tirK n * (y 0 ^ 2 + y 1 ^ 2) ^ (-(1/2 : ℝ) - (n : ℝ)) :=
    fun i hi => tirOuter_le n _ hu0 hu1 i hi
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun w : Space => w 0 ^ 2 + w 1 ^ 2) Axi.axisᶜ y‖ ≤ 4 ^ i := by
    intro i hi1 _
    rw [iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hyc]
    exact (tirSq_D y hy1 i hi1).trans
      (le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hi1))
  have hcomp := norm_iteratedFDerivWithin_comp_le
    (g := fun t : ℝ => t ^ (-(1/2 : ℝ))) (f := fun w : Space => w 0 ^ 2 + w 1 ^ 2)
    (n := n) (s := Axi.axisᶜ) (t := Ioi 0) (x := y) (N := ∞)
    hg hsqC.contDiffOn (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
    Axi.isOpen_compl_axis.uniqueDiffOn hst hyc hC hD
  have hfun : ((fun t : ℝ => t ^ (-(1/2 : ℝ))) ∘ (fun w : Space => w 0 ^ 2 + w 1 ^ 2)) =
      (fun w : Space => (Axi.ϱ w)⁻¹) := by
    funext w
    exact (tirInv_eq w).symm
  rw [hfun, iteratedFDerivWithin_of_isOpen n Axi.isOpen_compl_axis hyc] at hcomp
  exact hcomp

/-- Uniform bound with the exponent `N = 1 + 2n`, for points with `ϱ < 1` off the axis. -/
theorem tirBound (n : ℕ) : ∃ C : ℝ, ∀ y : Space, y ∉ Axi.axis → Axi.ϱ y < 1 →
    ‖iteratedFDeriv ℝ n (fun w : Space => (Axi.ϱ w)⁻¹) y‖ ≤ C / Axi.ϱ y ^ (1 + 2 * n) := by
  refine ⟨(n.factorial : ℝ) * tirK n * 4 ^ n, fun y hy hy1 => ?_⟩
  have hpt := tirPoint n y hy hy1
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  rw [← Axi.ϱ_sq y, tirRpow (Axi.ϱ y) hϱ n] at hpt
  exact hpt.trans (le_of_eq (by ring))

/-- **`ϱ⁻¹` is tame** (task `PartII-a:R08/2/5`): the Prop `TameInvRho` of `Sub/R08_2.lean`. -/
theorem tameInvRho : UnforcedLeray.Short.PartIIa.TameInvRho := by
  unfold TameInvRho FlatOn
  intro δ M
  refine ⟨?_, fun n => ?_⟩
  · exact (Axi.contDiffOn_ϱ (k := ∞)).inv (fun y hy => Axi.ϱ_ne_zero hy)
  · obtain ⟨C, hC⟩ := tirBound n
    refine ⟨C, 1 + 2 * n, fun y hy => ?_⟩
    have hy' : y ∉ Axi.axis ∧ Axi.ϱ y < 1 := by
      obtain ⟨h1, h2, -, -⟩ := hy
      exact ⟨h1, h2⟩
    rw [neg_zero, zero_div, Real.exp_zero, mul_one]
    exact hC y hy'.1 hy'.2

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.tameInvRho
