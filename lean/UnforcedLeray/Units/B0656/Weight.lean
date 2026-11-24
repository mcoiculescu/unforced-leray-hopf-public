import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# B0656, part 1: the smooth periodic weight `ρ_ℓ`

Blueprint unit **B0656** (`unlabeled:13869`), `paper/main.tex` lines 13869–13878.

The weight `ρ_ℓ(q,η) = 1 + (ℓ/π)² sin²(πq/ℓ) + η²` is defined on the plane `ℝ × ℝ` of
lifted cylinder coordinates `(q, η)`. This file proves the three pointwise facts that the
manuscript asserts about it:

* it is smooth, `ℓ`-periodic in `q`, and at least one everywhere, in particular at both seams
  `q = ±ℓ/2` (line 13878);
* on the centered cell `|q| ≤ ℓ/2` it is comparable to `1 + q² + η²` with the constants `4/π²`
  and `1`, uniformly in `ℓ > 0` (line 13876);
* every fixed derivative of `ρ_ℓ^s` (any real `s`, in particular `s = ±m`) is bounded by a
  constant times `ρ_ℓ^s`, the constant depending on the order and on `s` but not on `ℓ ≥ 1`
  (lines 13877–13878).
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped ContDiff Nat

namespace UnforcedLeray.B0656

/-- Lifted coordinates `(q, η)` of the periodic cylinder. -/
abbrev Plane := ℝ × ℝ

/-- The smooth periodic weight `ρ_ℓ(q,η) = 1 + (ℓ/π)² sin²(πq/ℓ) + η²`
(`paper/main.tex`, line 13872). The formula is used on the whole plane; it is `ℓ`-periodic
in `q` (`rho_periodic`), so it is the periodic extension of its restriction to the centered
cell `-ℓ/2 ≤ q ≤ ℓ/2`. -/
def rho (ℓ : ℝ) (z : Plane) : ℝ :=
  1 + (ℓ / π) ^ 2 * Real.sin (π * z.1 / ℓ) ^ 2 + z.2 ^ 2

/-- The `q`-part of the weight. -/
def rhoQ (ℓ : ℝ) (q : ℝ) : ℝ :=
  1 + (ℓ / π) ^ 2 * Real.sin (π * q / ℓ) ^ 2

theorem rho_eq (ℓ : ℝ) (z : Plane) : rho ℓ z = rhoQ ℓ z.1 + z.2 ^ 2 := rfl

theorem one_le_rhoQ (ℓ q : ℝ) : 1 ≤ rhoQ ℓ q := by
  unfold rhoQ
  have : 0 ≤ (ℓ / π) ^ 2 * Real.sin (π * q / ℓ) ^ 2 := by positivity
  linarith

/-- The weight is at least one everywhere. -/
theorem one_le_rho (ℓ : ℝ) (z : Plane) : 1 ≤ rho ℓ z := by
  rw [rho_eq]
  have := one_le_rhoQ ℓ z.1
  have : 0 ≤ z.2 ^ 2 := sq_nonneg _
  linarith

theorem rho_pos (ℓ : ℝ) (z : Plane) : 0 < rho ℓ z :=
  lt_of_lt_of_le one_pos (one_le_rho ℓ z)

theorem one_add_sq_le_rho (ℓ : ℝ) (z : Plane) : 1 + z.2 ^ 2 ≤ rho ℓ z := by
  rw [rho_eq]
  have := one_le_rhoQ ℓ z.1
  linarith

theorem rhoQ_le_rho (ℓ : ℝ) (z : Plane) : rhoQ ℓ z.1 ≤ rho ℓ z := by
  rw [rho_eq]
  have : 0 ≤ z.2 ^ 2 := sq_nonneg _
  linarith

theorem contDiff_rhoQ (ℓ : ℝ) : ContDiff ℝ ∞ (rhoQ ℓ) := by
  unfold rhoQ
  fun_prop

/-- **Claim (a), smoothness** (line 13869: "smooth periodic weight"). The weight is a
`C^∞` function on the whole plane, hence also across the seams of the centered cell. -/
theorem contDiff_rho (ℓ : ℝ) : ContDiff ℝ ∞ (rho ℓ) := by
  unfold rho
  fun_prop

/-- **Claim (a), periodicity** (line 13869). `ρ_ℓ` is `ℓ`-periodic in `q`. -/
theorem rho_periodic {ℓ : ℝ} (hℓ : ℓ ≠ 0) (q η : ℝ) : rho ℓ (q + ℓ, η) = rho ℓ (q, η) := by
  simp only [rho]
  have : π * (q + ℓ) / ℓ = π * q / ℓ + π := by field_simp
  rw [this, Real.sin_add_pi, neg_sq]

/-- **Claim (a), the seams** (line 13878: "this weight does not vanish at either seam").
At `q = ±ℓ/2` the weight equals `1 + (ℓ/π)² + η² > 0`. Together with `contDiff_rho` this
records that the periodic weight is neither zero nor singular across the seams. -/
theorem rho_seam {ℓ : ℝ} (hℓ : ℓ ≠ 0) (η : ℝ) :
    rho ℓ (ℓ / 2, η) = 1 + (ℓ / π) ^ 2 + η ^ 2 ∧
      rho ℓ (-(ℓ / 2), η) = 1 + (ℓ / π) ^ 2 + η ^ 2 := by
  have h1 : π * (ℓ / 2) / ℓ = π / 2 := by field_simp
  have h2 : π * (-(ℓ / 2)) / ℓ = -(π / 2) := by field_simp
  refine ⟨?_, ?_⟩
  · simp only [rho, h1, Real.sin_pi_div_two]
    ring
  · simp only [rho, h2, Real.sin_neg, Real.sin_pi_div_two]
    ring

/-- `(ℓ/π)² sin²(πq/ℓ) ≤ q²` for every `ℓ` and `q`. -/
theorem sinPart_le_sq (ℓ q : ℝ) : (ℓ / π) ^ 2 * Real.sin (π * q / ℓ) ^ 2 ≤ q ^ 2 := by
  rcases eq_or_ne ℓ 0 with h | h
  · subst h
    simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  have hbound : |ℓ / π * Real.sin (π * q / ℓ)| ≤ |q| := by
    rw [abs_mul]
    calc |ℓ / π| * |Real.sin (π * q / ℓ)| ≤ |ℓ / π| * |π * q / ℓ| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _)
      _ = |ℓ / π * (π * q / ℓ)| := (abs_mul _ _).symm
      _ = |q| := by
          congr 1
          field_simp
  have := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  rw [sq_abs, sq_abs, mul_pow] at this
  exact this

/-- Jordan's inequality on the half cell: `(4/π²) q² ≤ (ℓ/π)² sin²(πq/ℓ)` for `|q| ≤ ℓ/2`. -/
theorem sq_le_sinPart {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : |q| ≤ ℓ / 2) :
    4 / π ^ 2 * q ^ 2 ≤ (ℓ / π) ^ 2 * Real.sin (π * q / ℓ) ^ 2 := by
  -- reduce to `q ≥ 0`, using that both sides are even in `q`
  have hsq : Real.sin (π * q / ℓ) ^ 2 = Real.sin (π * |q| / ℓ) ^ 2 := by
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show π * -q / ℓ = -(π * q / ℓ) by ring, Real.sin_neg, neg_sq]
  rw [hsq, show q ^ 2 = |q| ^ 2 from (sq_abs q).symm]
  set x := |q| with hx
  have hx0 : 0 ≤ x := abs_nonneg q
  have hy0 : 0 ≤ π * x / ℓ := by positivity
  have hy1 : π * x / ℓ ≤ π / 2 := by
    rw [div_le_iff₀ hℓ]
    nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin hy0 hy1
  have hlhs : 2 / π * (π * x / ℓ) = 2 * x / ℓ := by field_simp
  rw [hlhs] at hj
  have hj0 : 0 ≤ 2 * x / ℓ := by positivity
  have hsq2 := pow_le_pow_left₀ hj0 hj 2
  have hπ : 0 < π := Real.pi_pos
  calc 4 / π ^ 2 * x ^ 2 = (ℓ / π) ^ 2 * (2 * x / ℓ) ^ 2 := by field_simp; ring
    _ ≤ (ℓ / π) ^ 2 * Real.sin (π * x / ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq2 (sq_nonneg _)

theorem four_div_pi_sq_le_one : 4 / π ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [Real.pi_gt_three]

/-- **Claim (b)** (line 13876: "uniformly comparable on the centered cell to `1+q²+η²`").
For every `ℓ > 0` and every point of the centered cell `|q| ≤ ℓ/2`,
`(4/π²)(1+q²+η²) ≤ ρ_ℓ(q,η) ≤ 1+q²+η²`. The constants do not depend on `ℓ`. -/
theorem rho_comparable {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Plane) (hz : |z.1| ≤ ℓ / 2) :
    4 / π ^ 2 * (1 + z.1 ^ 2 + z.2 ^ 2) ≤ rho ℓ z ∧ rho ℓ z ≤ 1 + z.1 ^ 2 + z.2 ^ 2 := by
  have hup := sinPart_le_sq ℓ z.1
  have hlow := sq_le_sinPart hℓ hz
  have hc := four_div_pi_sq_le_one
  have hc0 : 0 ≤ 4 / π ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [rho]
    have h1 : 4 / π ^ 2 * 1 ≤ 1 := by linarith
    have h2 : 4 / π ^ 2 * z.2 ^ 2 ≤ z.2 ^ 2 := by
      have := mul_le_mul_of_nonneg_right hc (sq_nonneg z.2)
      linarith
    nlinarith
  · simp only [rho]
    linarith

/-! ### Derivative bounds -/

/-- Cosine form of the `q`-part. -/
theorem rhoQ_eq_cos (ℓ q : ℝ) :
    rhoQ ℓ q = (1 + (ℓ / π) ^ 2 / 2) + (-((ℓ / π) ^ 2 / 2)) * Real.cos (2 * π / ℓ * q) := by
  unfold rhoQ
  have hs : Real.sin (π * q / ℓ) ^ 2 = 1 / 2 - Real.cos (2 * (π * q / ℓ)) / 2 := by
    rw [Real.sin_sq, Real.cos_sq]
    ring
  rw [hs, show 2 * (π * q / ℓ) = 2 * π / ℓ * q by ring]
  ring

theorem rhoQ_fun_eq_cos (ℓ : ℝ) :
    rhoQ ℓ = fun q => (1 + (ℓ / π) ^ 2 / 2) + (-((ℓ / π) ^ 2 / 2)) * Real.cos (2 * π / ℓ * q) :=
  funext (rhoQ_eq_cos ℓ)

/-- Iterated derivatives of positive order of the `q`-part. -/
theorem iteratedDeriv_rhoQ {n : ℕ} (hn : 0 < n) (ℓ q : ℝ) :
    iteratedDeriv n (rhoQ ℓ) q =
      (-((ℓ / π) ^ 2 / 2)) * ((2 * π / ℓ) ^ n * iteratedDeriv n Real.cos (2 * π / ℓ * q)) := by
  rw [rhoQ_fun_eq_cos, iteratedDeriv_const_add hn,
    iteratedDeriv_const_mul _ (by fun_prop),
    iteratedDeriv_comp_const_mul (Real.contDiff_cos (n := n))]

theorem abs_iteratedDeriv_one_rhoQ_le {ℓ : ℝ} (hℓ : 0 < ℓ) (q : ℝ) :
    |iteratedDeriv 1 (rhoQ ℓ) q| ≤ rhoQ ℓ q := by
  rw [iteratedDeriv_rhoQ one_pos, iteratedDeriv_one, Real.deriv_cos', pow_one]
  have hπ : 0 < π := Real.pi_pos
  have hval : (-((ℓ / π) ^ 2 / 2)) * ((2 * π / ℓ) * -Real.sin (2 * π / ℓ * q)) =
      2 * (ℓ / π * Real.sin (π * q / ℓ)) * Real.cos (π * q / ℓ) := by
    rw [show 2 * π / ℓ * q = 2 * (π * q / ℓ) by ring, Real.sin_two_mul]
    field_simp
  rw [hval]
  set t := ℓ / π * Real.sin (π * q / ℓ)
  have hcos := Real.abs_cos_le_one (π * q / ℓ)
  have ht : rhoQ ℓ q = 1 + t ^ 2 := by
    simp only [rhoQ, t, mul_pow]
  rw [ht, abs_mul, abs_mul]
  have h2t : |(2:ℝ)| * |t| ≤ 1 + t ^ 2 := by
    rw [abs_two]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  calc |(2:ℝ)| * |t| * |Real.cos (π * q / ℓ)| ≤ |(2:ℝ)| * |t| * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
    _ ≤ 1 + t ^ 2 := by rw [mul_one]; exact h2t

theorem abs_iteratedDeriv_add_two_rhoQ_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (k : ℕ) (q : ℝ) :
    |iteratedDeriv (k + 2) (rhoQ ℓ) q| ≤ 2 * (2 * π) ^ k := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hπ : 0 < π := Real.pi_pos
  rw [iteratedDeriv_rhoQ (by omega)]
  have hκ0 : 0 ≤ 2 * π / ℓ := by positivity
  have hκ : 2 * π / ℓ ≤ 2 * π := by
    rw [div_le_iff₀ hℓ0]
    nlinarith
  have hcos := Real.abs_iteratedDeriv_cos_le_one (k + 2) (2 * π / ℓ * q)
  have hconst : (ℓ / π) ^ 2 / 2 * (2 * π / ℓ) ^ 2 = 2 := by
    field_simp
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ / π) ^ 2 / 2),
    abs_of_nonneg (pow_nonneg hκ0 _), pow_add]
  have hk : (2 * π / ℓ) ^ k ≤ (2 * π) ^ k := pow_le_pow_left₀ hκ0 hκ k
  calc (ℓ / π) ^ 2 / 2 * ((2 * π / ℓ) ^ k * (2 * π / ℓ) ^ 2 *
        |iteratedDeriv (k + 2) Real.cos (2 * π / ℓ * q)|)
      ≤ (ℓ / π) ^ 2 / 2 * ((2 * π / ℓ) ^ k * (2 * π / ℓ) ^ 2 * 1) := by
        gcongr
    _ = 2 * (2 * π / ℓ) ^ k := by
        rw [mul_one, mul_comm ((2 * π / ℓ) ^ k), ← mul_assoc, hconst]
    _ ≤ 2 * (2 * π) ^ k := by gcongr

theorem abs_iteratedDeriv_sq_le (n : ℕ) (η : ℝ) :
    |iteratedDeriv n (fun x : ℝ => x ^ 2) η| ≤ 2 * (1 + η ^ 2) := by
  rw [iteratedDeriv_pow]
  rcases n with _ | _ | _ | n
  · simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [abs_of_nonneg (sq_nonneg η)]
    nlinarith [sq_nonneg η]
  · simp only [Nat.descFactorial_one, Nat.cast_ofNat, zero_add, Nat.reduceSub, pow_one]
    rw [abs_mul, abs_two]
    nlinarith [sq_abs η, sq_nonneg (|η| - 1), abs_nonneg η]
  · simp
    nlinarith [sq_nonneg η]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp
    nlinarith [sq_nonneg η]

/-- Composition with the first coordinate does not increase iterated derivative norms. -/
theorem norm_iteratedFDeriv_comp_fst_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ n (fun w : Plane => f w.1) z‖ ≤ |iteratedDeriv n f z.1| := by
  have hcomp : (fun w : Plane => f w.1) = f ∘ (ContinuousLinearMap.fst ℝ ℝ ℝ) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf z
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin n, ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  calc ‖iteratedFDeriv ℝ n f ((ContinuousLinearMap.fst ℝ ℝ ℝ) z)‖ *
        ∏ _i : Fin n, ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖
      ≤ ‖iteratedFDeriv ℝ n f ((ContinuousLinearMap.fst ℝ ℝ ℝ) z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = |iteratedDeriv n f z.1| := by
        rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        rfl

/-- Composition with the second coordinate does not increase iterated derivative norms. -/
theorem norm_iteratedFDeriv_comp_snd_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ n (fun w : Plane => f w.2) z‖ ≤ |iteratedDeriv n f z.2| := by
  have hcomp : (fun w : Plane => f w.2) = f ∘ (ContinuousLinearMap.snd ℝ ℝ ℝ) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf z
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin n, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  calc ‖iteratedFDeriv ℝ n f ((ContinuousLinearMap.snd ℝ ℝ ℝ) z)‖ *
        ∏ _i : Fin n, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖iteratedFDeriv ℝ n f ((ContinuousLinearMap.snd ℝ ℝ ℝ) z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = |iteratedDeriv n f z.2| := by
        rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        rfl

/-- The uniform constants for the derivatives of `ρ_ℓ` itself. -/
def rhoConst (n : ℕ) : ℝ := 2 * (2 * π) ^ n + 3

theorem one_le_rhoConst (n : ℕ) : 1 ≤ rhoConst n := by
  unfold rhoConst
  have : 0 ≤ 2 * (2 * π) ^ n := by positivity
  linarith

theorem rhoConst_mono {i n : ℕ} (h : i ≤ n) : rhoConst i ≤ rhoConst n := by
  unfold rhoConst
  have : (2 * π) ^ i ≤ (2 * π) ^ n :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) h
  linarith

/-- Every derivative of `ρ_ℓ` is bounded by `rhoConst n · ρ_ℓ`, uniformly in `ℓ ≥ 1`. -/
theorem norm_iteratedFDeriv_rho_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (n : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ n (rho ℓ) z‖ ≤ rhoConst n * rho ℓ z := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hρ := one_le_rho ℓ z
  rcases n with _ | n
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (rho_pos ℓ z)]
    have := one_le_rhoConst 0
    nlinarith
  have hsplit : rho ℓ = (fun w : Plane => rhoQ ℓ w.1) + (fun w : Plane => w.2 ^ 2) := by
    funext w
    rfl
  have hQ : ContDiff ℝ ∞ (fun w : Plane => rhoQ ℓ w.1) := (contDiff_rhoQ ℓ).comp contDiff_fst
  have hS : ContDiff ℝ ∞ (fun w : Plane => w.2 ^ 2) := by fun_prop
  have hD : iteratedFDeriv ℝ (n + 1) (rho ℓ) z =
      iteratedFDeriv ℝ (n + 1) (fun w : Plane => rhoQ ℓ w.1) z +
        iteratedFDeriv ℝ (n + 1) (fun w : Plane => w.2 ^ 2) z := by
    rw [hsplit, iteratedFDeriv_add_apply (hQ.contDiffAt.of_le (by exact_mod_cast le_top))
      (hS.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [hD]
  refine (norm_add_le _ _).trans ?_
  have hb := (norm_iteratedFDeriv_comp_snd_le (f := fun x : ℝ => x ^ 2) (by fun_prop) (n + 1) z).trans
    (abs_iteratedDeriv_sq_le (n + 1) z.2)
  have hb' : 2 * (1 + z.2 ^ 2) ≤ 2 * rho ℓ z := by
    have := one_add_sq_le_rho ℓ z
    linarith
  have ha := norm_iteratedFDeriv_comp_fst_le (contDiff_rhoQ ℓ) (n + 1) z
  rcases n with _ | k
  · have ha1 : |iteratedDeriv (0 + 1) (rhoQ ℓ) z.1| ≤ rhoQ ℓ z.1 :=
      abs_iteratedDeriv_one_rhoQ_le hℓ0 z.1
    have := rhoQ_le_rho ℓ z
    have hc : (3:ℝ) ≤ rhoConst (0 + 1) := by
      unfold rhoConst
      have : 0 ≤ 2 * (2 * π) ^ (0 + 1) := by positivity
      linarith
    nlinarith
  · have ha2 : |iteratedDeriv (k + 1 + 1) (rhoQ ℓ) z.1| ≤ 2 * (2 * π) ^ k :=
      abs_iteratedDeriv_add_two_rhoQ_le hℓ k z.1
    have hpow : (2 * π) ^ k ≤ (2 * π) ^ (k + 1 + 1) :=
      pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) (by omega)
    have hpos : 0 ≤ (2 * π) ^ k := by positivity
    unfold rhoConst
    have : 2 * (2 * π) ^ k ≤ 2 * (2 * π) ^ k * rho ℓ z := by nlinarith
    nlinarith

/-- **Claim (c)** (lines 13877–13878: "All fixed derivative ratios of `ρ_ℓ^{±m}` are bounded
uniformly for `ℓ ≥ 1`"). For every order `n` and every real exponent `s` there is a constant
`C`, independent of `ℓ ≥ 1` and of the point, with `‖Dⁿ(ρ_ℓ^s)(z)‖ ≤ C ρ_ℓ(z)^s`. Here `Dⁿ` is
the full `n`-th Fréchet derivative, so the bound covers every mixed partial derivative of
order `n` (`abs_partialMulti_rho_rpow_le`). The exponent is arbitrary, so it covers both
`s = m` and `s = -m`. -/
theorem norm_iteratedFDeriv_rho_rpow_le (n : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ z : Plane,
      ‖iteratedFDeriv ℝ n (fun w => rho ℓ w ^ s) z‖ ≤ C * rho ℓ z ^ s := by
  set Cs : ℝ := ∑ i ∈ Finset.range (n + 1),
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ s) (Ioi 0) 1‖ with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hK0 : 0 ≤ rhoConst n := le_trans zero_le_one (one_le_rhoConst n)
  refine ⟨n ! * Cs * rhoConst n ^ n, by positivity, ?_⟩
  intro ℓ hℓ z
  set c := rho ℓ z with hc_def
  have hc : 0 < c := rho_pos ℓ z
  set f : Plane → ℝ := fun w => c⁻¹ * rho ℓ w with hf_def
  have hfz : f z = 1 := by
    simp only [f]
    exact inv_mul_cancel₀ hc.ne'
  have hfun : (fun w => rho ℓ w ^ s) = fun w => c ^ s • ((fun t : ℝ => t ^ s) ∘ f) w := by
    funext w
    simp only [Function.comp, f, smul_eq_mul]
    rw [Real.mul_rpow (inv_nonneg.2 hc.le) (rho_pos ℓ w).le, Real.inv_rpow hc.le, ← mul_assoc,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  have hf_smooth : ContDiff ℝ ∞ f := contDiff_const.mul (contDiff_rho ℓ)
  have hg : ContDiffOn ℝ n (fun t : ℝ => t ^ s) (Ioi 0) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hcomp : ‖iteratedFDeriv ℝ n ((fun t : ℝ => t ^ s) ∘ f) z‖ ≤
      n ! * Cs * rhoConst n ^ n := by
    apply norm_iteratedFDeriv_comp_le' (t := Ioi 0) (N := n)
    · rintro _ ⟨w, rfl⟩
      simp only [f, mem_Ioi]
      exact mul_pos (inv_pos.2 hc) (rho_pos ℓ w)
    · exact isOpen_Ioi.uniqueDiffOn
    · exact hg
    · exact contDiff_infty.1 hf_smooth n
    · exact le_rfl
    · intro i hi
      rw [hfz, hCs]
      exact Finset.single_le_sum (f := fun i =>
        ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ s) (Ioi 0) 1‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · intro i hi1 hin
      have hfeq : f = fun w => c⁻¹ • rho ℓ w := rfl
      rw [hfeq, iteratedFDeriv_const_smul_apply'
        ((contDiff_rho ℓ).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
      have hb := norm_iteratedFDeriv_rho_le hℓ i z
      calc c⁻¹ * ‖iteratedFDeriv ℝ i (rho ℓ) z‖ ≤ c⁻¹ * (rhoConst i * c) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hc.le)
        _ = rhoConst i := by field_simp
        _ ≤ rhoConst n := rhoConst_mono hin
        _ ≤ rhoConst n ^ i := by
            calc rhoConst n = rhoConst n ^ 1 := (pow_one _).symm
              _ ≤ rhoConst n ^ i := pow_le_pow_right₀ (one_le_rhoConst n) hi1
  have hsmooth_at : ContDiffAt ℝ n ((fun t : ℝ => t ^ s) ∘ f) z := by
    apply ContDiffAt.comp
    · rw [hfz]
      exact Real.contDiffAt_rpow_const_of_ne one_ne_zero
    · exact (contDiff_infty.1 hf_smooth n).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply' hsmooth_at, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hc s)]
  calc c ^ s * ‖iteratedFDeriv ℝ n ((fun t : ℝ => t ^ s) ∘ f) z‖
      ≤ c ^ s * (n ! * Cs * rhoConst n ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hc s).le
    _ = n ! * Cs * rhoConst n ^ n * c ^ s := mul_comm _ _

/-- The two signs `ρ_ℓ^{m}` and `ρ_ℓ^{-m}` named in the manuscript (lines 13877–13878). -/
theorem norm_iteratedFDeriv_rho_rpow_pm_le (n : ℕ) (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ z : Plane,
      ‖iteratedFDeriv ℝ n (fun w => rho ℓ w ^ m) z‖ ≤ C * rho ℓ z ^ m ∧
      ‖iteratedFDeriv ℝ n (fun w => rho ℓ w ^ (-m)) z‖ ≤ C * rho ℓ z ^ (-m) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_iteratedFDeriv_rho_rpow_le n m
  obtain ⟨C₂, hC₂, h₂⟩ := norm_iteratedFDeriv_rho_rpow_le n (-m)
  refine ⟨max C₁ C₂, le_trans hC₁ (le_max_left _ _), fun ℓ hℓ z => ⟨?_, ?_⟩⟩
  · exact (h₁ ℓ hℓ z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_pos_of_pos (rho_pos ℓ z) m).le)
  · exact (h₂ ℓ hℓ z).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_pos_of_pos (rho_pos ℓ z) (-m)).le)

/-! ### Mixed partial derivatives `D^α` -/

/-- The directions of a multi-index `α = (α_q, α_η)`: `α_q` copies of `∂_q` followed by
`α_η` copies of `∂_η`. -/
def multiDir (α : ℕ × ℕ) (j : Fin (α.1 + α.2)) : Plane :=
  if (j : ℕ) < α.1 then (1, 0) else (0, 1)

/-- The classical mixed partial derivative `D^α f = ∂_q^{α_q} ∂_η^{α_η} f`, read off from
the iterated Fréchet derivative. For a `C^∞` function the order of the factors does not
matter. -/
def partialMulti (α : ℕ × ℕ) (f : Plane → ℝ) (z : Plane) : ℝ :=
  iteratedFDeriv ℝ (α.1 + α.2) f z (multiDir α)

theorem norm_multiDir (α : ℕ × ℕ) (j : Fin (α.1 + α.2)) : ‖multiDir α j‖ = 1 := by
  unfold multiDir
  split_ifs <;> simp [Prod.norm_def]

theorem abs_partialMulti_le (α : ℕ × ℕ) (f : Plane → ℝ) (z : Plane) :
    |partialMulti α f z| ≤ ‖iteratedFDeriv ℝ (α.1 + α.2) f z‖ := by
  unfold partialMulti
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ (α.1 + α.2) f z).le_opNorm _).trans ?_
  simp [norm_multiDir]

/-- **Claim (c), multi-index form.** `|D^α(ρ_ℓ^s)| ≤ C_{α,s} ρ_ℓ^s`, uniformly in `ℓ ≥ 1`. -/
theorem abs_partialMulti_rho_rpow_le (α : ℕ × ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ z : Plane,
      |partialMulti α (fun w => rho ℓ w ^ s) z| ≤ C * rho ℓ z ^ s := by
  obtain ⟨C, hC, h⟩ := norm_iteratedFDeriv_rho_rpow_le (α.1 + α.2) s
  exact ⟨C, hC, fun ℓ hℓ z => (abs_partialMulti_le α _ z).trans (h ℓ hℓ z)⟩

end UnforcedLeray.B0656
