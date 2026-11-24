import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# B0281 `background:eq:2.1`: parameters of the exact common unforced background

Unit B0281 of `paper/main.tex`, label `background:eq:2.1`, tex lines 5070–5080
(§`sec:st18-5857`, "Parameters, symmetry, and the result", at the start of
§`sec:background`).

Statement in words. Fix `q₀ = 11/4`. For a small viscosity `ν > 0` the cylinder period is
`c = ν^{-ρ}` with a fixed `ρ > 1/2`, the ring scale is `ε = R⁻¹ = e^{-d/ν}`, where `d`
ranges over a fixed positive compact interval, and the similarity-time period is
`P = 2εc`. A polynomial `P_ν = P(c, ν⁻¹)` has a degree fixed by the finite derivative and
moment budget; its constants may depend on fixed positive margins and on the terminal slow
age, but not on `R`. At fixed parameters all spatial derivative orders are allowed.

Formal setting.
* `q0` is the real number `11/4`.
* `BackgroundParams` records the fixed data: `ρ` with `1/2 < ρ`, and the compact interval
  `dRange = [dMin, dMax]` with `0 < dMin ≤ dMax`. The two symbols `P` of the manuscript are
  kept apart: the period `P = 2εc` is `BackgroundParams.period`, and the generic polynomial
  `P_ν` is the bound predicate `BackgroundParams.PolyBounded`.
* `c`, `eps`, `R`, `period` are functions of `ν` (and `d`). They are meant for `ν > 0`; every
  lemma about them assumes `0 < ν` where that matters (for `ν ≤ 0`, `ν ^ (-ρ)` and `-d/ν` are
  Lean junk values and nothing is claimed about them).
* "`X ≤ P_ν` with degree `k`" is `ViscosityPolyBounded k X`: there is one real polynomial
  `Q` in two variables of total degree `≤ k` with `|X ν d| ≤ Q(c, ν⁻¹)` for every
  sufficiently small `ν > 0` and every `d ∈ dRange`. The polynomial and the smallness
  threshold are chosen before `ν` and `d`, which is the formal content of "constants may
  depend on fixed margins and terminal slow age, not on `R`": `R = e^{d/ν}` is a function of
  `(ν, d)`, so a bound uniform in both cannot depend on it. Everything fixed outside the
  family (margins, `Σ`, the budget) enters through the choice of the family `X` and is free
  to appear in `Q`. `viscosityPolyBounded_iff` proves that this is equivalent to the
  one-constant form `|X| ≤ C (1 + c + ν⁻¹)^k` (`PolyBounded`), and
  `not_polyBounded_R` shows that `R` itself is not of this form, so the restriction is
  not empty.
* "At fixed parameters all spatial derivative orders are allowed" is a convention on later
  estimates, not an arithmetic fact; it has no Lean content here.

Proved facts. The arithmetic stated by the display: `ε = R⁻¹`, `0 < ε < 1 < R`,
`-ν log ε = d`, `0 < c`, `0 < P = 2εc` (`background_eq_2_1`). Supporting facts used
downstream: the closure of `P_ν`-bounds under sums, products and degree increase; `c`,
`ν⁻¹` and `1 + |log ε|` are `P_ν`-bounded of degree one (the last is the bin count at tex
line 10712); the absorption lemma `PolyBounded.absorb` (a `P_ν` loss times `e^{a/ν} ε^θ`
tends to zero uniformly on `dRange` when `a < θ dMin`, the mechanism behind tex lines
5722–5724); `P → 0` uniformly; `ν c² = ν^{1-2ρ} > 1` for `ν < 1` (the role of `ρ > 1/2`).
Finally the final construction `c = ν^{-2}`, `ε = C_* ν^r e^{-d₀/ν}` of
`lem:late-stress-3-10` lies in this family with `ρ = 2` and `dRange = [d₀/2, 3d₀/2]` for
small `ν`, uniformly over a positive compact range of `C_*` and a bounded range of `r`
(tex lines 10810–10812): `exists_lateD_mem`, `eps_lateD`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace UnforcedLeray.B0281

/-! ## The fixed exponent `q₀` -/

/-- The fixed Lebesgue exponent `q₀ = 11/4` of `background:eq:2.1` (tex line 5074). -/
def q0 : ℝ := 11 / 4

theorem q0_eq : q0 = 11 / 4 := rfl

theorem q0_pos : 0 < q0 := by norm_num [q0]

/-- The exponent `8/11` of `R` in `background:eq:2.6` (tex line 5110) is `2/q₀`. -/
theorem two_div_q0 : 2 / q0 = 8 / 11 := by norm_num [q0]

/-- The exponent `3/11` of `ε` in `background:eq:2.6` (tex line 5110) is `1 − 2/q₀`. -/
theorem one_sub_two_div_q0 : 1 - 2 / q0 = 3 / 11 := by norm_num [q0]

/-! ## The fixed data of the family -/

/-- The fixed data of the background family `background:eq:2.1` (tex lines 5074–5077):
the exponent `ρ > 1/2` of the cylinder period `c = ν^{-ρ}` and the fixed positive compact
interval `[dMin, dMax]` over which `d` ranges in `ε = e^{-d/ν}`. -/
structure BackgroundParams where
  /-- The exponent of the cylinder period `c = ν^{-ρ}`. -/
  ρ : ℝ
  /-- Left endpoint of the fixed positive compact `d`-interval. -/
  dMin : ℝ
  /-- Right endpoint of the fixed positive compact `d`-interval. -/
  dMax : ℝ
  half_lt_ρ : 1 / 2 < ρ
  dMin_pos : 0 < dMin
  dMin_le_dMax : dMin ≤ dMax

namespace BackgroundParams

variable (p : BackgroundParams)

/-- The fixed positive compact interval of `d` (tex line 5077). -/
def dRange : Set ℝ := Icc p.dMin p.dMax

theorem ρ_pos : 0 < p.ρ := by have := p.half_lt_ρ; linarith

theorem isCompact_dRange : IsCompact p.dRange := isCompact_Icc

theorem dRange_nonempty : p.dRange.Nonempty := nonempty_Icc.2 p.dMin_le_dMax

theorem dMin_mem_dRange : p.dMin ∈ p.dRange := ⟨le_rfl, p.dMin_le_dMax⟩

theorem pos_of_mem_dRange {d : ℝ} (hd : d ∈ p.dRange) : 0 < d :=
  lt_of_lt_of_le p.dMin_pos hd.1

theorem dMax_pos : 0 < p.dMax := lt_of_lt_of_le p.dMin_pos p.dMin_le_dMax

/-- The cylinder period `c = ν^{-ρ}` (tex line 5074). -/
def c (ν : ℝ) : ℝ := ν ^ (-p.ρ)

theorem c_pos {ν : ℝ} (hν : 0 < ν) : 0 < p.c ν := Real.rpow_pos_of_pos hν _

theorem one_lt_c {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) : 1 < p.c ν :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν hν1 (by linarith [p.ρ_pos])

/-- `ν c² = ν^{1-2ρ}`. -/
theorem nu_mul_c_sq {ν : ℝ} (hν : 0 < ν) : ν * p.c ν ^ 2 = ν ^ (1 - 2 * p.ρ) := by
  have h : (1 : ℝ) - 2 * p.ρ = 1 + (-p.ρ) * ((2 : ℕ) : ℝ) := by push_cast; ring
  rw [h, Real.rpow_add hν, Real.rpow_one, Real.rpow_mul_natCast hν.le, c]

/-- The role of `ρ > 1/2`: `ν c² > 1` for `0 < ν < 1`, so `1/(ν c²) < 1`. -/
theorem one_lt_nu_mul_c_sq {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) : 1 < ν * p.c ν ^ 2 := by
  rw [p.nu_mul_c_sq hν]
  exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν hν1 (by linarith [p.half_lt_ρ])

end BackgroundParams

/-! ## The ring scale `ε = R⁻¹ = e^{-d/ν}` -/

/-- The ring scale `ε = e^{-d/ν}` (tex line 5075). -/
def eps (ν d : ℝ) : ℝ := Real.exp (-d / ν)

/-- The ring radius `R = e^{d/ν}`, so that `ε = R⁻¹` (tex line 5075). -/
def R (ν d : ℝ) : ℝ := Real.exp (d / ν)

/-- `ε = R⁻¹` (tex line 5075). -/
theorem eps_eq_inv_R (ν d : ℝ) : eps ν d = (R ν d)⁻¹ := by
  rw [eps, R, neg_div, Real.exp_neg]

theorem eps_pos (ν d : ℝ) : 0 < eps ν d := Real.exp_pos _

theorem R_pos (ν d : ℝ) : 0 < R ν d := Real.exp_pos _

theorem eps_mul_R (ν d : ℝ) : eps ν d * R ν d = 1 := by
  rw [eps_eq_inv_R, inv_mul_cancel₀ (R_pos ν d).ne']

theorem eps_lt_one {ν d : ℝ} (hν : 0 < ν) (hd : 0 < d) : eps ν d < 1 := by
  rw [eps, ← Real.exp_zero]
  apply Real.exp_lt_exp.2
  rw [neg_div]
  exact neg_lt_zero.2 (div_pos hd hν)

theorem one_lt_R {ν d : ℝ} (hν : 0 < ν) (hd : 0 < d) : 1 < R ν d := by
  rw [R, ← Real.exp_zero]
  exact Real.exp_lt_exp.2 (div_pos hd hν)

theorem log_eps (ν d : ℝ) : Real.log (eps ν d) = -d / ν := Real.log_exp _

/-- `d = -ν log ε`: the parameter `d` is recovered from `ε`. -/
theorem neg_mul_log_eps {ν : ℝ} (hν : ν ≠ 0) (d : ℝ) : -ν * Real.log (eps ν d) = d := by
  rw [log_eps]
  field_simp

/-- Every positive number is `e^{-d/ν}` for `d = -ν log ε`. -/
theorem eps_neg_mul_log {ν e : ℝ} (hν : ν ≠ 0) (he : 0 < e) :
    eps ν (-ν * Real.log e) = e := by
  have h : -(-ν * Real.log e) / ν = Real.log e := by field_simp
  rw [eps, h, Real.exp_log he]

namespace BackgroundParams

variable (p : BackgroundParams)

/-- The similarity-time period `P = 2εc` (tex line 5075). It is the period of the
background in `τ = log t`; the generic polynomial `P_ν` is `PolyBounded` below. -/
def period (ν d : ℝ) : ℝ := 2 * eps ν d * p.c ν

theorem period_pos {ν : ℝ} (hν : 0 < ν) (d : ℝ) : 0 < p.period ν d :=
  mul_pos (mul_pos two_pos (eps_pos ν d)) (p.c_pos hν)

theorem period_eq (ν d : ℝ) : p.period ν d = 2 * ν ^ (-p.ρ) * Real.exp (-d / ν) := by
  rw [period, eps, c]; ring

/-- **`background:eq:2.1` (tex lines 5074–5077).** For `ν > 0` and `d` in the fixed
positive compact interval: `ε = R⁻¹`, `0 < ε < 1 < R`, `-ν log ε = d`, `c > 0`, and the
period `P = 2εc` is positive. -/
theorem background_eq_2_1 {ν d : ℝ} (hν : 0 < ν) (hd : d ∈ p.dRange) :
    eps ν d = (R ν d)⁻¹ ∧ 0 < eps ν d ∧ eps ν d < 1 ∧ 1 < R ν d ∧
      -ν * Real.log (eps ν d) = d ∧ 0 < p.c ν ∧
      p.period ν d = 2 * eps ν d * p.c ν ∧ 0 < p.period ν d :=
  ⟨eps_eq_inv_R ν d, eps_pos ν d, eps_lt_one hν (p.pos_of_mem_dRange hd),
    one_lt_R hν (p.pos_of_mem_dRange hd), neg_mul_log_eps hν.ne' d, p.c_pos hν, rfl,
    p.period_pos hν d⟩

/-! ## Viscosity polynomials `P_ν = P(c, ν⁻¹)` -/

/-- The weight `1 + c + ν⁻¹`; a polynomial in `(c, ν⁻¹)` of degree `k` is bounded by a
constant times its `k`-th power (`abs_eval_le`). -/
def polyWeight (ν : ℝ) : ℝ := 1 + p.c ν + ν⁻¹

theorem one_le_polyWeight {ν : ℝ} (hν : 0 < ν) : 1 ≤ p.polyWeight ν := by
  have h1 := p.c_pos hν
  have h2 := inv_pos.2 hν
  unfold polyWeight
  linarith

theorem polyWeight_pos {ν : ℝ} (hν : 0 < ν) : 0 < p.polyWeight ν :=
  lt_of_lt_of_le one_pos (p.one_le_polyWeight hν)

theorem c_le_polyWeight {ν : ℝ} (hν : 0 < ν) : p.c ν ≤ p.polyWeight ν := by
  have h2 := inv_pos.2 hν
  unfold polyWeight
  linarith

theorem inv_le_polyWeight {ν : ℝ} (hν : 0 < ν) : ν⁻¹ ≤ p.polyWeight ν := by
  have h1 := p.c_pos hν
  unfold polyWeight
  linarith

/-- On `(0,1]`, `1 + c + ν⁻¹ ≤ 3 ν^{-max(ρ,1)}`. -/
theorem polyWeight_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    p.polyWeight ν ≤ 3 * ν ^ (-max p.ρ 1) := by
  have hM1 := le_max_right p.ρ 1
  have hMρ := le_max_left p.ρ 1
  have h1 : (1 : ℝ) ≤ ν ^ (-max p.ρ 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have h2 : p.c ν ≤ ν ^ (-max p.ρ 1) :=
    Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
  have h3 : ν⁻¹ ≤ ν ^ (-max p.ρ 1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
  unfold polyWeight
  linarith

theorem polyWeight_pow_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (k : ℕ) :
    p.polyWeight ν ^ k ≤ 3 ^ k * ν ^ (-(max p.ρ 1 * k)) := by
  calc p.polyWeight ν ^ k ≤ (3 * ν ^ (-max p.ρ 1)) ^ k :=
        pow_le_pow_left₀ (p.polyWeight_pos hν).le (p.polyWeight_le hν hν1) k
    _ = 3 ^ k * (ν ^ (-max p.ρ 1)) ^ k := mul_pow _ _ _
    _ = 3 ^ k * ν ^ (-(max p.ρ 1 * k)) := by
        rw [← neg_mul, Real.rpow_mul_natCast hν.le]

/-- The two variables `(c, ν⁻¹)` of a viscosity polynomial. -/
def polyVars (ν : ℝ) : Fin 2 → ℝ := ![p.c ν, ν⁻¹]

theorem abs_polyVars_le {ν : ℝ} (hν : 0 < ν) (i : Fin 2) :
    |p.polyVars ν i| ≤ p.polyWeight ν := by
  revert i
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [polyVars, Matrix.cons_val_zero]
    rw [abs_of_pos (p.c_pos hν)]
    exact p.c_le_polyWeight hν
  · simp only [polyVars, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [abs_of_pos (inv_pos.2 hν)]
    exact p.inv_le_polyWeight hν

/-- A real polynomial `Q(c, ν⁻¹)` is bounded by the sum of the absolute values of its
coefficients times `(1 + c + ν⁻¹)^{deg Q}`. -/
theorem abs_eval_le {ν : ℝ} (hν : 0 < ν) (Q : MvPolynomial (Fin 2) ℝ) :
    |MvPolynomial.eval (p.polyVars ν) Q| ≤
      (∑ m ∈ Q.support, |Q.coeff m|) * p.polyWeight ν ^ Q.totalDegree := by
  have hB : 1 ≤ p.polyWeight ν := p.one_le_polyWeight hν
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Finset.abs_prod]
  calc ∏ i, |p.polyVars ν i ^ m i| = ∏ i, |p.polyVars ν i| ^ m i := by
        simp_rw [abs_pow]
    _ ≤ ∏ i, p.polyWeight ν ^ m i :=
        Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
          (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (p.abs_polyVars_le hν i) _)
    _ = p.polyWeight ν ^ ∑ i, m i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ p.polyWeight ν ^ Q.totalDegree := by
        refine pow_le_pow_right₀ hB ?_
        have h := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h

/-- The linear form `1 + X₀ + X₁` in the two variables `(c, ν⁻¹)`. -/
def weightLinear : MvPolynomial (Fin 2) ℝ :=
  1 + MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)

/-- The polynomial `C (1 + X₀ + X₁)^k`, whose value at `(c, ν⁻¹)` is `C (1 + c + ν⁻¹)^k`. -/
def weightPoly (C : ℝ) (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C C * weightLinear ^ k

theorem totalDegree_weightLinear_le : weightLinear.totalDegree ≤ 1 := by
  unfold weightLinear
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_one]; exact zero_le_one
    · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_X]

theorem totalDegree_weightPoly_le (C : ℝ) (k : ℕ) : (weightPoly C k).totalDegree ≤ k := by
  unfold weightPoly
  calc (MvPolynomial.C C * weightLinear ^ k).totalDegree
      ≤ (MvPolynomial.C C : MvPolynomial (Fin 2) ℝ).totalDegree +
          (weightLinear ^ k).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k * 1 := by
        refine add_le_add (MvPolynomial.totalDegree_C C).le ?_
        exact (MvPolynomial.totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left _ totalDegree_weightLinear_le)
    _ = k := by rw [zero_add, mul_one]

theorem eval_weightPoly (ν C : ℝ) (k : ℕ) :
    MvPolynomial.eval (p.polyVars ν) (weightPoly C k) = C * p.polyWeight ν ^ k := by
  simp only [weightPoly, weightLinear, polyVars, polyWeight, map_mul, map_pow, map_add,
    map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- **`P_ν = P(c, ν⁻¹)` (tex lines 5077–5079).** `|X| ≤ P_ν` with a viscosity polynomial
of degree at most `k`: one real polynomial `Q` in two variables, of total degree `≤ k`,
with `|X ν d| ≤ Q(c, ν⁻¹)` for all sufficiently small `ν > 0` and all `d ∈ dRange`. The
polynomial and the threshold `ν₀` precede `ν` and `d`, hence do not depend on `R`. -/
def ViscosityPolyBounded (k : ℕ) (X : ℝ → ℝ → ℝ) : Prop :=
  ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ k ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ d ∈ p.dRange, |X ν d| ≤ MvPolynomial.eval (p.polyVars ν) Q

/-- The one-constant form of a `P_ν` bound of degree `k`:
`|X ν d| ≤ C (1 + c + ν⁻¹)^k` for small `ν > 0`, uniformly in `d ∈ dRange`. -/
def PolyBounded (k : ℕ) (X : ℝ → ℝ → ℝ) : Prop :=
  ∃ C ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ d ∈ p.dRange, |X ν d| ≤ C * p.polyWeight ν ^ k

/-- `X ≤ P_ν` for a viscosity polynomial of some fixed degree. -/
def IsPolyBounded (X : ℝ → ℝ → ℝ) : Prop := ∃ k : ℕ, p.PolyBounded k X

/-- The two forms of a degree-`k` viscosity-polynomial bound agree. -/
theorem viscosityPolyBounded_iff {k : ℕ} {X : ℝ → ℝ → ℝ} :
    p.ViscosityPolyBounded k X ↔ p.PolyBounded k X := by
  constructor
  · rintro ⟨Q, hQ, ν₀, hν₀, h⟩
    refine ⟨∑ m ∈ Q.support, |Q.coeff m|, ν₀, hν₀, fun ν hν d hd => ?_⟩
    have hB := p.one_le_polyWeight hν.1
    calc |X ν d| ≤ MvPolynomial.eval (p.polyVars ν) Q := h ν hν d hd
      _ ≤ |MvPolynomial.eval (p.polyVars ν) Q| := le_abs_self _
      _ ≤ (∑ m ∈ Q.support, |Q.coeff m|) * p.polyWeight ν ^ Q.totalDegree :=
          p.abs_eval_le hν.1 Q
      _ ≤ (∑ m ∈ Q.support, |Q.coeff m|) * p.polyWeight ν ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hQ)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · rintro ⟨C, ν₀, hν₀, h⟩
    refine ⟨weightPoly C k, totalDegree_weightPoly_le C k, ν₀, hν₀, fun ν hν d hd => ?_⟩
    rw [p.eval_weightPoly]
    exact h ν hν d hd

theorem PolyBounded.mono {k k' : ℕ} {X : ℝ → ℝ → ℝ} (hX : p.PolyBounded k X)
    (hk : k ≤ k') : p.PolyBounded k' X := by
  obtain ⟨C, ν₀, hν₀, h⟩ := hX
  refine ⟨|C|, ν₀, hν₀, fun ν hν d hd => ?_⟩
  have hB := p.one_le_polyWeight hν.1
  calc |X ν d| ≤ C * p.polyWeight ν ^ k := h ν hν d hd
    _ ≤ |C| * p.polyWeight ν ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans hB) _)
    _ ≤ |C| * p.polyWeight ν ^ k' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hk) (abs_nonneg C)

theorem PolyBounded.add {k₁ k₂ : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : p.PolyBounded k₁ X)
    (hY : p.PolyBounded k₂ Y) :
    p.PolyBounded (max k₁ k₂) (fun ν d => X ν d + Y ν d) := by
  obtain ⟨C₁, ν₁, hν₁, h₁⟩ := hX.mono p (le_max_left k₁ k₂)
  obtain ⟨C₂, ν₂, hν₂, h₂⟩ := hY.mono p (le_max_right k₁ k₂)
  refine ⟨C₁ + C₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν d hd => ?_⟩
  have hν1 : ν ∈ Ioc 0 ν₁ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioc 0 ν₂ := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  calc |X ν d + Y ν d| ≤ |X ν d| + |Y ν d| := abs_add_le _ _
    _ ≤ (C₁ + C₂) * p.polyWeight ν ^ max k₁ k₂ := by
        rw [add_mul]; exact add_le_add (h₁ ν hν1 d hd) (h₂ ν hν2 d hd)

theorem PolyBounded.mul {k₁ k₂ : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : p.PolyBounded k₁ X)
    (hY : p.PolyBounded k₂ Y) :
    p.PolyBounded (k₁ + k₂) (fun ν d => X ν d * Y ν d) := by
  obtain ⟨C₁, ν₁, hν₁, h₁⟩ := hX
  obtain ⟨C₂, ν₂, hν₂, h₂⟩ := hY
  refine ⟨C₁ * C₂, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν d hd => ?_⟩
  have hν1 : ν ∈ Ioc 0 ν₁ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioc 0 ν₂ := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  have a := h₁ ν hν1 d hd
  have b := h₂ ν hν2 d hd
  rw [abs_mul, pow_add]
  calc |X ν d| * |Y ν d|
      ≤ (C₁ * p.polyWeight ν ^ k₁) * (C₂ * p.polyWeight ν ^ k₂) :=
        mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
    _ = C₁ * C₂ * (p.polyWeight ν ^ k₁ * p.polyWeight ν ^ k₂) := by ring

theorem polyBounded_const (K : ℝ) : p.PolyBounded 0 (fun _ _ => K) :=
  ⟨|K|, 1, one_pos, fun ν _ d _ => by rw [pow_zero, mul_one]⟩

theorem polyBounded_c : p.PolyBounded 1 (fun ν _ => p.c ν) :=
  ⟨1, 1, one_pos, fun ν hν d _ => by
    rw [abs_of_pos (p.c_pos hν.1), pow_one, one_mul]
    exact p.c_le_polyWeight hν.1⟩

theorem polyBounded_inv : p.PolyBounded 1 (fun ν _ => ν⁻¹) :=
  ⟨1, 1, one_pos, fun ν hν d _ => by
    rw [abs_of_pos (inv_pos.2 hν.1), pow_one, one_mul]
    exact p.inv_le_polyWeight hν.1⟩

/-- `1 + |log ε|` is a viscosity polynomial of degree one on the family (used for the bin
count `C_δ(1 + |log ε|)` at tex lines 10711–10713). -/
theorem polyBounded_one_add_abs_log_eps :
    p.PolyBounded 1 (fun ν d => 1 + |Real.log (eps ν d)|) := by
  refine ⟨1 + p.dMax, 1, one_pos, fun ν hν d hd => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hd0 : 0 < d := p.pos_of_mem_dRange hd
  have hB := p.one_le_polyWeight hν0
  have hinv := p.inv_le_polyWeight hν0
  have hinvpos : 0 < ν⁻¹ := inv_pos.2 hν0
  have hdmax : d ≤ p.dMax := hd.2
  have hdM := p.dMax_pos
  have habs : |-d / ν| = d * ν⁻¹ := by
    rw [neg_div, abs_neg, abs_of_pos (div_pos hd0 hν0), div_eq_mul_inv]
  show abs (1 + |Real.log (eps ν d)|) ≤ (1 + p.dMax) * p.polyWeight ν ^ 1
  rw [log_eps, habs, abs_of_pos (by positivity), pow_one]
  have h1 : d * ν⁻¹ ≤ p.dMax * ν⁻¹ := mul_le_mul_of_nonneg_right hdmax hinvpos.le
  have h2 : p.dMax * ν⁻¹ ≤ p.dMax * p.polyWeight ν := mul_le_mul_of_nonneg_left hinv hdM.le
  nlinarith

/-! ## Absorption of polynomial losses by exponential margins -/

/-- For `b > 0`, `K ν^{-s} e^{-b/ν}` is below any `η > 0` for all small `ν > 0`. -/
theorem _root_.UnforcedLeray.B0281.exists_mul_rpow_mul_exp_lt (K s b : ℝ) (hb : 0 < b)
    {η : ℝ} (hη : 0 < η) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ν₁ ≤ 1 ∧ ∀ ν ∈ Ioc 0 ν₁, K * ν ^ (-s) * Real.exp (-b / ν) < η := by
  have hK : 0 < |K| + 1 := by positivity
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb
  have hev : ∀ᶠ x : ℝ in atTop, x ^ s * Real.exp (-b * x) < η / (|K| + 1) :=
    (tendsto_order.1 hlim).2 _ (div_pos hη hK)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hM : 0 < max N 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max N 1)⁻¹, inv_pos.2 hM, inv_le_one_of_one_le₀ (le_max_right _ _),
    fun ν hν => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hx : N ≤ ν⁻¹ := (le_max_left N 1).trans ((le_inv_comm₀ hν0 hM).1 hν.2)
  have h := hN ν⁻¹ hx
  rw [Real.inv_rpow hν0.le, ← Real.rpow_neg hν0.le, ← div_eq_mul_inv] at h
  have hy : 0 ≤ ν ^ (-s) * Real.exp (-b / ν) := by positivity
  calc K * ν ^ (-s) * Real.exp (-b / ν) = K * (ν ^ (-s) * Real.exp (-b / ν)) := by ring
    _ ≤ (|K| + 1) * (ν ^ (-s) * Real.exp (-b / ν)) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hy
    _ < (|K| + 1) * (η / (|K| + 1)) := mul_lt_mul_of_pos_left h hK
    _ = η := by field_simp

/-- **Absorption.** A `P_ν` loss times `e^{a/ν} ε^θ` tends to zero uniformly on the
compact `d`-interval whenever `θ ≥ 0` and `a < θ dMin`. This is how the polynomial
constants are absorbed by strict exponential margins, for example in the contraction
condition `background:eq:2.43` "for small `ν`, uniformly on the fixed compact
`d`-interval" (tex lines 5722–5724). -/
theorem PolyBounded.absorb {k : ℕ} {X : ℝ → ℝ → ℝ} (hX : p.PolyBounded k X) {a θ : ℝ}
    (hθ : 0 ≤ θ) (ha : a < θ * p.dMin) {η : ℝ} (hη : 0 < η) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioc 0 ν₁, ∀ d ∈ p.dRange,
      |X ν d| * Real.exp (a / ν) * eps ν d ^ θ < η := by
  obtain ⟨C, ν₀, hν₀, hC⟩ := hX
  obtain ⟨ν₁, hν₁, hν₁1, h⟩ := exists_mul_rpow_mul_exp_lt (|C| * 3 ^ k)
    (max p.ρ 1 * k) (θ * p.dMin - a) (by linarith) hη
  refine ⟨min ν₀ ν₁, lt_min hν₀ hν₁, fun ν hν d hd => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hνν₀ : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hνν₁ : ν ≤ ν₁ := hν.2.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hνν₁.trans hν₁1
  have hB := p.one_le_polyWeight hν0
  have hXb : |X ν d| ≤ |C| * (3 ^ k * ν ^ (-(max p.ρ 1 * k))) :=
    (hC ν ⟨hν0, hνν₀⟩ d hd).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans hB) _)).trans
        (mul_le_mul_of_nonneg_left (p.polyWeight_pow_le hν0 hν1 k) (abs_nonneg C)))
  have hE : Real.exp (a / ν) * eps ν d ^ θ ≤ Real.exp (-(θ * p.dMin - a) / ν) := by
    rw [eps, ← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hθd : θ * p.dMin ≤ θ * d := mul_le_mul_of_nonneg_left hd.1 hθ
    have e1 : a / ν + -d / ν * θ = (a - θ * d) * ν⁻¹ := by ring
    have e2 : -(θ * p.dMin - a) / ν = (a - θ * p.dMin) * ν⁻¹ := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hν0.le)
  have hEnn : 0 ≤ Real.exp (a / ν) * eps ν d ^ θ :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (eps_pos ν d).le θ)
  calc |X ν d| * Real.exp (a / ν) * eps ν d ^ θ
      = |X ν d| * (Real.exp (a / ν) * eps ν d ^ θ) := by ring
    _ ≤ (|C| * (3 ^ k * ν ^ (-(max p.ρ 1 * k)))) * Real.exp (-(θ * p.dMin - a) / ν) :=
        mul_le_mul hXb hE hEnn (by positivity)
    _ = |C| * 3 ^ k * ν ^ (-(max p.ρ 1 * k)) * Real.exp (-(θ * p.dMin - a) / ν) := by ring
    _ < η := h ν ⟨hν0, hνν₁⟩

/-- The period `P = 2εc` tends to zero as `ν ↓ 0`, uniformly on the `d`-interval. -/
theorem exists_period_lt {η : ℝ} (hη : 0 < η) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioc 0 ν₁, ∀ d ∈ p.dRange, p.period ν d < η := by
  have hX := (p.polyBounded_const 2).mul p p.polyBounded_c
  obtain ⟨ν₁, hν₁, h⟩ := hX.absorb p (a := 0) (θ := 1) zero_le_one
    (by rw [one_mul]; exact p.dMin_pos) hη
  refine ⟨ν₁, hν₁, fun ν hν d hd => ?_⟩
  have h' := h ν hν d hd
  rw [zero_div, Real.exp_zero, mul_one, Real.rpow_one,
    abs_of_pos (mul_pos two_pos (p.c_pos hν.1))] at h'
  calc p.period ν d = 2 * p.c ν * eps ν d := by rw [period]; ring
    _ < η := h'

/-- The ring radius `R = e^{d/ν}` is not bounded by any viscosity polynomial uniformly on
the family: "constants ... not on `R`" (tex line 5079) is a genuine restriction. -/
theorem not_polyBounded_R (k : ℕ) : ¬ p.PolyBounded k (fun ν d => R ν d) := by
  rintro ⟨C, ν₀, hν₀, hC⟩
  have hX : p.PolyBounded k (fun ν _ => C * p.polyWeight ν ^ k) :=
    ⟨|C|, 1, one_pos, fun ν hν d _ => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (p.polyWeight_pos hν.1).le _)]⟩
  obtain ⟨ν₁, hν₁, h⟩ := hX.absorb p (a := 0) (θ := 1) zero_le_one
    (by rw [one_mul]; exact p.dMin_pos) one_pos
  have hν : min ν₀ ν₁ ∈ Ioc 0 ν₀ := ⟨lt_min hν₀ hν₁, min_le_left _ _⟩
  have hν' : min ν₀ ν₁ ∈ Ioc 0 ν₁ := ⟨lt_min hν₀ hν₁, min_le_right _ _⟩
  have h1 := h _ hν' p.dMin p.dMin_mem_dRange
  have h2 := hC _ hν p.dMin p.dMin_mem_dRange
  have hR := R_pos (min ν₀ ν₁) p.dMin
  rw [zero_div, Real.exp_zero, mul_one, Real.rpow_one, eps_eq_inv_R, ← div_eq_mul_inv,
    div_lt_one hR] at h1
  rw [abs_of_pos hR] at h2
  have := le_abs_self (C * p.polyWeight (min ν₀ ν₁) ^ k)
  linarith

end BackgroundParams

/-! ## The final construction lies in the family -/

/-- The fixed data of the final construction of `lem:late-stress-3-10` (tex lines
10691–10693): `c = ν^{-2}` (`ρ = 2`) and the `d`-interval `[d₀/2, 3d₀/2]` (tex line 10812). -/
def lateParams (d0 : ℝ) (hd0 : 0 < d0) : BackgroundParams where
  ρ := 2
  dMin := d0 / 2
  dMax := 3 * d0 / 2
  half_lt_ρ := by norm_num
  dMin_pos := by positivity
  dMin_le_dMax := by linarith

theorem lateParams_c {d0 : ℝ} (hd0 : 0 < d0) {ν : ℝ} (hν : 0 < ν) :
    (lateParams d0 hd0).c ν = (ν ^ 2)⁻¹ := by
  simp only [BackgroundParams.c, lateParams]
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- The ring scale `ε = C_* ν^r e^{-d₀/ν}` of `lem:late-stress-3-10` (tex line 10692). -/
def lateEps (d0 Cs r ν : ℝ) : ℝ := Cs * ν ^ r * Real.exp (-d0 / ν)

/-- `d₀ − ν log C_* − r ν log ν` (tex line 10811). -/
def lateD (d0 Cs r ν : ℝ) : ℝ := d0 - ν * Real.log Cs - r * ν * Real.log ν

theorem lateEps_pos {d0 Cs r ν : ℝ} (hCs : 0 < Cs) (hν : 0 < ν) : 0 < lateEps d0 Cs r ν :=
  mul_pos (mul_pos hCs (Real.rpow_pos_of_pos hν r)) (Real.exp_pos _)

/-- `−ν log ε = d₀ − ν log C_* − r ν log ν` (tex line 10811). -/
theorem neg_mul_log_lateEps (d0 r : ℝ) {Cs ν : ℝ} (hCs : 0 < Cs) (hν : 0 < ν) :
    -ν * Real.log (lateEps d0 Cs r ν) = lateD d0 Cs r ν := by
  unfold lateEps lateD
  rw [Real.log_mul (mul_pos hCs (Real.rpow_pos_of_pos hν r)).ne' (Real.exp_pos _).ne',
    Real.log_mul hCs.ne' (Real.rpow_pos_of_pos hν r).ne', Real.log_rpow hν, Real.log_exp]
  field_simp
  ring

/-- The final ring scale is the family's `ε = e^{-d/ν}` at `d = d₀ − ν log C_* − r ν log ν`. -/
theorem eps_lateD (d0 r : ℝ) {Cs ν : ℝ} (hCs : 0 < Cs) (hν : 0 < ν) :
    eps ν (lateD d0 Cs r ν) = lateEps d0 Cs r ν := by
  rw [← neg_mul_log_lateEps d0 r hCs hν, eps_neg_mul_log hν.ne' (lateEps_pos hCs hν)]

/-- `|ν log ν| ≤ 2√ν` on `(0,1]`. -/
theorem abs_mul_log_le_two_sqrt {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    |ν * Real.log ν| ≤ 2 * Real.sqrt ν := by
  have hlog : Real.log ν ≤ 0 := Real.log_nonpos hν.le hν1
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h1 : Real.log (Real.sqrt ν)⁻¹ ≤ (Real.sqrt ν)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at h1
  have h2 : Real.log ν = 2 * Real.log (Real.sqrt ν) := by
    conv_lhs => rw [← Real.mul_self_sqrt hν.le]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  have h3 : ν * (Real.sqrt ν)⁻¹ = Real.sqrt ν := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hs.ne']
    exact Real.mul_self_sqrt hν.le
  have h4 : ν * (-Real.log (Real.sqrt ν)) ≤ ν * ((Real.sqrt ν)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left h1 hν.le
  have hneg : ν * Real.log ν ≤ 0 := by nlinarith
  rw [abs_of_nonpos hneg, h2]
  nlinarith

/-- **The final construction lies in the family (tex lines 10810–10812).** Fix `d₀ > 0`, a
positive compact range `[Cmin, Cmax]` for `C_*` and a bounded range `[-rmax, rmax]` for `r`.
For all small `ν > 0`, uniformly on these ranges, `d₀ − ν log C_* − r ν log ν` lies in
`[d₀/2, 3d₀/2]`; together with `eps_lateD` and `lateParams_c`, the choice
`c = ν^{-2}`, `ε = C_* ν^r e^{-d₀/ν}` is an instance of `background:eq:2.1`. -/
theorem exists_lateD_mem (d0 : ℝ) (hd0 : 0 < d0) (Cmin Cmax rmax : ℝ) (hCmin : 0 < Cmin) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioc 0 ν₁, ∀ Cs ∈ Icc Cmin Cmax, ∀ r ∈ Icc (-rmax) rmax,
      lateD d0 Cs r ν ∈ (lateParams d0 hd0).dRange := by
  set L : ℝ := |Real.log Cmin| + |Real.log Cmax| with hL
  set K : ℝ := L + 2 * |rmax| + 1 with hK
  have hLnn : 0 ≤ L := by positivity
  have hKpos : 0 < K := by positivity
  set δ : ℝ := d0 / (2 * K) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨min 1 (δ ^ 2), lt_min one_pos (by positivity), fun ν hν Cs hCs r hr => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hνδ : ν ≤ δ ^ 2 := hν.2.trans (min_le_right _ _)
  have hs0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
  have hsδ : Real.sqrt ν ≤ δ :=
    calc Real.sqrt ν ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hνδ
      _ = δ := Real.sqrt_sq hδpos.le
  have hs1 : Real.sqrt ν ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hν1
  have hνs : ν ≤ Real.sqrt ν :=
    calc ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν0.le).symm
      _ ≤ Real.sqrt ν * 1 := mul_le_mul_of_nonneg_left hs1 hs0
      _ = Real.sqrt ν := mul_one _
  have hCs0 : 0 < Cs := hCmin.trans_le hCs.1
  have hlogC : |Real.log Cs| ≤ L := by
    have h1 := Real.log_le_log hCmin hCs.1
    have h2 := Real.log_le_log hCs0 hCs.2
    have h3 := neg_abs_le (Real.log Cmin)
    have h4 := le_abs_self (Real.log Cmax)
    have h5 := abs_nonneg (Real.log Cmax)
    have h6 := abs_nonneg (Real.log Cmin)
    rw [abs_le]
    constructor <;> linarith
  have hr' : |r| ≤ |rmax| := by
    have h1 := le_abs_self rmax
    have h2 := neg_abs_le rmax
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hA : |ν * Real.log Cs| ≤ L * Real.sqrt ν := by
    rw [abs_mul, abs_of_pos hν0]
    calc ν * |Real.log Cs| ≤ Real.sqrt ν * L := mul_le_mul hνs hlogC (abs_nonneg _) hs0
      _ = L * Real.sqrt ν := mul_comm _ _
  have hB : |r * ν * Real.log ν| ≤ 2 * |rmax| * Real.sqrt ν := by
    rw [mul_assoc, abs_mul]
    calc |r| * |ν * Real.log ν| ≤ |rmax| * (2 * Real.sqrt ν) :=
          mul_le_mul hr' (abs_mul_log_le_two_sqrt hν0 hν1) (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |rmax| * Real.sqrt ν := by ring
  have hKs : K * Real.sqrt ν ≤ d0 / 2 :=
    calc K * Real.sqrt ν ≤ K * δ := mul_le_mul_of_nonneg_left hsδ hKpos.le
      _ = d0 / 2 := by rw [hδ]; field_simp
  have hLK : L * Real.sqrt ν + 2 * |rmax| * Real.sqrt ν ≤ K * Real.sqrt ν := by
    rw [hK]; nlinarith
  have habs : |lateD d0 Cs r ν - d0| ≤ d0 / 2 := by
    have e : lateD d0 Cs r ν - d0 = -(ν * Real.log Cs) + -(r * ν * Real.log ν) := by
      unfold lateD; ring
    rw [e]
    calc |-(ν * Real.log Cs) + -(r * ν * Real.log ν)|
        ≤ |-(ν * Real.log Cs)| + |-(r * ν * Real.log ν)| := abs_add_le _ _
      _ = |ν * Real.log Cs| + |r * ν * Real.log ν| := by rw [abs_neg, abs_neg]
      _ ≤ d0 / 2 := by linarith
  rw [abs_le] at habs
  show lateD d0 Cs r ν ∈ Icc (d0 / 2) (3 * d0 / 2)
  constructor <;> linarith [habs.1, habs.2]

/-- **The final choice as an instance of `background:eq:2.1`.** For small `ν > 0`,
uniformly over `C_* ∈ [Cmin, Cmax]` and `r ∈ [-rmax, rmax]`, the choice
`c = ν^{-2}`, `ε = C_* ν^r e^{-d₀/ν}` is `c = ν^{-ρ}`, `ε = e^{-d/ν}` with `ρ = 2` and
`d ∈ [d₀/2, 3d₀/2]` (tex lines 10691–10693 and 10810–10812). -/
theorem late_choice_mem_family (d0 : ℝ) (hd0 : 0 < d0) (Cmin Cmax rmax : ℝ)
    (hCmin : 0 < Cmin) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν ∈ Ioc 0 ν₁, ∀ Cs ∈ Icc Cmin Cmax, ∀ r ∈ Icc (-rmax) rmax,
      ∃ d ∈ (lateParams d0 hd0).dRange,
        eps ν d = Cs * ν ^ r * Real.exp (-d0 / ν) ∧ (lateParams d0 hd0).c ν = (ν ^ 2)⁻¹ := by
  obtain ⟨ν₁, hν₁, h⟩ := exists_lateD_mem d0 hd0 Cmin Cmax rmax hCmin
  refine ⟨ν₁, hν₁, fun ν hν Cs hCs r hr => ⟨lateD d0 Cs r ν, h ν hν Cs hCs r hr, ?_, ?_⟩⟩
  · exact eps_lateD d0 r (hCmin.trans_le hCs.1) hν.1
  · exact lateParams_c hd0 hν.1

end UnforcedLeray.B0281
