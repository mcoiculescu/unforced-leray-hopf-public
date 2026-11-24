import UnforcedLeray.Short.PartIIIa.StressInputs
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Part III-a, `PartIII-a:T23/5/org`: leaves of the inlet transverse tail

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`: "Increasing `C_⊥` absorbs the fixed weights, derivative budgets, and
the finite inlet's stream tail") and lines 2347-2366 (the inlet stream: "the Gaussian angular-two
eigenstream is a harmonic quadrupole plus a Gaussian remainder outside a fixed core. Periodizing
its harmonic part uses only `∑_n (q+nc+iη)^{-2} = (π/c)² csc²(π(q+iη)/c)` ... Thus the actual
periodized stream and every fixed derivative have exponential transverse decay, with polynomial
`c` costs"; the normalized lift `e_ε = e₀ + εe₁`, `e₀ = χ(-ψ_η, ψ_q)`,
`e₁ = (0, (χ - 2sχ')ψ - χηψ_η)`).

Objects (no free predicates): the inlet columns `p.inlet i = 𝒩_v (ringStreamProfile R (χψ_i))`
with `ψ_0 = 2 Re P_c q`, `ψ_1 = -2 Im P_c q`, `P_c q = periodicStream p.mode p.c`
(`Cons/L2/BackgroundConcrete/Fields.lean`, `frozenStream`, `cutStream`, `inletProfile`, `inlet`),
the chart coefficient `chartCoeff`, the weight `transWeight` (`StressSpaces.lean`).

## The two leaves

* `PeriodicStreamTail` (SP 2349-2358): for the growing eigenvector `q`, the periodized stream
  `P_c q` and its first derivative, times any polynomial weight `(1+|η|)^m`, are
  `≤ C c^k e^{-a|η|/c}` on `|η| ≥ c ≥ 1` (exponential transverse decay with polynomial `c` costs).
* `InletChartFromStream` (SP 2360-2366): the chart coefficient of an inlet column is bounded by the
  inlet stream and its gradient, `|v_i| ≤ K(1 + ε(1+|η|))(|ψ_i| + |∇ψ_i|)` (the cutoff `χ` and
  `sχ'` are bounded uniformly in `H`).

## The free-mode defect and the corrected target

`InletTransverseTail` (`StressInputs.lean`) chooses `C_⊥, ν₀` before `∀ p`, while `p.mode` is a
free field of `Params`; the inlet is linear in `p.mode`, so the statement is false for
`p.mode := M • q`, `M → ∞` (recorded as `ORG:stmt/PartIII-a/ParamsWideQuantifiers`, which
restates it with the slow data fixed before the constants, in the pattern of
`IIb.StrongRegularity`). `InletTransverseTailQ` below is that corrected statement, verbatim in the
prescribed pattern: `∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
Blueprint.Planar.IsGrowingEigenpair lam q →` in front and `p.ageCut = Sig → p.mode = q →` after
`p.ν ≤ ν₀ →`. Once `InletTransverseTail` is restated so, `inletTransverseTail_of ha hb` proves it.

## Proved here (no `sorry`)

* `inletTransverseTail_of : PeriodicStreamTail → InletChartFromStream → InletTransverseTailQ`:
  on the tail `√s ≤ √(ε^{-b}) < |η|`, `W ≤ (1+|η|)^{⌈m_Z⌉}`, `ε ≤ 1`, `c = ν^{-2}`;
  `|η| > C_⊥ c/ν` gives `e^{-a|η|/c} ≤ e^{-(D+1)/ν}` for `C_⊥ ≥ (D+1)/a`, and the polynomial
  `4KC ν^{-2k}` is absorbed by `e^{1/ν}` for small `ν` (`inletTail_poly_le_exp_inv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal Nat

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb UnforcedLeray.Blueprint

/-! ## The leaves -/

/-- **(a) Exponential transverse decay of the periodized eigenstream** (SP 2349-2358: "the
Gaussian angular-two eigenstream is a harmonic quadrupole plus a Gaussian remainder outside a fixed
core. Periodizing its harmonic part uses only `∑_n (q+nc+iη)^{-2} = (π/c)² csc²(π(q+iη)/c)` ...
the actual periodized stream and every fixed derivative have exponential transverse decay, with
polynomial `c` costs"). For the growing eigenvector `q` (G1) and every weight power `m` there are
a rate `a > 0` and a polynomial `C c^k` such that, for every period `c ≥ 1` and every point
`x = (ξ, η)` with `|η| ≥ c` (outside every periodized core), `P_c q = periodicStream q c` is
differentiable at `x` and
`(1+|η|)^m (|P_c q(x)| + ‖D P_c q(x)‖) ≤ C c^k e^{-a|η|/c}`. -/
def PeriodicStreamTail : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
  ∀ m : ℕ, ∃ (a C : ℝ) (k : ℕ), 0 < a ∧
    ∀ c : ℝ, 1 ≤ c → ∀ x : ℝ × ℝ, c ≤ |x.2| →
      DifferentiableAt ℝ (periodicStream q c) x ∧
      (1 + |x.2|) ^ m * (‖periodicStream q c x‖ + ‖fderiv ℝ (periodicStream q c) x‖) ≤
        C * c ^ k * Real.exp (-(a * |x.2| / c))

/-- **(b) The inlet chart coefficient is controlled by the inlet stream** (SP 2360-2366: the
normalized lift `e_ε = e₀ + εe₁`, `e₀ = χ(-ψ_η, ψ_q)`, `e₁ = (0, (χ - 2sχ')ψ - χηψ_η)`; the
coefficient `v = s^{-1/2}V`, SP 2711). There is `K ≥ 0` such that for every level `p`, column `i`
and chart point with `s > 0` at which the frozen stream `ψ_i = p.frozenStream i` is
differentiable, `|v_i| ≤ K (1 + ε(1+|η|)) (|ψ_i| + ‖Dψ_i‖)` (here `0 ≤ χ ≤ 1` and
`|sχ'(s)|` is bounded uniformly in the cutoff age `H`). -/
def InletChartFromStream : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : Params) (i : Fin 2) (pt : ℝ × (ℝ × ℝ)), 0 < pt.1 →
    DifferentiableAt ℝ (p.frozenStream i) pt.2 →
    ‖chartCoeff p.R (p.inlet i) pt‖ ≤
      K * (1 + p.ε * (1 + |pt.2.2|)) *
        (|p.frozenStream i pt.2| + ‖fderiv ℝ (p.frozenStream i) pt.2‖)

/-- **The inlet transverse tail with the slow data fixed** (SP 2739-2756, "Increasing `C_⊥`
absorbs ... the finite inlet's stream tail"): `InletTransverseTail` of `StressInputs.lean` with
`∀ Sig lam q, 0 < Sig → IsGrowingEigenpair lam q →` before the constants and
`p.ageCut = Sig → p.mode = q →` after `p.ν ≤ ν₀ →` (the pattern of `IIb.StrongRegularity`; the
inlet is the fixed Gaussian angular-two eigenstream, SP 2347-2358, 2385-2387). -/
def InletTransverseTailQ : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2,
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          Real.exp (-D / p.ν)

/-! ## Elementary helpers -/

/-- Polynomial costs are absorbed by `e^{1/ν}`: `A ν^{-n} ≤ e^{1/ν}` for `0 < ν ≤ ν₁`. -/
theorem inletTail_poly_le_exp_inv (A : ℝ) (n : ℕ) : ∃ ν₁ : ℝ, 0 < ν₁ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ → A * (ν⁻¹) ^ n ≤ Real.exp (1 / ν) := by
  set B : ℝ := max (A * ((n + 1)! : ℝ)) 1 with hB
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  refine ⟨B⁻¹, inv_pos.2 hBpos, fun ν hν hνle => ?_⟩
  have hxpos : 0 < ν⁻¹ := inv_pos.2 hν
  have hxB : B ≤ ν⁻¹ := (le_inv_comm₀ hν hBpos).1 hνle
  have hfac : (0 : ℝ) < ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hAx : A ≤ ν⁻¹ / ((n + 1)! : ℝ) := by
    rw [le_div_iff₀ hfac]
    exact le_trans (le_max_left _ _) hxB
  have hexp := Real.pow_div_factorial_le_exp (x := ν⁻¹) hxpos.le (n + 1)
  rw [one_div]
  calc A * (ν⁻¹) ^ n ≤ ν⁻¹ / ((n + 1)! : ℝ) * (ν⁻¹) ^ n :=
        mul_le_mul_of_nonneg_right hAx (pow_nonneg hxpos.le n)
    _ = (ν⁻¹) ^ (n + 1) / ((n + 1)! : ℝ) := by rw [pow_succ]; ring
    _ ≤ Real.exp ν⁻¹ := hexp

theorem inletTail_transWeight_nonneg (mZ : ℝ) (pt : ℝ × (ℝ × ℝ)) : 0 ≤ transWeight mZ pt :=
  Real.rpow_nonneg (by positivity) _

/-- `W = ⟨η/√(1+s)⟩^{m_Z} ≤ (1+|η|)^{⌈m_Z⌉}` for `s ≥ 0`, `m_Z ≥ 0`. -/
theorem inletTail_transWeight_le {mZ : ℝ} (hmZ : 0 ≤ mZ) {pt : ℝ × (ℝ × ℝ)} (hs : 0 ≤ pt.1) :
    transWeight mZ pt ≤ (1 + |pt.2.2|) ^ (⌈mZ⌉₊) := by
  have h1s : 1 ≤ 1 + pt.1 := by linarith
  have hsq : (pt.2.2 / Real.sqrt (1 + pt.1)) ^ 2 ≤ pt.2.2 ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
    exact div_le_self (sq_nonneg _) h1s
  have hbase : 1 + (pt.2.2 / Real.sqrt (1 + pt.1)) ^ 2 ≤ (1 + |pt.2.2|) ^ 2 := by
    have : pt.2.2 ^ 2 = |pt.2.2| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg pt.2.2]
  have hη1 : 1 ≤ 1 + |pt.2.2| := by linarith [abs_nonneg pt.2.2]
  unfold transWeight
  calc (1 + (pt.2.2 / Real.sqrt (1 + pt.1)) ^ 2) ^ (mZ / 2)
      ≤ ((1 + |pt.2.2|) ^ 2) ^ (mZ / 2) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith)
    _ = (1 + |pt.2.2|) ^ mZ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        congr 1
        push_cast
        ring
    _ ≤ (1 + |pt.2.2|) ^ (⌈mZ⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hη1 (Nat.le_ceil mZ)
    _ = (1 + |pt.2.2|) ^ (⌈mZ⌉₊) := Real.rpow_natCast _ _

/-- A real part (or imaginary part) of a complex stream, times `a`, `|a| ≤ 2`. -/
theorem inletTail_clm_aux (P : ℝ × ℝ → ℂ) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (a : ℝ)
    (ha : |a| ≤ 2) {x : ℝ × ℝ} (hP : DifferentiableAt ℝ P x) :
    DifferentiableAt ℝ (fun y => a * L (P y)) x ∧
      |a * L (P x)| + ‖fderiv ℝ (fun y => a * L (P y)) x‖ ≤
        2 * (‖P x‖ + ‖fderiv ℝ P x‖) := by
  have hd : HasFDerivAt (fun y => a * L (P y)) (a • (L.comp (fderiv ℝ P x))) x :=
    (L.hasFDerivAt.comp x hP.hasFDerivAt).const_mul a
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  have hLP : |L (P x)| ≤ ‖P x‖ := by
    have h := L.le_opNorm (P x)
    rw [Real.norm_eq_abs] at h
    nlinarith [norm_nonneg (P x)]
  have h1 : |a * L (P x)| ≤ 2 * ‖P x‖ := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg (L (P x)), norm_nonneg (P x)]
  have hLD : ‖L.comp (fderiv ℝ P x)‖ ≤ ‖fderiv ℝ P x‖ := by
    calc ‖L.comp (fderiv ℝ P x)‖ ≤ ‖L‖ * ‖fderiv ℝ P x‖ := L.opNorm_comp_le _
      _ ≤ 1 * ‖fderiv ℝ P x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = ‖fderiv ℝ P x‖ := one_mul _
  have h2 : ‖a • (L.comp (fderiv ℝ P x))‖ ≤ 2 * ‖fderiv ℝ P x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg a, norm_nonneg (L.comp (fderiv ℝ P x)), norm_nonneg (fderiv ℝ P x)]
  linarith

/-- The frozen streams `ψ_0 = 2 Re P_c q`, `ψ_1 = -2 Im P_c q` inherit differentiability and
`|ψ_i| + ‖Dψ_i‖ ≤ 2(|P_c q| + ‖D P_c q‖)`. -/
theorem inletTail_frozenStream (p : Params) (i : Fin 2) {x : ℝ × ℝ}
    (hP : DifferentiableAt ℝ (periodicStream p.mode p.c) x) :
    DifferentiableAt ℝ (p.frozenStream i) x ∧
      |p.frozenStream i x| + ‖fderiv ℝ (p.frozenStream i) x‖ ≤
        2 * (‖periodicStream p.mode p.c x‖ + ‖fderiv ℝ (periodicStream p.mode p.c) x‖) := by
  fin_cases i
  · have e : p.frozenStream 0 =
        fun y => (2 : ℝ) * Complex.reCLM (periodicStream p.mode p.c y) := by
      funext y
      simp [Params.frozenStream]
    show DifferentiableAt ℝ (p.frozenStream 0) x ∧
      |p.frozenStream 0 x| + ‖fderiv ℝ (p.frozenStream 0) x‖ ≤
        2 * (‖periodicStream p.mode p.c x‖ + ‖fderiv ℝ (periodicStream p.mode p.c) x‖)
    rw [e]
    exact inletTail_clm_aux _ Complex.reCLM Complex.reCLM_norm.le 2 (by norm_num) hP
  · have e : p.frozenStream 1 =
        fun y => (-2 : ℝ) * Complex.imCLM (periodicStream p.mode p.c y) := by
      funext y
      simp [Params.frozenStream]
    show DifferentiableAt ℝ (p.frozenStream 1) x ∧
      |p.frozenStream 1 x| + ‖fderiv ℝ (p.frozenStream 1) x‖ ≤
        2 * (‖periodicStream p.mode p.c x‖ + ‖fderiv ℝ (periodicStream p.mode p.c) x‖)
    rw [e]
    exact inletTail_clm_aux _ Complex.imCLM Complex.imCLM_norm.le (-2) (by norm_num) hP

/-! ## The reduction -/

/-- **The inlet transverse tail from the two leaves** (SP 2739-2756; SP 2347-2366). -/
theorem inletTransverseTail_of (ha : PeriodicStreamTail) (hb : InletChartFromStream) :
    InletTransverseTailQ := by
  intro Sig lam q _hSig hq dm dp hdm mZ hmZ bexp D _hbexp hD
  obtain ⟨K, hK0, hK⟩ := hb
  obtain ⟨a, C, k, ha0, hdec⟩ := ha lam q hq (⌈mZ⌉₊ + 2)
  obtain ⟨ν₁, hν₁, hpoly⟩ := inletTail_poly_le_exp_inv (4 * K * C) (2 * k)
  refine ⟨max 1 ((D + 1) / a), min 1 ν₁, lt_min one_pos hν₁, ?_⟩
  intro p d hreg hνle _hSg hmode i pt hs hsb hη
  subst hmode
  set Cp : ℝ := max 1 ((D + 1) / a) with hCp
  have hCp1 : 1 ≤ Cp := le_max_left _ _
  have hCpa : D + 1 ≤ a * Cp := by
    have h : (D + 1) / a ≤ Cp := le_max_right _ _
    rw [div_le_iff₀ ha0] at h
    linarith
  have hν : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := le_trans hνle (min_le_left _ _)
  have hνν₁ : p.ν ≤ ν₁ := le_trans hνle (min_le_right _ _)
  have hcpos : 0 < p.c := p.c_pos
  have hc_eq : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hεpos : 0 < p.ε := p.ε_pos
  have hε_le : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have hd : 0 < d := lt_of_lt_of_le hdm hreg.dm_le
    rw [div_le_iff₀ hν]
    linarith
  have hsqrtnn : 0 ≤ Real.sqrt (p.ε ^ (-bexp)) := Real.sqrt_nonneg _
  have hcν : 0 ≤ p.c / p.ν := div_nonneg hcpos.le hν.le
  have hXge : p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1 ≤
      Cp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) :=
    le_mul_of_one_le_left (by linarith) hCp1
  have hηnn : 0 ≤ |pt.2.2| := abs_nonneg _
  -- `√s < |η|` on the tail
  have hs1 : Real.sqrt pt.1 ≤ 1 + |pt.2.2| := by
    have : Real.sqrt pt.1 ≤ Real.sqrt (p.ε ^ (-bexp)) := Real.sqrt_le_sqrt hsb.le
    linarith
  -- `1 ≤ c ≤ |η|`
  have hc1 : 1 ≤ p.c := by
    rw [hc_eq]
    exact (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hν.le hν1)
  have hcνc : p.c ≤ p.c / p.ν := by
    rw [le_div_iff₀ hν]
    nlinarith
  have hcη : p.c ≤ |pt.2.2| := by linarith
  -- stream bounds from leaf (a)
  obtain ⟨hPd, hPb⟩ := hdec p.c hc1 pt.2 hcη
  obtain ⟨hψd, hψb⟩ := inletTail_frozenStream p i hPd
  set S : ℝ := ‖periodicStream p.mode p.c pt.2‖ + ‖fderiv ℝ (periodicStream p.mode p.c) pt.2‖
    with hS
  have hSnn : 0 ≤ S := by positivity
  -- chart bound from leaf (b)
  have hcoef0 := hK p i pt hs hψd
  have hfac1 : 1 + p.ε * (1 + |pt.2.2|) ≤ 2 * (1 + |pt.2.2|) := by nlinarith
  have hψnn : 0 ≤ |p.frozenStream i pt.2| + ‖fderiv ℝ (p.frozenStream i) pt.2‖ := by
    positivity
  have hcoef : ‖chartCoeff p.R (p.inlet i) pt‖ ≤ 4 * K * (1 + |pt.2.2|) * S := by
    calc ‖chartCoeff p.R (p.inlet i) pt‖
        ≤ K * (1 + p.ε * (1 + |pt.2.2|)) *
            (|p.frozenStream i pt.2| + ‖fderiv ℝ (p.frozenStream i) pt.2‖) := hcoef0
      _ ≤ K * (2 * (1 + |pt.2.2|)) * (2 * S) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hfac1 hK0) hψb hψnn
          positivity
      _ = 4 * K * (1 + |pt.2.2|) * S := by ring
  -- weight
  have hW := inletTail_transWeight_le (by linarith : (0 : ℝ) ≤ mZ) (le_of_lt hs)
  have hWnn := inletTail_transWeight_nonneg mZ pt
  have hsqrt_nn : 0 ≤ Real.sqrt pt.1 := Real.sqrt_nonneg _
  have hstep1 : Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
      4 * K * ((1 + |pt.2.2|) ^ (⌈mZ⌉₊ + 2) * S) := by
    calc Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖
        ≤ (1 + |pt.2.2|) * (1 + |pt.2.2|) ^ (⌈mZ⌉₊) * (4 * K * (1 + |pt.2.2|) * S) := by
          apply mul_le_mul (mul_le_mul hs1 hW hWnn (by positivity)) hcoef (norm_nonneg _)
          positivity
      _ = 4 * K * ((1 + |pt.2.2|) ^ (⌈mZ⌉₊ + 2) * S) := by ring
  -- exponential rate: `(D+1)/ν ≤ a|η|/c`
  have hηc : Cp * (p.c / p.ν) < |pt.2.2| := by
    have : Cp * (p.c / p.ν) ≤ Cp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hrate : (D + 1) / p.ν ≤ a * |pt.2.2| / p.c := by
    rw [div_le_div_iff₀ hν hcpos]
    have h1 : Cp * p.c < |pt.2.2| * p.ν := by
      have h := hηc
      rw [mul_div_assoc'] at h
      rwa [div_lt_iff₀ hν] at h
    nlinarith
  have hexp_le : Real.exp (-(a * |pt.2.2| / p.c)) ≤ Real.exp (-(D + 1) / p.ν) := by
    apply Real.exp_le_exp.2
    rw [neg_div]
    linarith
  -- sign of the polynomial constant
  have hCc : 0 ≤ C * p.c ^ k := by
    have h0 : 0 ≤ C * p.c ^ k * Real.exp (-(a * |pt.2.2| / p.c)) :=
      le_trans (by positivity) hPb
    by_contra hneg
    have hneg' : C * p.c ^ k < 0 := lt_of_not_ge hneg
    have := mul_neg_of_neg_of_pos hneg' (Real.exp_pos (-(a * |pt.2.2| / p.c)))
    linarith
  have hck : p.c ^ k = (p.ν⁻¹) ^ (2 * k) := by
    rw [hc_eq, pow_mul, inv_pow p.ν 2]
  have hpolyν := hpoly p.ν hν hνν₁
  calc Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖
      ≤ 4 * K * ((1 + |pt.2.2|) ^ (⌈mZ⌉₊ + 2) * S) := hstep1
    _ ≤ 4 * K * (C * p.c ^ k * Real.exp (-(a * |pt.2.2| / p.c))) :=
        mul_le_mul_of_nonneg_left hPb (by positivity)
    _ ≤ 4 * K * (C * p.c ^ k * Real.exp (-(D + 1) / p.ν)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hexp_le hCc
    _ = (4 * K * C * (p.ν⁻¹) ^ (2 * k)) * Real.exp (-(D + 1) / p.ν) := by
        rw [hck]; ring
    _ ≤ Real.exp (1 / p.ν) * Real.exp (-(D + 1) / p.ν) :=
        mul_le_mul_of_nonneg_right hpolyν (Real.exp_pos _).le
    _ = Real.exp (-D / p.ν) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring

end UnforcedLeray.Short.IIIa
