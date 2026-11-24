import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartIIa.Sub.R01_1

/-!
# Part III-a, `PartIII-a:T23/1`: the late raw coefficient bound (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 2703-2723
(`stress-short:coefficients` and the paragraph "To check the age powers ..."), with the Part I
train estimates `sct:mean` (397-404), `sct:fluctuation` (439-446) and `sct:expansion` (447-459).

Target: `RawCoeffLate` (`StressInputs.lean`): for ages `s ≥ 1`,
`√s W|v_raw| ≤ P_ν(s^{-1/2}+ε)` and `‖W v_raw(s)‖_{L²_η L^∞_q} ≤ P_ν[(1+s)^{-3/4}+ε(1+s)^{-1/4}]`,
`v_raw = chartCoeff p.R p.raw`, `W = ⟨η/√(1+s)⟩^{m_Z}`.

## The route (SP 2719-2727)

* `v_raw = b_raw = (v₁, v₂ + εH)` with `H = (1 - η∂_η - 2s∂_s)ψ` the stream completion
  (`Sub/T23_1_org/Bridge.lean`, `chartCoeff_raw`), so `|v_raw| ≤ |v| + ε|H|`.
* `v = \bar v + \tilde v` (horizontal mean and fluctuation). "The mean stream and its fixed weighted
  derivatives have size `(1+s)^{-1/2}` on transverse scale `√(1+s)`. One transverse derivative gives
  the velocity size `(1+s)^{-1}`" (SP 2719-2721): `LateMeanVel`.  "Fluctuations have exponential
  decay after overlap; before overlap the Gaussian comparison gives the same polynomial bounds"
  (SP 2726-2727): `LateFluctVel` (from `sct:fluctuation`, `P e^{-κνs/c²}`, the polynomial absorbing
  `(1+s)` before overlap).
* `H = H_mean + H_fluct` (`RaisedStreamSplit`): "The stream completion
  `ε(1-η∂_η-2s∂_s)ψ` has size `P_ν ε (1+s)^{-1/2}`. Its slower decay is retained" (SP 2721-2723):
  `LateMeanCompletion` (mean stream `S`, its weighted derivatives `ηS_η`, `sS_s`) and
  `LateFluctCompletion` (fluctuation stream, exponentially small).
* "Multiplying by any further fixed power of `⟨η/√(1+s)⟩` leaves these conclusions unchanged, by
  the weighted train expansion" (SP 2728-2730): every leaf is stated for every weight exponent
  `m_Z ≥ 0`; the assembly uses `m_Z + 1`.
* "The `L²_η` norm adds the factor `(1+s)^{1/4}`" (SP 2724): with one extra weight power,
  `∫ ⟨η/√(1+s)⟩^{-2} dη = π√(1+s)` (`integral_univ_inv_one_add_sq`).

All leaves are stated for the BUC train of Part I at `(ν, c)`, `c = ν^{-2}`, the class in which the
Part I estimates hold (`BgRegime.train_buc`, SP 270-288, 2040).

## Contents

* definitions: `fluctStream` (`\tilde ψ = ψ - \bar ψ`), `meanCompletion` (`(1-η∂_η-2s∂_s)S`);
* leaf statements: `LateFluctVel`, `LateMeanVel`, `LateFluctCompletion`, `LateMeanCompletion`,
  `RaisedStreamSplit` (tasks `PartIII-a:T23/1/1` .. `/5`);
* helper lemmas for the leaves (proved): `period_eq_trainPeriod`, `polyP_le_inv_pow`,
  `one_add_mul_exp_neg_le`, `transWeight_le_sqrt_jap`, `transWeight_le_two_pow`;
* assembly (proved): `lateVel_of`, `lateCompletion_of`, `rawCoeffLate_of_vel`, `rawCoeffLate_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-! ## The mean/fluctuation split of the stream -/

/-- The fluctuation stream `\tilde ψ(r, z) = ψ(r, z) - \bar ψ(r, η)` (SP 439-446, the source's
tilde; `PartI.hmean` is the normalized horizontal average). -/
def fluctStream {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ℝ → UnforcedLeray.Cyl.Plane → ℝ :=
  fun r z => tr.ψ r z - UnforcedLeray.Short.PartI.hmean c (tr.ψ r) z.2

/-- The stream completion of the mean stream `S = \bar ψ`: `(1 - η∂_η - 2s∂_s)S` at `(s, η)`
(SP 2721-2723; it is `C03.raisedStream` of the `q`-independent field `S`). -/
def meanCompletion {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  UnforcedLeray.Short.PartI.meanStream tr s η -
    (η * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η +
      2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s)

/-! ## The leaf statements -/

/-- **Fluctuation velocity at late ages** (SP 2726-2727 from `sct:fluctuation`, SP 439-446): for
every weight exponent `m_Z ≥ 0` there are `C, k, ν₀` with
`W |\tilde v(s, q, η)| ≤ C ν^{-k} (1+s)^{-1}` for `s ≥ 1`, for every BUC train at `(ν, ν^{-2})`,
`ν ≤ ν₀`. (`⟨η⟩^m|\tilde v| ≤ P e^{-κνs/c²}` and `(1+s)e^{-κνs/c²} ≤ 1 + c²/(κν)`, polynomial in
`ν⁻¹` since `c = ν^{-2}`.) -/
def LateFluctVel : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * ‖UnforcedLeray.Short.PartI.hfluct c (tr.v s) (q, η)‖ ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (-1 : ℝ)

/-- **Mean velocity at late ages** (SP 2719-2721: "the mean stream and its fixed weighted
derivatives have size `(1+s)^{-1/2}` on transverse scale `√(1+s)`. One transverse derivative gives
the velocity size `(1+s)^{-1}`"; `sct:mean` `\bar v = (-S_η, 0)` and `sct:expansion`): for every
`m_Z ≥ 0` there are `C, k, ν₀` with `W |\bar v(s, η)| ≤ C ν^{-k} (1+s)^{-1}` for `s ≥ 1`. -/
def LateMeanVel : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * ‖UnforcedLeray.Short.PartI.hmean c (tr.v s) η‖ ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (-1 : ℝ)

/-- **Stream completion of the fluctuation at late ages** (SP 2721-2723 and 2726-2727, from
`sct:fluctuation` for `\tilde ψ`, `∂_η\tilde ψ`, `∂_s\tilde ψ`): for every `m_Z ≥ 0` there are
`C, k, ν₀` with `W |(1 - η∂_η - 2s∂_s)\tilde ψ(s, q, η)| ≤ C ν^{-k} (1+s)^{-1/2}` for `s ≥ 1`. -/
def LateFluctCompletion : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) *
            |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (-1 / 2 : ℝ)

/-- **Stream completion of the mean stream at late ages** (SP 2721-2723: "the stream completion
`ε(1-η∂_η-2s∂_s)ψ` has size `P_ν ε(1+s)^{-1/2}`"; `S`, `ηS_η`, `sS_s` have size `(1+s)^{-1/2}`
on transverse scale `√(1+s)`, `sct:expansion` SP 447-459): for every `m_Z ≥ 0` there are
`C, k, ν₀` with `W |(1 - η∂_η - 2s∂_s)S(s, η)| ≤ C ν^{-k} (1+s)^{-1/2}` for `s ≥ 1`. -/
def LateMeanCompletion : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * |meanCompletion tr s η| ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (-1 / 2 : ℝ)

/-- **The stream completion splits into mean and fluctuation** (calculus; SP 2721-2723 with
`ψ = \bar ψ + \tilde ψ`): for a BUC train and `s > 0`,
`(1-η∂_η-2s∂_s)ψ = (1-η∂_η-2s∂_s)\tilde ψ + (1-η∂_η-2s∂_s)S`.  (`ψ` is `C^∞` for `s > 0`,
`PartI.TrainStreamSmooth`, and so is `S`, `PartIIa.MeanStreamSmooth`; `deriv` is additive on
differentiable functions.) -/
def RaisedStreamSplit : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ q η : ℝ,
      UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η =
        UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η + meanCompletion tr s η

/-! ## Helper lemmas (for the leaves) -/

/-- `c = ν^{-2}` is the Part I period `trainPeriod 2 ν` (SP 2031; `subst` it to apply the Part I
estimates, which are stated over `B0140.TrainSol ν (trainPeriod ρ ν)`). -/
theorem period_eq_trainPeriod {ν c : ℝ} (hν : 0 < ν) (hc : c = (ν ^ 2)⁻¹) :
    c = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
  rw [hc]
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- The Part I polynomial `P = C(1+c+ν⁻¹)^N` at `c = ν⁻²`, `0 < ν ≤ 1`, is at most
`|C| 3^N ν^{-2N}`. -/
theorem polyP_le_inv_pow (C : ℝ) (N : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ ≤ |C| * 3 ^ N * ν⁻¹ ^ (2 * N) := by
  unfold UnforcedLeray.Short.PartI.polyP
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have h2 : ν⁻¹ ≤ ν⁻¹ ^ 2 := by nlinarith
  have hb : 1 + (ν ^ 2)⁻¹ + ν⁻¹ ≤ 3 * ν⁻¹ ^ 2 := by
    rw [← inv_pow]; nlinarith
  have hb0 : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by positivity
  have hp : (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N ≤ 3 ^ N * ν⁻¹ ^ (2 * N) := by
    calc (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N ≤ (3 * ν⁻¹ ^ 2) ^ N := pow_le_pow_left₀ hb0 hb N
      _ = 3 ^ N * ν⁻¹ ^ (2 * N) := by rw [mul_pow, pow_mul]
  calc C * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N ≤ |C| * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hb0 N)
    _ ≤ |C| * (3 ^ N * ν⁻¹ ^ (2 * N)) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = |C| * 3 ^ N * ν⁻¹ ^ (2 * N) := by ring

/-- Absorption of the exponential age decay (SP 2726-2727): `(1+s) e^{-as} ≤ 1 + a⁻¹` for
`a > 0`, `s ≥ 0` (`e^{as} ≥ 1 + as`).  Applied with `a/2` and squared it gives
`(1+s)² e^{-as} ≤ (1 + 2a⁻¹)²`. -/
theorem one_add_mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1 + s) * Real.exp (-(a * s)) ≤ 1 + a⁻¹ := by
  have he : 1 + a * s ≤ Real.exp (a * s) := by
    have := Real.add_one_le_exp (a * s)
    linarith
  have hpos : 0 < 1 + a * s := by positivity
  have hkey : 1 + s ≤ (1 + a⁻¹) * (1 + a * s) := by
    have ha' : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
    have e : (1 + a⁻¹) * (1 + a * s) = 1 + s + a * s + a⁻¹ := by
      calc (1 + a⁻¹) * (1 + a * s) = 1 + a * s + a⁻¹ + (a⁻¹ * a) * s := by ring
        _ = 1 + s + a * s + a⁻¹ := by rw [ha']; ring
    rw [e]
    have h1 : 0 ≤ a * s := mul_nonneg ha.le hs
    have h2 : 0 ≤ a⁻¹ := inv_nonneg.2 ha.le
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc 1 + s ≤ (1 + a⁻¹) * (1 + a * s) := hkey
    _ ≤ (1 + a⁻¹) * Real.exp (a * s) :=
        mul_le_mul_of_nonneg_left he (by positivity)

/-- The transverse weight is at most `⟨η⟩^{⌈m_Z⌉}`: `W = (1 + η²/(1+s))^{m_Z/2} ≤ (1+η²)^{m/2}`,
`m = ⌈m_Z⌉₊`, `s ≥ 0` (`Train.jap m z = (1+η²)^m`, the weight of `sct:fluctuation`). -/
theorem transWeight_le_sqrt_jap {mZ : ℝ} (hmZ : 0 ≤ mZ) {p : ℝ × (ℝ × ℝ)} (hs : 0 ≤ p.1) :
    transWeight mZ p ≤ Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ p.2) := by
  unfold transWeight UnforcedLeray.Train.jap
  have h1s : 0 < 1 + p.1 := by linarith
  have hx : (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 = p.2.2 ^ 2 / (1 + p.1) := by
    rw [div_pow, Real.sq_sqrt h1s.le]
  have hxle : p.2.2 ^ 2 / (1 + p.1) ≤ p.2.2 ^ 2 :=
    div_le_self (sq_nonneg _) (by linarith)
  have hx0 : 0 ≤ p.2.2 ^ 2 / (1 + p.1) := div_nonneg (sq_nonneg _) h1s.le
  rw [hx]
  have hb1 : 1 ≤ 1 + p.2.2 ^ 2 := by nlinarith [sq_nonneg p.2.2]
  calc (1 + p.2.2 ^ 2 / (1 + p.1)) ^ (mZ / 2)
      ≤ (1 + p.2.2 ^ 2) ^ (mZ / 2) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ (1 + p.2.2 ^ 2) ^ ((⌈mZ⌉₊ : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by
          have := Nat.le_ceil mZ
          linarith)
    _ = Real.sqrt ((1 + p.2.2 ^ 2) ^ ⌈mZ⌉₊) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + p.2.2 ^ 2) ⌈mZ⌉₊,
          ← Real.rpow_mul (by linarith)]
        congr 1
        ring

/-- The transverse weight at transverse scale `√(1+s)` (SP 2719-2720):
`W ≤ 2^n (1 + η^{2n}/(1+s)^n)`, `n = ⌈m_Z/2⌉₊`, `s ≥ 0`. -/
theorem transWeight_le_two_pow (mZ : ℝ) {s : ℝ} (hs : 0 ≤ s) (q η : ℝ) :
    transWeight mZ (s, (q, η)) ≤
      2 ^ ⌈mZ / 2⌉₊ * (1 + η ^ (2 * ⌈mZ / 2⌉₊) / (1 + s) ^ ⌈mZ / 2⌉₊) := by
  unfold transWeight
  set n := ⌈mZ / 2⌉₊ with hn
  have h1s : 0 < 1 + s := by linarith
  have hx : (η / Real.sqrt (1 + s)) ^ 2 = η ^ 2 / (1 + s) := by
    rw [div_pow, Real.sq_sqrt h1s.le]
  simp only
  rw [hx]
  set x := η ^ 2 / (1 + s) with hxdef
  have hx0 : 0 ≤ x := div_nonneg (sq_nonneg _) h1s.le
  have hb1 : 1 ≤ 1 + x := by linarith
  have hstep1 : (1 + x) ^ (mZ / 2) ≤ (1 + x) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (Nat.le_ceil _)
  have hmax : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hstep2 : (1 + x) ^ n ≤ 2 ^ n * (max 1 x) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hmax n
  have hstep3 : (max 1 x) ^ n ≤ 1 + x ^ n := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx0 n]
  have hxn : x ^ n = η ^ (2 * n) / (1 + s) ^ n := by
    rw [hxdef, div_pow, pow_mul]
  calc (1 + x) ^ (mZ / 2) ≤ (1 + x) ^ n := hstep1
    _ ≤ 2 ^ n * (max 1 x) ^ n := hstep2
    _ ≤ 2 ^ n * (1 + x ^ n) := mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = 2 ^ n * (1 + η ^ (2 * n) / (1 + s) ^ n) := by rw [hxn]

/-! ## Assembly -/

/-- `C ν^{-k} x ≤ max C 0 · ν^{-K} x` for `k ≤ K`, `0 < ν ≤ 1`, `x ≥ 0`. -/
theorem const_mul_inv_pow_le {C ν x : ℝ} {k K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hk : k ≤ K)
    (hx : 0 ≤ x) : C * ν⁻¹ ^ k * x ≤ max C 0 * ν⁻¹ ^ K * x := by
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have hp : ν⁻¹ ^ k ≤ ν⁻¹ ^ K := pow_le_pow_right₀ h1 hk
  have hk0 : 0 ≤ ν⁻¹ ^ k := by positivity
  apply mul_le_mul_of_nonneg_right _ hx
  calc C * ν⁻¹ ^ k ≤ max C 0 * ν⁻¹ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
    _ ≤ max C 0 * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

/-- The whole train velocity at late ages (SP 2719-2727). -/
def LateVel : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * ‖tr.v s (q, η)‖ ≤ C * ν⁻¹ ^ k * (1 + s) ^ (-1 : ℝ)

/-- The whole stream completion at late ages (SP 2721-2723). -/
def LateCompletion : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (-1 / 2 : ℝ)

theorem transWeight_nonneg (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) : 0 ≤ transWeight mZ p := by
  unfold transWeight
  positivity

/-- `v = \bar v + \tilde v` (SP 2719-2727). -/
theorem lateVel_of (h1 : LateFluctVel) (h2 : LateMeanVel) : LateVel := by
  intro mZ hmZ
  obtain ⟨C₁, k₁, ν₁, hν₁, H1⟩ := h1 mZ hmZ
  obtain ⟨C₂, k₂, ν₂, hν₂, H2⟩ := h2 mZ hmZ
  refine ⟨max C₁ 0 + max C₂ 0, max k₁ k₂, min (min ν₁ ν₂) 1,
    add_nonneg (le_max_right _ _) (le_max_right _ _),
    lt_min (lt_min hν₁ hν₂) one_pos, min_le_right _ _, ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₁ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : ν ≤ ν₂ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hx : 0 ≤ (1 + s) ^ (-1 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hF := (H1 ν ⟨hν0, hνa⟩ c hc tr hbuc s hs q η).trans
    (const_mul_inv_pow_le hν0 hν1 (le_max_left k₁ k₂) hx)
  have hM := (H2 ν ⟨hν0, hνb⟩ c hc tr hbuc s hs q η).trans
    (const_mul_inv_pow_le hν0 hν1 (le_max_right k₁ k₂) hx)
  have hW := transWeight_nonneg mZ (s, (q, η))
  have hsplit : ‖tr.v s (q, η)‖ ≤ ‖UnforcedLeray.Short.PartI.hfluct c (tr.v s) (q, η)‖ +
      ‖UnforcedLeray.Short.PartI.hmean c (tr.v s) η‖ := by
    have he : tr.v s (q, η) = UnforcedLeray.Short.PartI.hfluct c (tr.v s) (q, η) +
        UnforcedLeray.Short.PartI.hmean c (tr.v s) η := by
      simp only [UnforcedLeray.Short.PartI.hfluct, sub_add_cancel]
    rw [he]
    exact norm_add_le _ _
  calc transWeight mZ (s, (q, η)) * ‖tr.v s (q, η)‖
      ≤ transWeight mZ (s, (q, η)) * (‖UnforcedLeray.Short.PartI.hfluct c (tr.v s) (q, η)‖ +
          ‖UnforcedLeray.Short.PartI.hmean c (tr.v s) η‖) := mul_le_mul_of_nonneg_left hsplit hW
    _ = transWeight mZ (s, (q, η)) * ‖UnforcedLeray.Short.PartI.hfluct c (tr.v s) (q, η)‖ +
        transWeight mZ (s, (q, η)) * ‖UnforcedLeray.Short.PartI.hmean c (tr.v s) η‖ := by ring
    _ ≤ max C₁ 0 * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 : ℝ) +
        max C₂ 0 * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 : ℝ) := add_le_add hF hM
    _ = (max C₁ 0 + max C₂ 0) * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 : ℝ) := by ring

/-- `H = H_fluct + H_mean` (SP 2721-2723). -/
theorem lateCompletion_of (h3 : LateFluctCompletion) (h4 : LateMeanCompletion)
    (h5 : RaisedStreamSplit) : LateCompletion := by
  intro mZ hmZ
  obtain ⟨C₁, k₁, ν₁, hν₁, H1⟩ := h3 mZ hmZ
  obtain ⟨C₂, k₂, ν₂, hν₂, H2⟩ := h4 mZ hmZ
  refine ⟨max C₁ 0 + max C₂ 0, max k₁ k₂, min (min ν₁ ν₂) 1,
    add_nonneg (le_max_right _ _) (le_max_right _ _),
    lt_min (lt_min hν₁ hν₂) one_pos, min_le_right _ _, ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₁ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : ν ≤ ν₂ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hx : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hF := (H1 ν ⟨hν0, hνa⟩ c hc tr hbuc s hs q η).trans
    (const_mul_inv_pow_le hν0 hν1 (le_max_left k₁ k₂) hx)
  have hM := (H2 ν ⟨hν0, hνb⟩ c hc tr hbuc s hs q η).trans
    (const_mul_inv_pow_le hν0 hν1 (le_max_right k₁ k₂) hx)
  have hW := transWeight_nonneg mZ (s, (q, η))
  have hsplit : |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
      |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| + |meanCompletion tr s η| := by
    rw [h5 ν c hν0 hc0 tr hbuc s (by linarith) q η]
    exact abs_add_le _ _
  calc transWeight mZ (s, (q, η)) * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η|
      ≤ transWeight mZ (s, (q, η)) *
          (|UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| +
            |meanCompletion tr s η|) := mul_le_mul_of_nonneg_left hsplit hW
    _ = transWeight mZ (s, (q, η)) *
          |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| +
        transWeight mZ (s, (q, η)) * |meanCompletion tr s η| := by ring
    _ ≤ max C₁ 0 * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 / 2 : ℝ) +
        max C₂ 0 * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 / 2 : ℝ) := add_le_add hF hM
    _ = (max C₁ 0 + max C₂ 0) * ν⁻¹ ^ max k₁ k₂ * (1 + s) ^ (-1 / 2 : ℝ) := by ring

/-- One more weight power: `W_{m+1} = W_m ⟨η/√(1+s)⟩`. -/
theorem transWeight_add_one (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    transWeight (mZ + 1) p =
      transWeight mZ p * Real.sqrt (1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) := by
  unfold transWeight
  set B : ℝ := 1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 with hBdef
  have hB : 0 < B := by rw [hBdef]; positivity
  rw [Real.sqrt_eq_rpow B, ← Real.rpow_add hB]
  congr 1
  ring

/-- `∫ (1 + (η/√a)²)⁻¹ dη = √a π` for `a > 0`. -/
theorem lintegral_inv_one_add_sq_div {a : ℝ} (ha : 0 < a) :
    ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt a) ^ 2)⁻¹) =
      ENNReal.ofReal (Real.sqrt a * Real.pi) := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hint : Integrable (fun η : ℝ => (1 + (η / Real.sqrt a) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_div hsa
  have hnn : 0 ≤ᵐ[volume] fun η : ℝ => (1 + (η / Real.sqrt a) ^ 2)⁻¹ :=
    Eventually.of_forall fun η => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  have hcv : ∫ x : ℝ, (1 + (x / Real.sqrt a) ^ 2)⁻¹ =
      |Real.sqrt a| • ∫ y : ℝ, (1 + y ^ 2)⁻¹ :=
    Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) (Real.sqrt a)
  rw [hcv, integral_univ_inv_one_add_sq, abs_of_pos (Real.sqrt_pos.2 ha), smul_eq_mul]

/-- **Assembly from the whole velocity and stream completion** (SP 2703-2724). -/
theorem rawCoeffLate_of_vel (hV : LateVel) (hH : LateCompletion) : RawCoeffLate := by
  intro dm dp hdm mZ hmZ
  have hmZ1 : 0 ≤ mZ + 1 := by linarith
  obtain ⟨A, k₁, ν₁, hA, hν₁, hν₁1, H1⟩ := hV (mZ + 1) hmZ1
  obtain ⟨B, k₂, ν₂, hB, hν₂, hν₂1, H2⟩ := hH (mZ + 1) hmZ1
  set C : ℝ := (A + B) * (1 + Real.sqrt Real.pi) with hCdef
  have hπ : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hAC : A ≤ C := by
    rw [hCdef]; nlinarith
  have hBC : B ≤ C := by
    rw [hCdef]; nlinarith
  have hAπ : Real.sqrt Real.pi * A ≤ C := by
    rw [hCdef]; nlinarith
  have hBπ : Real.sqrt Real.pi * B ≤ C := by
    rw [hCdef]; nlinarith
  refine ⟨C, max k₁ k₂, min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν
  have hν0 : 0 < p.ν := p.ν_pos
  have hνa : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hνb : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hνa.trans hν₁1
  have hε : 0 < p.ε := p.ε_pos
  set N : ℝ := p.ν⁻¹ ^ max k₁ k₂ with hN
  have hN0 : 0 ≤ N := by rw [hN]; exact pow_nonneg (inv_nonneg.2 hν0.le) _
  -- the pointwise bounds on the actual train, with one extra weight power
  have hv : ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
      transWeight (mZ + 1) (s, (q, η)) * ‖p.train.v s (q, η)‖ ≤ A * N * (1 + s) ^ (-1 : ℝ) := by
    intro s hs q η
    have hx : 0 ≤ (1 + s) ^ (-1 : ℝ) := Real.rpow_nonneg (by linarith) _
    have h := (H1 p.ν ⟨hν0, hνa⟩ p.c hreg.c_eq p.train hreg.train_buc s hs q η).trans
      (const_mul_inv_pow_le hν0 hν1 (le_max_left k₁ k₂) hx)
    rwa [max_eq_left hA] at h
  have hh : ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
      transWeight (mZ + 1) (s, (q, η)) *
          |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η| ≤
        B * N * (1 + s) ^ (-1 / 2 : ℝ) := by
    intro s hs q η
    have hx : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have h := (H2 p.ν ⟨hν0, hνb⟩ p.c hreg.c_eq p.train hreg.train_buc s hs q η).trans
      (const_mul_inv_pow_le hν0 hν1 (le_max_right k₁ k₂) hx)
    rwa [max_eq_left hB] at h
  -- the weighted raw coefficient, with one weight power to spare
  have hcore : ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
      transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ *
          Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) ≤
        A * N * (1 + s) ^ (-1 : ℝ) + p.ε * (B * N * (1 + s) ^ (-1 / 2 : ℝ)) := by
    intro s hs q η
    have hs0 : 0 < s := by linarith
    have hb := norm_rawProfile_le p.ε p.train.v p.train.ψ (s, (q, η))
    rw [← chartCoeff_raw p (pt := (s, (q, η))) hs0, abs_of_pos hε] at hb
    have hW1 := transWeight_add_one mZ (s, (q, η))
    simp only at hW1
    have hW0 := transWeight_nonneg mZ (s, (q, η))
    have hg0 : 0 ≤ Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) := Real.sqrt_nonneg _
    have hWg : 0 ≤ transWeight mZ (s, (q, η)) * Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) :=
      mul_nonneg hW0 hg0
    calc transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ *
          Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2)
        = transWeight (mZ + 1) (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ := by
          rw [hW1]; ring
      _ ≤ transWeight (mZ + 1) (s, (q, η)) * (‖p.train.v s (q, η)‖ +
            p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) := by
          rw [hW1]
          exact mul_le_mul_of_nonneg_left hb hWg
      _ = transWeight (mZ + 1) (s, (q, η)) * ‖p.train.v s (q, η)‖ +
            p.ε * (transWeight (mZ + 1) (s, (q, η)) *
              |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) := by ring
      _ ≤ A * N * (1 + s) ^ (-1 : ℝ) + p.ε * (B * N * (1 + s) ^ (-1 / 2 : ℝ)) :=
          add_le_add (hv s hs q η) (mul_le_mul_of_nonneg_left (hh s hs q η) hε.le)
  refine ⟨?_, ?_⟩
  · -- `√s W|v| ≤ P_ν(s^{-1/2} + ε)`
    intro pt hs
    obtain ⟨s, q, η⟩ := pt
    simp only at hs
    have hs0 : 0 < s := by linarith
    have hg1 : 1 ≤ Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) := by
      have h := Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ 1 + (η / Real.sqrt (1 + s)) ^ 2 by
          nlinarith [sq_nonneg (η / Real.sqrt (1 + s))])
      rwa [Real.sqrt_one] at h
    have hX0 : 0 ≤ transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ :=
      mul_nonneg (transWeight_nonneg _ _) (norm_nonneg _)
    have hX : transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ ≤
        A * N * (1 + s) ^ (-1 : ℝ) + p.ε * (B * N * (1 + s) ^ (-1 / 2 : ℝ)) :=
      (le_mul_of_one_le_right hX0 hg1).trans (hcore s hs q η)
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
    -- `√s (1+s)^{-1} ≤ s^{-1/2}` and `√s (1+s)^{-1/2} ≤ 1`
    have hF1 : Real.sqrt s * (1 + s) ^ (-1 : ℝ) ≤ s ^ (-1 / 2 : ℝ) := by
      rw [Real.rpow_neg_one]
      have h1 : (1 + s)⁻¹ ≤ s⁻¹ := inv_anti₀ hs0 (by linarith)
      have h2 : Real.sqrt s * s⁻¹ = s ^ (-1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hs0]
        norm_num
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 hsq
    have hF2 : Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ) ≤ 1 := by
      have h1s : 0 < 1 + s := by linarith
      have he : (1 + s) ^ (-1 / 2 : ℝ) = (Real.sqrt (1 + s))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h1s.le]
        norm_num
      rw [he, ← div_eq_mul_inv, div_le_one (Real.sqrt_pos.2 h1s)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hB0 : 0 ≤ B * N := mul_nonneg hB hN0
    have hA0 : 0 ≤ A * N := mul_nonneg hA hN0
    have hs12 : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    calc Real.sqrt s * transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖
        = Real.sqrt s * (transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖) := by
          ring
      _ ≤ Real.sqrt s * (A * N * (1 + s) ^ (-1 : ℝ) + p.ε * (B * N * (1 + s) ^ (-1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hX hsq
      _ = A * N * (Real.sqrt s * (1 + s) ^ (-1 : ℝ)) +
            p.ε * (B * N) * (Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ)) := by ring
      _ ≤ A * N * s ^ (-1 / 2 : ℝ) + p.ε * (B * N) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hF1 hA0)
            (mul_le_mul_of_nonneg_left hF2 (mul_nonneg hε.le hB0))
      _ ≤ C * N * s ^ (-1 / 2 : ℝ) + p.ε * (C * N) * 1 := by
          have h1 : A * N ≤ C * N := mul_le_mul_of_nonneg_right hAC hN0
          have h2 : B * N ≤ C * N := mul_le_mul_of_nonneg_right hBC hN0
          have := mul_le_mul_of_nonneg_right h1 hs12
          have := mul_le_mul_of_nonneg_left h2 hε.le
          linarith
      _ = C * N * (s ^ (-1 / 2 : ℝ) + p.ε) := by ring
  · -- `‖W v(s)‖_{L²_η L^∞_q} ≤ P_ν[(1+s)^{-3/4} + ε(1+s)^{-1/4}]`
    intro s hs
    have hs0 : 0 < s := by linarith
    have ha : 0 < 1 + s := by linarith
    set K : ℝ := A * N * (1 + s) ^ (-1 : ℝ) + p.ε * (B * N * (1 + s) ^ (-1 / 2 : ℝ)) with hKdef
    have hK0 : 0 ≤ K := by
      have h1 : 0 ≤ (1 + s) ^ (-1 : ℝ) := Real.rpow_nonneg ha.le _
      have h2 : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg ha.le _
      rw [hKdef]
      exact add_nonneg (mul_nonneg (mul_nonneg hA hN0) h1)
        (mul_nonneg hε.le (mul_nonneg (mul_nonneg hB hN0) h2))
    have hgpos : ∀ η, 0 < Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) := fun η =>
      Real.sqrt_pos.2 (by positivity)
    -- pointwise in `(q, η)`
    have hpt : ∀ η q : ℝ, ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖chartCoeff p.R p.raw (s, (q, η))‖ₑ ≤
          ENNReal.ofReal (K * (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹) := by
      intro η q
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (transWeight_nonneg _ _)]
      apply ENNReal.ofReal_le_ofReal
      have h := hcore s hs q η
      rw [← div_eq_mul_inv, le_div_iff₀ (hgpos η)]
      exact h
    have hess : ∀ η : ℝ, essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖chartCoeff p.R p.raw (s, (q, η))‖ₑ) (volume.restrict (Ico (-(p.c / 2)) (p.c / 2))) ≤
          ENNReal.ofReal (K * (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹) := fun η =>
      essSup_le_of_ae_le _ (Eventually.of_forall fun q => hpt η q)
    have hsq_eq : ∀ η : ℝ,
        ENNReal.ofReal (K * (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹) ^ (2 : ℝ) =
          ENNReal.ofReal (K ^ 2) * ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2)⁻¹) := by
      intro η
      have hg0 : 0 ≤ (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹ :=
        inv_nonneg.2 (Real.sqrt_nonneg _)
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK0 hg0) (by norm_num),
        ← ENNReal.ofReal_mul (sq_nonneg K)]
      congr 1
      rw [Real.rpow_two, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    have hint : ∫⁻ η : ℝ,
        ENNReal.ofReal (K * (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹) ^ (2 : ℝ) =
        ENNReal.ofReal (K ^ 2 * (Real.sqrt (1 + s) * Real.pi)) := by
      simp_rw [hsq_eq]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_inv_one_add_sq_div ha,
        ← ENNReal.ofReal_mul (sq_nonneg K)]
    have hmono : etaL2QSup p.c mZ (chartCoeff p.R p.raw) s ≤
        ENNReal.ofReal (K ^ 2 * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) := by
      unfold etaL2QSup
      rw [← hint]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply lintegral_mono
      intro η
      exact ENNReal.rpow_le_rpow (hess η) (by norm_num)
    refine hmono.trans ?_
    have hX0 : 0 ≤ K ^ 2 * (Real.sqrt (1 + s) * Real.pi) := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    -- `(K² √a π)^{1/2} = K a^{1/4} √π`
    have hroot : (K ^ 2 * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) =
        K * (1 + s) ^ (1 / 4 : ℝ) * Real.sqrt Real.pi := by
      have h44 : Real.sqrt (Real.sqrt (1 + s)) = (1 + s) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
        norm_num
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0,
        Real.sqrt_mul (Real.sqrt_nonneg _), h44]
      ring
    rw [hroot]
    have hp1 : (1 + s) ^ (-1 : ℝ) * (1 + s) ^ (1 / 4 : ℝ) = (1 + s) ^ (-3 / 4 : ℝ) := by
      rw [← Real.rpow_add ha]; norm_num
    have hp2 : (1 + s) ^ (-1 / 2 : ℝ) * (1 + s) ^ (1 / 4 : ℝ) = (1 + s) ^ (-1 / 4 : ℝ) := by
      rw [← Real.rpow_add ha]; norm_num
    have hq1 : 0 ≤ (1 + s) ^ (-3 / 4 : ℝ) := Real.rpow_nonneg ha.le _
    have hq2 : 0 ≤ (1 + s) ^ (-1 / 4 : ℝ) := Real.rpow_nonneg ha.le _
    calc K * (1 + s) ^ (1 / 4 : ℝ) * Real.sqrt Real.pi
        = Real.sqrt Real.pi * A * N * ((1 + s) ^ (-1 : ℝ) * (1 + s) ^ (1 / 4 : ℝ)) +
            p.ε * (Real.sqrt Real.pi * B * N *
              ((1 + s) ^ (-1 / 2 : ℝ) * (1 + s) ^ (1 / 4 : ℝ))) := by
          rw [hKdef]; ring
      _ = Real.sqrt Real.pi * A * N * (1 + s) ^ (-3 / 4 : ℝ) +
            p.ε * (Real.sqrt Real.pi * B * N * (1 + s) ^ (-1 / 4 : ℝ)) := by
          rw [hp1, hp2]
      _ ≤ C * N * (1 + s) ^ (-3 / 4 : ℝ) + p.ε * (C * N * (1 + s) ^ (-1 / 4 : ℝ)) := by
          have h1 : Real.sqrt Real.pi * A * N ≤ C * N :=
            mul_le_mul_of_nonneg_right hAπ hN0
          have h2 : Real.sqrt Real.pi * B * N ≤ C * N :=
            mul_le_mul_of_nonneg_right hBπ hN0
          have h3 := mul_le_mul_of_nonneg_right h1 hq1
          have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hq2) hε.le
          linarith
      _ = C * N * ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ)) := by ring

/-- **`PartIII-a:T23/1`, conditional form** (SP 2703-2727): the five leaves give the late raw
coefficient bound. -/
theorem rawCoeffLate_of (h1 : LateFluctVel) (h2 : LateMeanVel) (h3 : LateFluctCompletion)
    (h4 : LateMeanCompletion) (h5 : RaisedStreamSplit) : RawCoeffLate :=
  rawCoeffLate_of_vel (lateVel_of h1 h2) (lateCompletion_of h3 h4 h5)

end UnforcedLeray.Short.IIIa
