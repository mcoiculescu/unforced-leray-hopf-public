import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge

/-!
# Part III-a, `PartIII-a:T23/2`: the early raw coefficient bound (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 2711-2738
(`stress-short:coefficients` and the paragraph "To check the age powers ..."), read at ages
`0 < s ≤ 1`; the train facts are Lemma `sct:heat` (lines 437-459: `sct:fluctuation` 439-446 and
`sct:expansion` 447-459, with "replacing the remainder power ... bounds `S` itself with `s`
replaced by `1+s`").

Target: `RawCoeffEarly` (`StressInputs.lean`): for ages `0 < s ≤ 1`,
`√s W|v_raw| ≤ P_ν √s` (the third bound of `stress-short:coefficients`, "early smoothness gives
the third bound", SP 2734-2735) and `‖W v_raw(s)‖_{L²_η L^∞_q} ≤ P_ν` (the fourth bound at
`s ≤ 1`, where `(1+s)^{-3/4} ≥ 2^{-3/4}`), `v_raw = chartCoeff p.R p.raw`,
`W = ⟨η/√(1+s)⟩^{m_Z}`.

## The route

* `v_raw = b_raw = (v₁, v₂ + εH)` with `H = (1 - η∂_η - 2s∂_s)ψ` the stream completion
  (`Sub/T23_1_org/Bridge.lean`, `chartCoeff_raw`, `norm_rawProfile_le`), so
  `|v_raw| ≤ |v| + ε|H|`, `ε ≤ 1`.
* "Early smoothness" (SP 2734-2735): at ages `0 < s ≤ 1` the train velocity `v = ∇^⊥ψ` and the
  stream completion `H` are bounded by `P_ν` with every fixed weight `⟨η⟩^m`.  This is the zero-age
  reading of `sct:heat`: the fluctuation obeys `P e^{-κνs/c²} ≤ P` at every age (`sct:fluctuation`
  is stated at all ages, so no Gaussian comparison `sct:comparison` is needed below age `1`; the
  comparison enters only the late range `1 ≤ s ≤ s_c` of `PartIII-a:T23/1`), and the mean stream
  `S` with its weighted derivatives is bounded by `P(1+s)^{…} ≤ 2^{…}P`.  In the drafts it is the
  Part II-a statement `PartIIa.EarlyStreamProfile` (`Short/PartII-a/Sub/R01.lean`, proved from
  `PartI.TrainFluctuationDecay`, `PartI.TrainMeanExpansion`, `PartIIa.LateProfileSmooth` as
  `PartIIa.earlyStreamProfile_of`).  The two leaves of this file are its readings for `v` and `H`:
  `EarlyVel` (`v₁ = -∂_ηψ`, `v₂ = ∂_qψ`) and `EarlyCompletion` (`ψ`, `η∂_ηψ`, `s∂_sψ`, the
  factor `|η|` absorbed by one more weight power).
* "The `L²_η` norm adds the factor `(1+s)^{1/4}`" (SP 2724): with one extra weight power,
  `∫ ⟨η/√(1+s)⟩^{-2} dη = π√(1+s) ≤ 2π` for `s ≤ 1`.

All leaves are stated for the BUC train of Part I at `(ν, c)`, `c = ν^{-2}`, the class in which the
Part I estimates hold (`BgRegime.train_buc`, SP 270-288, 2040).

## Contents

* leaf statements: `EarlyVel`, `EarlyCompletion` (tasks `PartIII-a:T23/2/1`, `/2`, to be proved
  from `PartIIa.EarlyStreamProfile` and `PartI.TrainStreamSmooth`);
* helper lemmas (proved, namespace `T23Early`, for the assembly and for the leaves):
  `transWeight_nonneg`, `transWeight_succ`, `const_mul_inv_pow_le`,
  `lintegral_inv_one_add_sq_div`, `transWeight_le_jap`, `rpow_neg_two`, `polyConst_two_le`,
  `norm_vec2_le`, `abs_le_one_add_sq`;
* assembly (proved): `rawCoeffEarly_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-! ## The leaf statements -/

/-- **Early smoothness of the train velocity** (SP 2734-2735, "early smoothness gives the third
bound"; the zero-age reading of `sct:fluctuation` 439-446 and `sct:expansion` 447-459, "bounds `S`
itself with `s` replaced by `1+s`"): for every weight exponent `m_Z ≥ 0` there are `C, k, ν₀`
with `W |v(s, q, η)| ≤ C ν^{-k}` for `0 < s ≤ 1`, for every BUC train at `(ν, ν^{-2})`,
`ν ≤ ν₀`.  (`v = ∇^⊥ψ = (-∂_ηψ, ∂_qψ)`; `PartIIa.EarlyStreamProfile` bounds
`(1+η²)^m |∂_ηψ|`, `(1+η²)^m |∂_qψ|` by `C(1+c+ν⁻¹)^d` on `0 < s ≤ 1`.) -/
def EarlyVel : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * ‖tr.v s (q, η)‖ ≤ C * ν⁻¹ ^ k

/-- **Early smoothness of the stream completion** (SP 2729-2731 and 2734-2735: the completion
`(1-η∂_η-2s∂_s)ψ` at ages `0 < s ≤ 1`; zero-age reading of `sct:fluctuation` and `sct:expansion`
for `ψ`, `∂_ηψ`, `∂_sψ`): for every `m_Z ≥ 0` there are `C, k, ν₀` with
`W |(1 - η∂_η - 2s∂_s)ψ(s, q, η)| ≤ C ν^{-k}` for `0 < s ≤ 1`, for every BUC train at
`(ν, ν^{-2})`, `ν ≤ ν₀` (`|η| ≤ 1+η²` absorbs the factor `η` into one more weight power, and
`s ≤ 1`). -/
def EarlyCompletion : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ q η : ℝ,
        transWeight mZ (s, (q, η)) * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
          C * ν⁻¹ ^ k

/-! ## Helper lemmas -/

namespace T23Early

theorem transWeight_nonneg (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) : 0 ≤ transWeight mZ p := by
  unfold transWeight
  positivity

/-- One more weight power: `W_{m+1} = W_m ⟨η/√(1+s)⟩`. -/
theorem transWeight_succ (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    transWeight (mZ + 1) p =
      transWeight mZ p * Real.sqrt (1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) := by
  unfold transWeight
  have hB : 0 < 1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 := by positivity
  rw [Real.sqrt_eq_rpow (1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2), ← Real.rpow_add hB]
  congr 1
  ring

/-- `C ν^{-k} ≤ max C 0 · ν^{-K}` for `k ≤ K`, `0 < ν ≤ 1`. -/
theorem const_mul_inv_pow_le {C ν : ℝ} {k K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hk : k ≤ K) :
    C * ν⁻¹ ^ k ≤ max C 0 * ν⁻¹ ^ K := by
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have hp : ν⁻¹ ^ k ≤ ν⁻¹ ^ K := pow_le_pow_right₀ h1 hk
  have hk0 : 0 ≤ ν⁻¹ ^ k := by positivity
  calc C * ν⁻¹ ^ k ≤ max C 0 * ν⁻¹ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
    _ ≤ max C 0 * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

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

/-- The transverse weight is at most `(1+η²)^{⌈m_Z/2⌉}` (the weight `(1+x.2.1²)^m` of
`PartIIa.EarlyStreamProfile`), for `m_Z ≥ 0`, `s ≥ 0`. -/
theorem transWeight_le_jap {mZ s : ℝ} (hmZ : 0 ≤ mZ) (hs : 0 ≤ s) (q η : ℝ) :
    transWeight mZ (s, (q, η)) ≤ (1 + η ^ 2) ^ ⌈mZ / 2⌉₊ := by
  unfold transWeight
  show (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2) ≤ (1 + η ^ 2) ^ ⌈mZ / 2⌉₊
  have h1s : 0 < 1 + s := by linarith
  have hx : (η / Real.sqrt (1 + s)) ^ 2 = η ^ 2 / (1 + s) := by
    rw [div_pow, Real.sq_sqrt h1s.le]
  rw [hx]
  have hx0 : 0 ≤ η ^ 2 / (1 + s) := div_nonneg (sq_nonneg η) h1s.le
  have hle : 1 + η ^ 2 / (1 + s) ≤ 1 + η ^ 2 := by
    have := div_le_self (sq_nonneg η) (show (1 : ℝ) ≤ 1 + s by linarith)
    linarith
  have hb1 : 1 ≤ 1 + η ^ 2 := by nlinarith [sq_nonneg η]
  calc (1 + η ^ 2 / (1 + s)) ^ (mZ / 2) ≤ (1 + η ^ 2) ^ (mZ / 2) :=
        Real.rpow_le_rpow (by linarith) hle (by linarith)
    _ ≤ (1 + η ^ 2) ^ (⌈mZ / 2⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (Nat.le_ceil _)
    _ = (1 + η ^ 2) ^ ⌈mZ / 2⌉₊ := Real.rpow_natCast _ _

/-- The period `ν^{-ρ}` at `ρ = 2` is `c = ν^{-2}` (SP 2031). -/
theorem rpow_neg_two {ν : ℝ} (hν : 0 < ν) : ν ^ (-(2 : ℝ)) = (ν ^ 2)⁻¹ := by
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- The polynomial constant `C(1+c+ν⁻¹)^d` (`PartIIa.polyConst C d ν c`) at `c = ν^{-2}`,
`0 < ν ≤ 1`, is at most `|C| 3^d ν^{-2d}`. -/
theorem polyConst_two_le (C : ℝ) (d : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    C * (1 + ν ^ (-(2 : ℝ)) + ν⁻¹) ^ d ≤ |C| * 3 ^ d * ν⁻¹ ^ (2 * d) := by
  rw [rpow_neg_two hν]
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have hb : 1 + (ν ^ 2)⁻¹ + ν⁻¹ ≤ 3 * ν⁻¹ ^ 2 := by
    rw [← inv_pow]; nlinarith
  have hb0 : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by positivity
  have hp : (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ d ≤ 3 ^ d * ν⁻¹ ^ (2 * d) := by
    calc (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ d ≤ (3 * ν⁻¹ ^ 2) ^ d := pow_le_pow_left₀ hb0 hb d
      _ = 3 ^ d * ν⁻¹ ^ (2 * d) := by rw [mul_pow, pow_mul]
  calc C * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ d ≤ |C| * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ d :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hb0 d)
    _ ≤ |C| * (3 ^ d * ν⁻¹ ^ (2 * d)) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = |C| * 3 ^ d * ν⁻¹ ^ (2 * d) := by ring

/-- `‖v‖ ≤ |v₀| + |v₁|` for a planar vector. -/
theorem norm_vec2_le (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  have h : |v 0| ^ 2 + |v 1| ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
  calc Real.sqrt (|v 0| ^ 2 + |v 1| ^ 2) ≤ Real.sqrt ((|v 0| + |v 1|) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = |v 0| + |v 1| := Real.sqrt_sq (by positivity)

/-- `|η| ≤ 1 + η²`: a factor `η` is absorbed by one more power of `1+η²`. -/
theorem abs_le_one_add_sq (η : ℝ) : |η| ≤ 1 + η ^ 2 := by
  nlinarith [sq_nonneg (|η| - 1), sq_abs η, abs_nonneg η]

end T23Early

/-! ## Assembly -/

/-- **`PartIII-a:T23/2`, conditional form** (SP 2711-2738 at ages `0 < s ≤ 1`): early
smoothness of the train velocity and of the stream completion give the early raw coefficient
bound. -/
theorem rawCoeffEarly_of (hV : EarlyVel) (hH : EarlyCompletion) : RawCoeffEarly := by
  intro dm dp hdm mZ hmZ
  have hmZ1 : 0 ≤ mZ + 1 := by linarith
  obtain ⟨A₀, k₁, ν₁, hν₁, H1⟩ := hV (mZ + 1) hmZ1
  obtain ⟨B₀, k₂, ν₂, hν₂, H2⟩ := hH (mZ + 1) hmZ1
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, max A₀ 0 = A := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, max B₀ 0 = B := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ le_max_right _ _
  have hB : 0 ≤ B := hBdef ▸ le_max_right _ _
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hπ : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hC1 : A + B ≤ (A + B) * (1 + Real.sqrt (2 * Real.pi)) := by nlinarith
  have hC2 : (A + B) * Real.sqrt (2 * Real.pi) ≤ (A + B) * (1 + Real.sqrt (2 * Real.pi)) := by
    nlinarith
  refine ⟨(A + B) * (1 + Real.sqrt (2 * Real.pi)), max k₁ k₂, min (min ν₁ ν₂) 1,
    lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro p d hreg hν
  have hν0 : 0 < p.ν := p.ν_pos
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hε : 0 < p.ε := p.ε_pos
  have hε1 : p.ε ≤ 1 := by
    have hd : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg hd.le hν0.le)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, p.ν⁻¹ ^ max k₁ k₂ = N := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hNdef ▸ pow_nonneg (inv_nonneg.2 hν0.le) _
  -- the pointwise bounds on the actual train, with one extra weight power
  have hv : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ q η : ℝ,
      transWeight (mZ + 1) (s, (q, η)) * ‖p.train.v s (q, η)‖ ≤ A * N := by
    intro s hs0 hs1 q η
    have h := (H1 p.ν ⟨hν0, hνa⟩ p.c hreg.c_eq p.train hreg.train_buc s hs0 hs1 q η).trans
      (T23Early.const_mul_inv_pow_le (C := A₀) hν0 hν1 (le_max_left k₁ k₂))
    rwa [hAdef, hNdef] at h
  have hh : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ q η : ℝ,
      transWeight (mZ + 1) (s, (q, η)) *
          |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η| ≤ B * N := by
    intro s hs0 hs1 q η
    have h := (H2 p.ν ⟨hν0, hνb⟩ p.c hreg.c_eq p.train hreg.train_buc s hs0 hs1 q η).trans
      (T23Early.const_mul_inv_pow_le (C := B₀) hν0 hν1 (le_max_right k₁ k₂))
    rwa [hBdef, hNdef] at h
  -- the weighted raw coefficient, with one weight power to spare
  have hcore : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ q η : ℝ,
      transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ *
          Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) ≤ (A + B) * N := by
    intro s hs0 hs1 q η
    have hb := norm_rawProfile_le p.ε p.train.v p.train.ψ (s, (q, η))
    rw [← chartCoeff_raw p (pt := (s, (q, η))) hs0, abs_of_pos hε] at hb
    have hW1 := T23Early.transWeight_succ mZ (s, (q, η))
    have hWg : 0 ≤ transWeight (mZ + 1) (s, (q, η)) := T23Early.transWeight_nonneg _ _
    calc transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ *
          Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2)
        = transWeight (mZ + 1) (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ := by
          rw [hW1]; ring
      _ ≤ transWeight (mZ + 1) (s, (q, η)) * (‖p.train.v s (q, η)‖ +
            p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) :=
          mul_le_mul_of_nonneg_left hb hWg
      _ = transWeight (mZ + 1) (s, (q, η)) * ‖p.train.v s (q, η)‖ +
            p.ε * (transWeight (mZ + 1) (s, (q, η)) *
              |UnforcedLeray.Cons.C03.raisedStream p.train.ψ s q η|) := by ring
      _ ≤ A * N + p.ε * (B * N) :=
          add_le_add (hv s hs0 hs1 q η) (mul_le_mul_of_nonneg_left (hh s hs0 hs1 q η) hε.le)
      _ ≤ A * N + 1 * (B * N) := by
          have := mul_le_mul_of_nonneg_right hε1 (mul_nonneg hB hN0)
          linarith
      _ = (A + B) * N := by ring
  refine ⟨?_, ?_⟩
  · -- `√s W|v| ≤ P_ν √s` for `0 < s ≤ 1`
    intro pt hs0 hs1
    obtain ⟨s, q, η⟩ := pt
    simp only at hs0 hs1 ⊢
    rw [hNdef]
    have hg1 : 1 ≤ Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) := by
      have h := Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ 1 + (η / Real.sqrt (1 + s)) ^ 2 by
          nlinarith [sq_nonneg (η / Real.sqrt (1 + s))])
      rwa [Real.sqrt_one] at h
    have hX0 : 0 ≤ transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ :=
      mul_nonneg (T23Early.transWeight_nonneg _ _) (norm_nonneg _)
    have hX : transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖ ≤ (A + B) * N :=
      (le_mul_of_one_le_right hX0 hg1).trans (hcore s hs0 hs1 q η)
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
    have hCN : (A + B) * N ≤ (A + B) * (1 + Real.sqrt (2 * Real.pi)) * N :=
      mul_le_mul_of_nonneg_right hC1 hN0
    calc Real.sqrt s * transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖
        = (transWeight mZ (s, (q, η)) * ‖chartCoeff p.R p.raw (s, (q, η))‖) * Real.sqrt s := by
          ring
      _ ≤ ((A + B) * N) * Real.sqrt s := mul_le_mul_of_nonneg_right hX hsq
      _ ≤ (A + B) * (1 + Real.sqrt (2 * Real.pi)) * N * Real.sqrt s :=
          mul_le_mul_of_nonneg_right hCN hsq
  · -- `‖W v(s)‖_{L²_η L^∞_q} ≤ P_ν` for `0 < s ≤ 1`
    intro s hs0 hs1
    have ha : 0 < 1 + s := by linarith
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, (A + B) * N = K := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := hKdef ▸ mul_nonneg hAB hN0
    have hgpos : ∀ η, 0 < Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2) := fun η =>
      Real.sqrt_pos.2 (by positivity)
    -- pointwise in `(q, η)`
    have hpt : ∀ η q : ℝ, ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖chartCoeff p.R p.raw (s, (q, η))‖ₑ ≤
          ENNReal.ofReal (K * (Real.sqrt (1 + (η / Real.sqrt (1 + s)) ^ 2))⁻¹) := by
      intro η q
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (T23Early.transWeight_nonneg _ _)]
      apply ENNReal.ofReal_le_ofReal
      have h := hcore s hs0 hs1 q η
      rw [hKdef] at h
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
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        T23Early.lintegral_inv_one_add_sq_div ha, ← ENNReal.ofReal_mul (sq_nonneg K)]
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
    rw [hNdef]
    have h4 : Real.sqrt (1 + s) ≤ 2 := by
      have h := Real.sqrt_le_sqrt (show 1 + s ≤ (2 : ℝ) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
    have hle : K ^ 2 * (Real.sqrt (1 + s) * Real.pi) ≤ K ^ 2 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 Real.pi_pos.le) (sq_nonneg K)
    calc (K ^ 2 * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ)
        = Real.sqrt (K ^ 2 * (Real.sqrt (1 + s) * Real.pi)) := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt (K ^ 2 * (2 * Real.pi)) := Real.sqrt_le_sqrt hle
      _ = K * Real.sqrt (2 * Real.pi) := by
          rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]
      _ = (A + B) * Real.sqrt (2 * Real.pi) * N := by rw [← hKdef]; ring
      _ ≤ (A + B) * (1 + Real.sqrt (2 * Real.pi)) * N := mul_le_mul_of_nonneg_right hC2 hN0

end UnforcedLeray.Short.IIIa
