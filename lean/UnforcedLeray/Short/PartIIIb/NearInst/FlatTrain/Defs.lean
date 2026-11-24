import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# The flat train multiplier bound: decomposition (source 2714-2729, 3566-3567)

Source of record: `the November 2 reference manuscript`.

`FlatTrainMultBound` (`NearInst/Targets.lean`) is the first line of `stress-short:coefficients`
(source 2716) for the flat train `v_flat = trainMer tr` (the planar train `B0140.TrainSol ν c`,
`c = ν⁻²`, as a chart coefficient, source 3566-3567, 3871-3872):
`sup √s W|v| ≤ P_ν`, `W = ⟨η/√(1+s)⟩^{m_Z}`.

## The class of the train

`FlatTrainMultBound` quantifies over *every* `tr : B0140.TrainSol ν c`.  The train of the source is
the Gallay-Slijepcevic solution in `BUC` (source 270-288, 2040: "Let `v_c` be the train of
Proposition `sct:train`"), and every Part I estimate (`StatementsTrain.lean`) is stated for the class
`PartI.IsBUCTrain`; `B0140.IsTrain` alone carries no time-uniform bound and does not determine the
train (`Short/PartI/TrainClass.lean`).  The bound is therefore stated and proved here for the BUC class:
`FlatTrainMultBoundBUC` is `FlatTrainMultBound` with `PartI.IsBUCTrain tr →` after the train binder.
Its consumer applies it at `p.trainData` under `IIb.BgRegime`, whose field `train_buc` supplies the
class.  (The correction of `Targets.lean` is a separate organize task.)

## The route (source 2722-2729)

`v = \bar v + \tilde v` with the horizontal mean `\bar v = PartI.hmean c v` and the fluctuation
`\tilde v = PartI.hfluct c v`:
* "Fluctuations have exponential decay after overlap; before overlap the Gaussian comparison gives
  the same polynomial bounds" (2726-2727): `sct:fluctuation` (`PartI.TrainFluctuationDecay`, 439-446)
  gives `⟨η⟩^m|\tilde v(s)| ≤ P e^{-κνs/c²}`, and `√s e^{-κνs/c²} ≤ (κν/c²)^{-1/2}` is polynomial in
  `ν⁻¹` (`FlatFluctBound`).
* "The mean stream and its fixed weighted derivatives have size `(1+s)^{-1/2}` on transverse scale
  `√(1+s)`; one transverse derivative gives the velocity size `(1+s)^{-1}`" (2722-2724):
  `\bar v₁ = -∂_η S`, `\bar v₂ = 0` (`sct:mean`, `PartI.TrainMeanEquations`, 397-404;
  `MeanVelNorm`) and `‖η^m ∂_η S(s)‖_∞ ≤ P(1+s)^{(m-2)/2}` (`sct:expansion`, last display,
  `PartI.TrainMeanExpansion`, 447-459; `MeanStreamDerivBound`), so that
  `W|\bar v| ≤ 2^n(|∂_ηS| + η^{2n}|∂_ηS|/(1+s)^n) ≤ P(1+s)^{-1}` and `√s(1+s)^{-1} ≤ 1`
  (`FlatMeanBound`).
* `trainMer` is measurable because the train is smooth on `[0,∞) × ℝ²` (`TrainMerMeasurable`).

The flat train has no compact-age inlet and no stream completion: those enter only the exact split
coefficient (`SplitMultBound`).

## Contents

* helper lemmas (proved): `trainPeriod_two`, `polyP_le_of_sq_inv`, `sqrt_mul_exp_neg_le`,
  `transWeight_le_sqrt_jap`, `transWeight_le_two_pow`, `abs_le_of_eLpNorm_top_le`, `norm_trainMer`;
* the leaf statements `TrainMerMeasurable`, `FlatFluctBound`, `MeanVelNorm`,
  `MeanStreamDerivBound`, `FlatMeanBound`;
* the assembly `flatTrainMultBoundBUC_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## The target for the BUC train -/

/-- **The actual train multiplier bound for the BUC train** (source 2714-2729 first line of
`stress-short:coefficients`, 3566-3567; the train of the source is the BUC train, 270-288, 2040):
`FlatTrainMultBound` with the class hypothesis `PartI.IsBUCTrain tr`.  For `m_Z > 3/2` there are
`C, k, ν₀` with `√s W |v_flat(s, q, η)| ≤ C ν^{-k}` for every BUC train at `(ν, ν⁻²)`, `ν ≤ ν₀`,
and every `s > 0`; `v_flat` is measurable. -/
def FlatTrainMultBoundBUC : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → Measurable (trainMer tr) ∧
      ∀ p : Chart, 0 < p.1 →
        Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ C * ν⁻¹ ^ k

/-! ## Helper lemmas -/

/-- `c = ν^{-2}`: the Part I period `trainPeriod 2 ν` is `(ν²)⁻¹` (source 2031). -/
theorem trainPeriod_two {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- The Part I polynomial `P = C(1+c+ν⁻¹)^N` at `c = ν⁻²`, `ν ≤ 1`, is at most
`|C| 3^N ν^{-2N}`. -/
theorem polyP_le_of_sq_inv (C : ℝ) (N : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
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

/-- `√s e^{-as} ≤ a^{-1/2}` for `a > 0`, `s ≥ 0` (absorbs the exponential age decay of the
fluctuation, source 2726-2727). -/
theorem sqrt_mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Real.sqrt s * Real.exp (-(a * s)) ≤ (Real.sqrt a)⁻¹ := by
  have has : 0 ≤ a * s := mul_nonneg ha.le hs
  have ht : Real.sqrt (a * s) ≤ Real.exp (a * s) := by
    have h1 := Real.add_one_le_exp (a * s)
    have h2 : Real.sqrt (a * s) ≤ a * s + 1 := by
      nlinarith [Real.sq_sqrt has, Real.sqrt_nonneg (a * s)]
    linarith
  rw [Real.sqrt_mul ha.le] at ht
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  rw [inv_mul_eq_div, le_div_iff₀ hsa]
  linarith [mul_comm (Real.sqrt a) (Real.sqrt s)]

/-- The transverse weight is at most `⟨η⟩^{⌈m_Z⌉}`: `W = (1 + η²/(1+s))^{m_Z/2} ≤ (1+η²)^{m/2}`,
`m = ⌈m_Z⌉₊`, `s ≥ 0` (`jap m z = (1+η²)^m`). -/
theorem transWeight_le_sqrt_jap {mZ : ℝ} (hmZ : 0 ≤ mZ) {p : Chart} (hs : 0 ≤ p.1) :
    UnforcedLeray.Short.IIIa.transWeight mZ p ≤
      Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ p.2) := by
  unfold UnforcedLeray.Short.IIIa.transWeight UnforcedLeray.Train.jap
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

/-- The transverse weight at transverse scale `√(1+s)`:
`W ≤ 2^n (1 + η^{2n}/(1+s)^n)`, `n = ⌈m_Z/2⌉₊`, `s ≥ 0`. -/
theorem transWeight_le_two_pow (mZ : ℝ) {s : ℝ} (hs : 0 ≤ s) (q η : ℝ) :
    UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) ≤
      2 ^ ⌈mZ / 2⌉₊ * (1 + η ^ (2 * ⌈mZ / 2⌉₊) / (1 + s) ^ ⌈mZ / 2⌉₊) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
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

/-- A continuous function is bounded pointwise by its `L^∞` norm. -/
theorem abs_le_of_eLpNorm_top_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : 0 ≤ K)
    (h : eLpNorm f ⊤ volume ≤ ENNReal.ofReal K) (x : ℝ) : |f x| ≤ K := by
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_exponent_top] at h
    exact (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun y hy => hy.trans h
  have hd : Dense {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} := Measure.dense_of_ae hae
  have hc : IsClosed {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} :=
    isClosed_le (continuous_enorm.comp hf) continuous_const
  have hx : x ∈ {y : ℝ | ‖f y‖ₑ ≤ ENNReal.ofReal K} := by
    rw [← hc.closure_eq, hd.closure_eq]; trivial
  have hx' : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal K := by
    rw [ofReal_norm]; exact hx
  rw [ENNReal.ofReal_le_ofReal_iff hK, Real.norm_eq_abs] at hx'
  exact hx'

/-- At nonnegative ages the flat coefficient is the train velocity. -/
theorem trainMer_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {p : Chart}
    (hp : 0 ≤ p.1) : trainMer tr p = tr.v p.1 p.2 := by
  ext i
  simp [trainMer, UnforcedLeray.Short.IIIa.trainVel, hp]

theorem norm_trainMer {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {p : Chart}
    (hp : 0 ≤ p.1) : ‖trainMer tr p‖ = ‖tr.v p.1 p.2‖ := by
  rw [trainMer_eq tr hp]

/-! ## The leaf statements -/

/-- **Measurability of the flat coefficient** (source 3566-3567; the train is smooth on
`[0,∞) × ℝ²`, 261-288, `B0140.IsTrain.smooth_v`; `trainMer` is `0` for `s < 0`). -/
def TrainMerMeasurable : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), Measurable (trainMer tr)

/-- **The fluctuation part of the flat train bound** (source 2726-2727 from `sct:fluctuation`,
439-446): for `m_Z ≥ 0` there are `C, k, ν₀` with `√s W |\tilde v(s, q, η)| ≤ C ν^{-k}` for every
BUC train at `(ν, ν⁻²)`, `ν ≤ ν₀`, `s > 0`. -/
def FlatFluctBound : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ p : Chart, 0 < p.1 →
        Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
            ‖UnforcedLeray.Short.PartI.hfluct c (tr.v p.1) p.2‖ ≤ C * ν⁻¹ ^ k

/-- **The mean velocity is the transverse derivative of the mean stream** (`sct:mean`, source
397-404: `\bar v₁ = -S_η`, `\bar v₂ = 0`): `|\bar v(s, η)| = |∂_η S(s, η)|` for `s > 0`. -/
def MeanVelNorm : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
      ‖UnforcedLeray.Short.PartI.hmean c (tr.v s) η‖ =
        |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|

/-- **Weighted sup bounds for the transverse derivative of the mean stream** (`sct:expansion`,
last display, source 456-459, with `b = 1`, `ℓ = 0`, `p = ∞`; source 2722-2724): for every `m`
there are `C, k, ν₀` with `|η|^m |∂_η S(s, η)| ≤ C ν^{-k} (1+s)^{(m-2)/2}` for every BUC train
at `(ν, ν⁻²)`, `ν ≤ ν₀`, `s > 0`. -/
def MeanStreamDerivBound : Prop :=
  ∀ m : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
        |η| ^ m * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
          C * ν⁻¹ ^ k * (1 + s) ^ (((m : ℝ) - 2) / 2)

/-- **The mean part of the flat train bound** (source 2722-2724: velocity size `(1+s)^{-1}` on
transverse scale `√(1+s)`): for `m_Z ≥ 0` there are `C, k, ν₀` with
`√s W |\bar v(s, η)| ≤ C ν^{-k}` for every BUC train at `(ν, ν⁻²)`, `ν ≤ ν₀`, `s > 0`. -/
def FlatMeanBound : Prop :=
  ∀ mZ : ℝ, 0 ≤ mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ p : Chart, 0 < p.1 →
        Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
            ‖UnforcedLeray.Short.PartI.hmean c (tr.v p.1) p.2.2‖ ≤ C * ν⁻¹ ^ k

/-! ## Assembly -/

/-- `C ν^{-k} ≤ max C 0 · ν^{-K}` for `k ≤ K`, `0 < ν ≤ 1`. -/
theorem mul_inv_pow_le_max {C ν : ℝ} {k K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hk : k ≤ K) :
    C * ν⁻¹ ^ k ≤ max C 0 * ν⁻¹ ^ K := by
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have hp : ν⁻¹ ^ k ≤ ν⁻¹ ^ K := pow_le_pow_right₀ h1 hk
  calc C * ν⁻¹ ^ k ≤ max C 0 * ν⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

/-- **Assembly** (source 2714-2729): measurability, the fluctuation part and the mean part give
the flat train multiplier bound for the BUC train. -/
theorem flatTrainMultBoundBUC_of (h1 : TrainMerMeasurable) (h2 : FlatFluctBound)
    (h3 : FlatMeanBound) : FlatTrainMultBoundBUC := by
  intro mZ hmZ
  have hmZ0 : 0 ≤ mZ := by linarith
  obtain ⟨C₂, k₂, ν₂, hν₂, hb₂⟩ := h2 mZ hmZ0
  obtain ⟨C₃, k₃, ν₃, hν₃, hb₃⟩ := h3 mZ hmZ0
  refine ⟨max C₂ 0 + max C₃ 0, max k₂ k₃, min (min ν₂ ν₃) 1, by positivity, ?_⟩
  intro ν hν c hc tr hbuc
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₂ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : ν ≤ ν₃ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  refine ⟨h1 ν c tr, fun p hp => ?_⟩
  have hF := hb₂ ν ⟨hν0, hνa⟩ c hc tr hbuc p hp
  have hM := hb₃ ν ⟨hν0, hνb⟩ c hc tr hbuc p hp
  have hF' := hF.trans (mul_inv_pow_le_max hν0 hν1 (le_max_left k₂ k₃))
  have hM' := hM.trans (mul_inv_pow_le_max hν0 hν1 (le_max_right k₂ k₃))
  have hW : 0 ≤ Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    positivity
  have hsplit : ‖trainMer tr p‖ ≤
      ‖UnforcedLeray.Short.PartI.hfluct c (tr.v p.1) p.2‖ +
        ‖UnforcedLeray.Short.PartI.hmean c (tr.v p.1) p.2.2‖ := by
    rw [norm_trainMer tr hp.le]
    have he : tr.v p.1 p.2 = UnforcedLeray.Short.PartI.hfluct c (tr.v p.1) p.2 +
        UnforcedLeray.Short.PartI.hmean c (tr.v p.1) p.2.2 := by
      unfold UnforcedLeray.Short.PartI.hfluct
      abel
    rw [he]
    exact norm_add_le _ _
  calc Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖
      ≤ Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
          (‖UnforcedLeray.Short.PartI.hfluct c (tr.v p.1) p.2‖ +
            ‖UnforcedLeray.Short.PartI.hmean c (tr.v p.1) p.2.2‖) :=
        mul_le_mul_of_nonneg_left hsplit hW
    _ = Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
          ‖UnforcedLeray.Short.PartI.hfluct c (tr.v p.1) p.2‖ +
        Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
          ‖UnforcedLeray.Short.PartI.hmean c (tr.v p.1) p.2.2‖ := by ring
    _ ≤ max C₂ 0 * ν⁻¹ ^ max k₂ k₃ + max C₃ 0 * ν⁻¹ ^ max k₂ k₃ := add_le_add hF' hM'
    _ = (max C₂ 0 + max C₃ 0) * ν⁻¹ ^ max k₂ k₃ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst
