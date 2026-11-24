import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge
import UnforcedLeray.Short.PartI.StatementsTrain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part III-a, `PartIII-a:T23/4`: the raw transverse tail (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`: "If `S = ε^{-b}` and `D_⊥ > 0` is fixed, the coefficient can also be
localized to `|η| ≤ L_⊥ = C_⊥(c/ν + √S + 1)` with `sup_{s<S, |η|>L_⊥} √s W(|v| + |v_flat|) ≤
e^{-D_⊥/ν}`. The Gaussian vorticity tail controls the heat-width part. The nonzero horizontal
stream kernels `e^{-|k_n||η|}/(2|k_n|)`, `|k_n| ≥ 2π/c`, control the `c/ν` part. The zero mode has
decaying heat primitives. Increasing `C_⊥` absorbs the fixed weights, derivative budgets ...").

Target: `RawTransverseTail` (`StressInputs.lean`), the train part of `stress-short:transverse`:
`√s W(|v_raw| + |v_flat|) ≤ e^{-D/ν}` on `0 < s < ε^{-b}`, `|η| > C_⊥(c/ν + √(ε^{-b}) + 1)`.

## The objects (no free data)

* `v_flat = p.train.v`: the velocity of the actual planar train (SP 2042, Proposition `sct:train`).
* `v_raw = chartCoeff p.R p.raw`: the raw field is the exact solenoidal lift of the train stream
  (SP 1205-1216, Proposition `sct:lift`; SP 2042-2043 "`V_0 = U_raw` its solenoidal lift"),
  `U_raw = √s(v + εH e_z)` (SP 5461), `H = (1 - η∂_η - 2s∂_s)ψ` (SP 1210).  In Lean
  `p.raw = axisExt (𝒩_v b_raw)` with `b_raw = rawProfile ε v ψ = v + εH e_z`
  (`Cons/L2/BackgroundConcrete/Fields.lean`, `Params.raw`; `Cons/C03Background/RawLift.lean`,
  `rawProfile`, `raisedStream`), and `chartCoeff p.R p.raw = b_raw` at `s > 0`
  (`Sub/T23_1_org/Bridge.lean`, `chartCoeff_raw`), so `|v_raw| ≤ |v| + ε|H|`
  (`norm_rawProfile_le`).
* The tails of `ψ, v` and their fixed derivatives are the Part I estimate `sct:transverse`
  (SP 463-467), proved in the source by exactly the three mechanisms SP 2750-2753 names
  (SP 494-510: Gaussian vorticity supersolutions, the nonzero-mode stream kernels
  `-e^{-|k_n||η|}/(2|k_n|)` split at distance `l/2`, and the two decaying zero-mode primitives
  `\bar v_1 = ∫_η^∞ \bar ω`, `S = ∫_η^∞ \bar v_1`).  Its constant `P_{S_*}` is polynomial in
  `c, ν⁻¹, 1+S_*` with degree fixed by the collection (SP 255-258); this uniformity is needed here
  because `S = ε^{-b} = e^{bd/ν}` grows with `ν⁻¹`.  `TrainTransverseTailsUniform` states it so;
  `PartI.TrainTransverseTails` (`Short/PartI/StatementsTrain.lean`) lets `C, N, ν₀` depend on
  `S_*` and is the special case `trainTransverseTails_of_uniform`.
* "Increasing `C_⊥` absorbs the fixed weights, derivative budgets" (SP 2754): the pure calculus
  `TailAbsorb` (split into the two exponentials, `TailAbsorbHeat`, `TailAbsorbGauss`).

## Contents

* leaf statements: `TrainVelTransverseTail` (task `PartIII-a:T23/4/1`), `RawChartTail` (`/2`),
  `RaisedStreamTransverseTail` (`/3`), `TailAbsorbHeat` (`/4`), `TailAbsorbGauss` (`/5`),
  `TrainTransverseTailsUniform` (Part I input; `/6/org`), `TailAbsorb`;
* helper lemmas (proved, namespace `T23Tail`): `transWeight_nonneg`, `transWeight_le_jap`,
  `norm_ageJet_zero_zero`, `abs_deriv_age_eq`, `abs_deriv_eta_le`, `abs_raisedStream_le`,
  `exp_add_one_div_le`;
* assembly (proved): `rawTransverseTail_of`, `rawChartTail_of`, `tailAbsorb_of`,
  `trainTransverseTails_of_uniform`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-! ## The leaf statements over the concrete level -/

/-- **(a) Transverse tail of the planar train velocity** (SP 2745-2753, the `|v_flat|` part of
`stress-short:transverse`; from `sct:transverse`, SP 463-467): for a window `[d₋, d₊]`,
`m_Z > 3/2`, `b > 0`, `D > 0` there are `C_⊥, ν₀` with, at every level of the regime with
`ν ≤ ν₀`, on `0 < s < ε^{-b}`, `|η| > C_⊥(c/ν + √(ε^{-b}) + 1)`:
`√s W |v_flat(s, q, η)| ≤ e^{-D/ν}/2`. -/
def TrainVelTransverseTail : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt * ‖p.train.v pt.1 pt.2‖ ≤ Real.exp (-D / p.ν) / 2

/-- **(b) Transverse tail of the raw chart coefficient** (SP 2745-2753, the `|v|` part of
`stress-short:transverse` for `V = U_raw`): same constants and region,
`√s W |v_raw(s, q, η)| ≤ e^{-D/ν}/2`, `v_raw = chartCoeff p.R p.raw = (v₁, v₂ + εH)` the profile of
the lift `U_raw = √s(v + εH e_z)` of the train stream (SP 1205-1216, 2042-2043, 5461). The
horizontal modes of `ψ, v` are controlled by the stream kernels and the zero mode by the decaying
primitives, inside `sct:transverse` (SP 494-510). Proved from (a) and (c) by `rawChartTail_of`. -/
def RawChartTail : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤ Real.exp (-D / p.ν) / 2

/-- **(c) Transverse tail of the stream completion** (SP 2729 "the stream completion
`ε(1-η∂_η-2s∂_s)ψ`", SP 2754 "increasing `C_⊥` absorbs the fixed weights, derivative budgets";
from `sct:transverse` for `ψ`, `D¹ψ`, `∂_sψ`, SP 463-467): same constants and region,
`√s W ε|H(s, q, η)| ≤ e^{-D/ν}/2`, `H = (1 - η∂_η - 2s∂_s)ψ` (`C03.raisedStream`). -/
def RaisedStreamTransverseTail : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt *
            (p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2|) ≤
          Real.exp (-D / p.ν) / 2

/-! ## The Part I input: `sct:transverse` with the source's polynomial `P_{S_*}` -/

/-- **`sct:transverse`, with `P_{S_*}` polynomial in `1+S_*`** (SP 463-467; SP 255-258: "The
letter `P` denotes a polynomial in `c, ν^{-1}`, with degree depending only on the fixed collection;
`P_S` may also depend polynomially on `1+S`. All the smallness conditions below are satisfied by
first fixing that collection and then decreasing `e_c`"): for `ρ > 1/2` and fixed orders `ℓ, j`
there are `b, C₀, C', C, N, ν₀` (independent of `S_*`) such that for every BUC train at
`(ν, c = ν^{-ρ})`, `ν ≤ ν₀`, every `S_* ≥ 0`, `l ≥ 0`, `0 < s ≤ S_*` and `|η| ≥ C'/ν + 2 + l`,
the jets `∂_s^ℓ D^j` of `ψ, v, ω, p` are bounded by
`C((1+c+ν⁻¹)(1+S_*))^N {e^{-bl/c} + e^{-bl²/(C₀+νS_*)}}`.  The source proves it by the Gaussian
vorticity supersolutions, the nonzero-mode stream kernels and the zero-mode primitives
(SP 487-510).  (The period is passed as `c` with `c = ν^{-ρ}`; `PartI.TrainTransverseTails` is the
weaker form with `C, N, ν₀` chosen after `S_*`.) -/
def TrainTransverseTailsUniform : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ (b C₀ C' C : ℝ) (N : ℕ) (ν₀ : ℝ),
    0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ c : ℝ, c = UnforcedLeray.Short.PartI.trainPeriod ρ ν →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ →
          ∀ z : UnforcedLeray.Cyl.Plane, C' / ν + 2 + l ≤ |z.2| →
            let K : ℝ := UnforcedLeray.Short.PartI.polyPS C N ν c S_ *
              (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
            ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.ψ s z‖ ≤ K ∧
              ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤ K ∧
              ‖UnforcedLeray.Short.PartI.ageJet ℓ j
                  (fun r w => UnforcedLeray.Cyl.curl (tr.v r) w) s z‖ ≤ K ∧
              ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.p s z‖ ≤ K

/-- The uniform form implies the Part I statement `PartI.TrainTransverseTails`. -/
theorem trainTransverseTails_of_uniform (h : TrainTransverseTailsUniform) :
    UnforcedLeray.Short.PartI.TrainTransverseTails := by
  intro ρ hρ ℓ j
  obtain ⟨b, C₀, C', C, N, ν₀, hb, hC₀, hC', hC, hν₀, hT⟩ := h ρ hρ ℓ j
  refine ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀,
    fun S_ hS ν hν hνle tr htr l hl s hs hsS z hz => ?_⟩
  exact hT ν hν hνle _ rfl tr htr S_ hS l hl s hs hsS z hz

/-! ## "Increasing `C_⊥` absorbs the fixed weights, derivative budgets" (SP 2754): calculus -/

/-- **Absorption of the heat-width exponential** (SP 2751-2754): for `b, D > 0`, `K ≥ 0` and
fixed powers `N, M, m` there are `C_⊥ > 0`, `ν₀ > 0` such that for `0 < ν ≤ ν₀`, `c = ν^{-2}`,
`1 ≤ S ≤ e^{K/ν}` and `|η| > C_⊥(c/ν + √S + 1)`, with `l = |η| - C'/ν - 2`:
`(1+S)^M (1+η²)^m · C((1+c+ν⁻¹)(1+S))^N e^{-bl/c} ≤ e^{-D/ν}/4`. -/
def TailAbsorbHeat : Prop :=
  ∀ (b C' C K D : ℝ) (N M m : ℕ), 0 < b → 0 < D → 0 ≤ K →
    ∃ (Cperp ν₀ : ℝ), 0 < Cperp ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ S : ℝ, 1 ≤ S → S ≤ Real.exp (K / ν) → ∀ η : ℝ,
        Cperp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) < |η| →
        (1 + S) ^ M * (1 + η ^ 2) ^ m *
            (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
              Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹))) ≤
          Real.exp (-D / ν) / 4

/-- **Absorption of the Gaussian exponential** (SP 2750, 2754): as `TailAbsorbHeat` with the
Gaussian factor `e^{-bl²/(C₀+νS)}`, `C₀ > 0`. -/
def TailAbsorbGauss : Prop :=
  ∀ (b C₀ C' C K D : ℝ) (N M m : ℕ), 0 < b → 0 < C₀ → 0 < D → 0 ≤ K →
    ∃ (Cperp ν₀ : ℝ), 0 < Cperp ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ S : ℝ, 1 ≤ S → S ≤ Real.exp (K / ν) → ∀ η : ℝ,
        Cperp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) < |η| →
        (1 + S) ^ M * (1 + η ^ 2) ^ m *
            (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
              Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S)))) ≤
          Real.exp (-D / ν) / 4

/-- **The absorbed `sct:transverse` bound** (SP 2754): both exponentials together, together with
the threshold `C'/ν + 2 ≤ |η|` at which `sct:transverse` applies with `l = |η| - C'/ν - 2 ≥ 0`. -/
def TailAbsorb : Prop :=
  ∀ (b C₀ C' C K D : ℝ) (N M m : ℕ), 0 < b → 0 < C₀ → 0 < D → 0 ≤ K →
    ∃ (Cperp ν₀ : ℝ), 0 < Cperp ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ S : ℝ, 1 ≤ S → S ≤ Real.exp (K / ν) → ∀ η : ℝ,
        Cperp * ((ν ^ 2)⁻¹ / ν + Real.sqrt S + 1) < |η| →
        C' / ν + 2 ≤ |η| ∧
        (1 + S) ^ M * (1 + η ^ 2) ^ m *
            (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
              (Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹)) +
                Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S))))) ≤
          Real.exp (-D / ν) / 2

/-! ## Helper lemmas -/

namespace T23Tail

theorem transWeight_nonneg (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) : 0 ≤ transWeight mZ p := by
  unfold transWeight
  positivity

/-- The transverse weight is at most `(1+η²)^{⌈m_Z/2⌉}` for `m_Z ≥ 0`, `s ≥ 0`. -/
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

/-- `‖∂_s⁰D⁰F(s)(z)‖ = ‖F(s, z)‖`. -/
theorem norm_ageJet_zero_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 0 F s z‖ = ‖F s z‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  rw [norm_iteratedFDeriv_zero, iteratedDeriv_zero]

/-- `|∂_sψ(s, z)| = ‖∂_s¹D⁰ψ(s)(z)‖`. -/
theorem abs_deriv_age_eq (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s : ℝ)
    (z : UnforcedLeray.Cyl.Plane) :
    |deriv (fun r => ψ r z) s| = ‖UnforcedLeray.Short.PartI.ageJet 1 0 ψ s z‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  rw [norm_iteratedFDeriv_zero, iteratedDeriv_one, Real.norm_eq_abs]

/-- `|∂_ηψ(s, q, η)| ≤ ‖D¹ψ(s)(q, η)‖` where `ψ(s)` is differentiable. -/
theorem abs_deriv_eta_le (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s q η : ℝ)
    (hf : DifferentiableAt ℝ (ψ s) (q, η)) :
    |deriv (fun t => ψ s (q, t)) η| ≤ ‖UnforcedLeray.Short.PartI.ageJet 0 1 ψ s (q, η)‖ := by
  have hj : UnforcedLeray.Short.PartI.ageJet 0 1 ψ s (q, η) =
      iteratedFDeriv ℝ 1 (ψ s) (q, η) := by
    unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
    congr 1
  rw [hj, norm_iteratedFDeriv_one]
  have hl : HasDerivAt (fun t : ℝ => ((q, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  have hc : HasDerivAt (fun t => ψ s (q, t)) (fderiv ℝ (ψ s) (q, η) ((0 : ℝ), (1 : ℝ))) η :=
    hf.hasFDerivAt.comp_hasDerivAt η hl
  rw [hc.deriv, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ (ψ s) (q, η) ((0 : ℝ), (1 : ℝ))‖
      ≤ ‖fderiv ℝ (ψ s) (q, η)‖ * ‖((0 : ℝ), (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (ψ s) (q, η)‖ := by
      rw [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one, mul_one]

theorem abs_sub_add_le3 (a b c : ℝ) : |a - (b + c)| ≤ |a| + (|b| + |c|) := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c]

/-- `|H| ≤ ‖ψ‖ + |η| ‖D¹ψ‖ + 2s ‖∂_sψ‖` for the stream completion `H = (1-η∂_η-2s∂_s)ψ` of a
train at age `s > 0` (SP 1210, 2729). -/
theorem abs_raisedStream_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 < s) (q η : ℝ) :
    |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
      ‖UnforcedLeray.Short.PartI.ageJet 0 0 tr.ψ s (q, η)‖ +
        |η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 tr.ψ s (q, η)‖ +
        2 * s * ‖UnforcedLeray.Short.PartI.ageJet 1 0 tr.ψ s (q, η)‖ := by
  have hd : DifferentiableAt ℝ (tr.ψ s) (q, η) :=
    (tr.isTrain.stream_differentiable s hs.le) (q, η)
  have h0 := norm_ageJet_zero_zero tr.ψ s (q, η)
  have h1 := abs_deriv_eta_le tr.ψ s q η hd
  have h2 := abs_deriv_age_eq tr.ψ s (q, η)
  rw [Real.norm_eq_abs] at h0
  unfold UnforcedLeray.Cons.C03.raisedStream
  rw [h0, ← h2]
  have hη := abs_nonneg η
  have e1 : |η * deriv (fun t => tr.ψ s (q, t)) η| ≤
      |η| * ‖UnforcedLeray.Short.PartI.ageJet 0 1 tr.ψ s (q, η)‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 hη
  have e2 : |2 * s * deriv (fun t => tr.ψ t (q, η)) s| =
      2 * s * |deriv (fun t => tr.ψ t (q, η)) s| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * s)]
  calc |tr.ψ s (q, η) - (η * deriv (fun t => tr.ψ s (q, t)) η +
          2 * s * deriv (fun t => tr.ψ t (q, η)) s)|
      ≤ |tr.ψ s (q, η)| + (|η * deriv (fun t => tr.ψ s (q, t)) η| +
          |2 * s * deriv (fun t => tr.ψ t (q, η)) s|) :=
        abs_sub_add_le3 _ _ _
    _ ≤ _ := by rw [e2]; linarith

/-- `e^{-(D+1)/ν} ≤ e^{-D/ν}/2` for `0 < ν ≤ 1`. -/
theorem exp_add_one_div_le {D ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Real.exp (-(D + 1) / ν) ≤ Real.exp (-D / ν) / 2 := by
  have h1ν : 1 ≤ 1 / ν := by rw [le_div_iff₀ hν]; linarith
  have hle : Real.exp (-1 / ν) ≤ Real.exp (-1) :=
    Real.exp_le_exp.2 (by rw [neg_div]; linarith)
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    linarith
  have hsplit : Real.exp (-(D + 1) / ν) = Real.exp (-D / ν) * Real.exp (-1 / ν) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hpos := Real.exp_pos (-D / ν)
  nlinarith

/-- The threshold bracket `c/ν + √S + 1` is nonnegative at a level. -/
theorem bracket_nonneg (p : Params) (bexp : ℝ) :
    0 ≤ p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1 := by
  have h1 : 0 < p.c / p.ν := div_pos p.c_pos p.ν_pos
  have h2 := Real.sqrt_nonneg (p.ε ^ (-bexp))
  linarith

end T23Tail

/-! ## Assembly -/

/-- **`PartIII-a:T23/4`, conditional form** (SP 2745-2753): the train and raw tails give
`RawTransverseTail` (`C_⊥ := max`, `ν₀ := min`, triangle inequality). -/
theorem rawTransverseTail_of (hA : TrainVelTransverseTail) (hB : RawChartTail) :
    RawTransverseTail := by
  intro dm dp hdm mZ hmZ bexp D hb hD
  obtain ⟨C1, n1, hn1, h1⟩ := hA dm dp hdm mZ hmZ bexp D hb hD
  obtain ⟨C2, n2, hn2, h2⟩ := hB dm dp hdm mZ hmZ bexp D hb hD
  refine ⟨max C1 C2, min n1 n2, lt_min hn1 hn2, fun p d hd hν pt hs hsS hη => ?_⟩
  have hX := T23Tail.bracket_nonneg p bexp
  have hη1 : C1 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) hη
  have hη2 : C2 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) hX) hη
  have e1 := h1 p d hd (hν.trans (min_le_left _ _)) pt hs hsS hη1
  have e2 := h2 p d hd (hν.trans (min_le_right _ _)) pt hs hsS hη2
  calc Real.sqrt pt.1 * transWeight mZ pt *
        (‖chartCoeff p.R p.raw pt‖ + ‖p.train.v pt.1 pt.2‖)
      = Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ +
          Real.sqrt pt.1 * transWeight mZ pt * ‖p.train.v pt.1 pt.2‖ := by ring
    _ ≤ Real.exp (-D / p.ν) / 2 + Real.exp (-D / p.ν) / 2 := add_le_add e2 e1
    _ = Real.exp (-D / p.ν) := by ring

/-- **(b) from (a) and (c)** (SP 1205-1216, 2729, 5461): `v_raw = v + εH e_z` at `s > 0`
(`chartCoeff_raw`), so `|v_raw| ≤ |v| + ε|H|`; apply (a), (c) with `D + 1` and
`e^{-(D+1)/ν} ≤ e^{-D/ν}/2` for `ν ≤ 1`. -/
theorem rawChartTail_of (hA : TrainVelTransverseTail) (hH : RaisedStreamTransverseTail) :
    RawChartTail := by
  intro dm dp hdm mZ hmZ bexp D hb hD
  obtain ⟨C1, n1, hn1, h1⟩ := hA dm dp hdm mZ hmZ bexp (D + 1) hb (by linarith)
  obtain ⟨C2, n2, hn2, h2⟩ := hH dm dp hdm mZ hmZ bexp (D + 1) hb (by linarith)
  refine ⟨max C1 C2, min (min n1 n2) 1, lt_min (lt_min hn1 hn2) one_pos,
    fun p d hd hν pt hs hsS hη => ?_⟩
  have hX := T23Tail.bracket_nonneg p bexp
  have hη1 : C1 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) hη
  have hη2 : C2 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) hX) hη
  have hν1 : p.ν ≤ n1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ n2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have e1 := h1 p d hd hν1 pt hs hsS hη1
  have e2 := h2 p d hd hν2 pt hs hsS hη2
  have hW : 0 ≤ Real.sqrt pt.1 * transWeight mZ pt :=
    mul_nonneg (Real.sqrt_nonneg _) (T23Tail.transWeight_nonneg mZ pt)
  have hnorm := norm_rawProfile_le p.ε p.train.v p.train.ψ pt
  have hε : |p.ε| = p.ε := abs_of_pos p.ε_pos
  rw [hε] at hnorm
  rw [chartCoeff_raw p hs]
  calc Real.sqrt pt.1 * transWeight mZ pt *
        ‖UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ pt‖
      ≤ Real.sqrt pt.1 * transWeight mZ pt * (‖p.train.v pt.1 pt.2‖ +
          p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2|) :=
        mul_le_mul_of_nonneg_left hnorm hW
    _ = Real.sqrt pt.1 * transWeight mZ pt * ‖p.train.v pt.1 pt.2‖ +
          Real.sqrt pt.1 * transWeight mZ pt *
            (p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2|) := by
        ring
    _ ≤ Real.exp (-(D + 1) / p.ν) / 2 + Real.exp (-(D + 1) / p.ν) / 2 := add_le_add e1 e2
    _ = Real.exp (-(D + 1) / p.ν) := by ring
    _ ≤ Real.exp (-D / p.ν) / 2 := T23Tail.exp_add_one_div_le p.ν_pos hν3

/-- **`TailAbsorb` from its two halves**: `C_⊥ := max(C_heat, C_gauss, |C'|+2)`,
`ν₀ := min(ν_heat, ν_gauss, 1)`; the threshold `C'/ν + 2 ≤ |η|` holds because
`c/ν = ν^{-3} ≥ ν^{-1}` and the bracket is `≥ 1`. -/
theorem tailAbsorb_of (h1 : TailAbsorbHeat) (h2 : TailAbsorbGauss) : TailAbsorb := by
  intro b C₀ C' C K D N M m hb hC₀ hD hK
  obtain ⟨A1, n1, hA1, hn1, e1⟩ := h1 b C' C K D N M m hb hD hK
  obtain ⟨A2, n2, hA2, hn2, e2⟩ := h2 b C₀ C' C K D N M m hb hC₀ hD hK
  have hApos : 0 < max (max A1 A2) (|C'| + 2) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨max (max A1 A2) (|C'| + 2), min (min n1 n2) 1, hApos,
    lt_min (lt_min hn1 hn2) one_pos, fun ν hν hνle S hS1 hSK η hη => ?_⟩
  have hν1 : ν ≤ n1 := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : ν ≤ n2 := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνone : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hinv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hνone
  have hc1 : 1 ≤ (ν ^ 2)⁻¹ := by
    rw [← inv_pow]; exact one_le_pow₀ hinv1
  have hcν : ν⁻¹ ≤ (ν ^ 2)⁻¹ / ν := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.2 hν]
  set X : ℝ := (ν ^ 2)⁻¹ / ν + Real.sqrt S + 1 with hX
  have hX1 : 1 ≤ X := by
    have := Real.sqrt_nonneg S
    have : 0 ≤ (ν ^ 2)⁻¹ / ν := by positivity
    linarith
  have hX0 : 0 ≤ X := by linarith
  have hthr1 : A1 * X < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) hX0) hη
  have hthr2 : A2 * X < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) hX0) hη
  have hthr3 : (|C'| + 2) * X < |η| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) hX0) hη
  refine ⟨?_, ?_⟩
  · have hCX : |C'| * ((ν ^ 2)⁻¹ / ν) ≤ |C'| * X := by
      have := Real.sqrt_nonneg S
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C')
    have hC'1 : C' / ν ≤ |C'| * ν⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_abs_self C') (inv_pos.2 hν).le
    have hC'2 : |C'| * ν⁻¹ ≤ |C'| * ((ν ^ 2)⁻¹ / ν) :=
      mul_le_mul_of_nonneg_left hcν (abs_nonneg C')
    nlinarith
  · have f1 := e1 ν hν hν1 S hS1 hSK η hthr1
    have f2 := e2 ν hν hν2 S hS1 hSK η hthr2
    calc (1 + S) ^ M * (1 + η ^ 2) ^ m *
          (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
            (Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹)) +
              Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S)))))
        = (1 + S) ^ M * (1 + η ^ 2) ^ m *
            (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
              Real.exp (-(b * (|η| - C' / ν - 2) / (ν ^ 2)⁻¹))) +
          (1 + S) ^ M * (1 + η ^ 2) ^ m *
            (UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ S *
              Real.exp (-(b * (|η| - C' / ν - 2) ^ 2 / (C₀ + ν * S)))) := by ring
      _ ≤ Real.exp (-D / ν) / 4 + Real.exp (-D / ν) / 4 := add_le_add f1 f2
      _ = Real.exp (-D / ν) / 2 := by ring

end UnforcedLeray.Short.IIIa
