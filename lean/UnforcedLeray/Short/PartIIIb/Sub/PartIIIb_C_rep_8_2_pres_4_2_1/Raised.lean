import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Org
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Weighted sup of the raised stream (task `PartIII-b:C/rep/8/2/pres/4/2/1/1/2`)

Source `the November 2 reference manuscript`:
2076-2077 (`H = ψ - η∂_ηψ - 2s∂_sψ`, `Cons.C03.raisedStream`), 5461-5463 (`U_raw = √s(v + εHe_z)`,
`H` with finite weighted train bounds), 2715-2725 (the mean stream and its fixed weighted
derivatives have size `(1+s)^{-1/2}`).

Route.  Split `ψ = S + ψ̃` (mean stream `S = \bar ψ`, fluctuation `ψ̃ = ψ - S`), so
`|H| ≤ |S| + |η∂_ηS| + 2s|∂_sS| + |ψ̃| + |η||∂_ηψ̃| + 2s|∂_sψ̃|`.
* Mean part (Part I `sct:expansion`, 447-459, `p = ∞`): `|S|, |η∂_ηS| ≤ P(1+s)^{-1/2}` and
  `|∂_sS| ≤ P(1+s)^{-3/2}`, so `√s` times the mean part is `≤ 4P`.
* Fluctuation part (Part I `sct:fluctuation`, 439-446): `⟨η⟩^m|∂_s^ℓD^jψ̃| ≤ Pe^{-κνs/c²}`,
  `c = ν⁻²`, and `√s(1+2s)e^{-κνs/c²} ≤ 8(1+κ⁻¹)²ν⁻¹⁰`.
* `ε = e^{-d/ν} ≤ 1` at the regime levels.

The Part I statements `TrainMeanExpansion`, `TrainFluctuationDecay` are the project-wide standing
hypotheses (`Short/PartI/StatementsTrain.lean`); they are explicit hypotheses of
`raisedWeightedSup_of` (the transverse tails and the fixed band are not needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RaisedSupAux

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

/-! ## Calculus helpers -/

/-- A continuous real function bounded a.e. by `B` is bounded everywhere by `B`. -/
theorem pw_of_ae_le {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ≥0∞}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ₑ ≤ B) (x : ℝ) : ‖f x‖ₑ ≤ B := by
  by_contra hx
  simp only [not_le] at hx
  have hU : IsOpen {y : ℝ | B < ‖f y‖ₑ} := isOpen_lt continuous_const hf.enorm
  have hpos : 0 < (volume : Measure ℝ) {y : ℝ | B < ‖f y‖ₑ} := hU.measure_pos volume ⟨x, hx⟩
  have hae : (volume : Measure ℝ) {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = 0 := ae_iff.1 h
  have hset : {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = {y : ℝ | B < ‖f y‖ₑ} := by
    ext y
    simp [not_le]
  rw [hset] at hae
  exact absurd hae (ne_of_gt hpos)

/-- An `eLpNorm ⊤` bound by `ofReal B` gives the pointwise real bound, for continuous `f`. -/
theorem norm_le_of_eLpNorm_top {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f ⊤ (volume : Measure ℝ) ≤ ENNReal.ofReal B) (x : ℝ) : ‖f x‖ ≤ B := by
  have h1 : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal B := by
    have h0 := enorm_ae_le_eLpNormEssSup f (volume : Measure ℝ)
    rw [← eLpNorm_exponent_top] at h0
    filter_upwards [h0] with y hy
    exact hy.trans h
  have h2 := pw_of_ae_le hf h1 x
  rw [Real.enorm_eq_ofReal_abs] at h2
  rw [Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h2

/-- A weighted sup bound gives the pointwise bound `⟨η⟩^m |f(z)| ≤ K`. -/
theorem le_of_wSupNorm {E : Type*} [NormedAddCommGroup E] {m : ℕ} {f : Plane → E} {K : ℝ}
    (hK : 0 ≤ K) (h : wSupNorm m f ≤ ENNReal.ofReal K) (z : Plane) :
    Real.sqrt (UnforcedLeray.Train.jap m z) * ‖f z‖ ≤ K := by
  have hle : ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ ≤ wSupNorm m f := by
    unfold wSupNorm
    exact le_iSup (fun z : Plane =>
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ) z
  have h2 := hle.trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 h2

/-- The period `trainPeriod 2 ν = (ν⁻¹)²`. -/
theorem trainPeriod_two_eq {ν : ℝ} (hν : 0 < ν) : trainPeriod 2 ν = (ν⁻¹) ^ 2 := by
  unfold trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]

theorem trainPeriod_two_pos {ν : ℝ} (hν : 0 < ν) : 0 < trainPeriod 2 ν := by
  rw [trainPeriod_two_eq hν]
  positivity

theorem polyP_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {ν : ℝ} (hν : 0 < ν) :
    0 ≤ polyP C N ν (trainPeriod 2 ν) := by
  unfold polyP
  have h1 := trainPeriod_two_pos hν
  have h2 := inv_pos.2 hν
  exact mul_nonneg hC (pow_nonneg (by linarith) N)

/-- Polynomial majorant: `polyP C N ν (ν⁻¹²) ≤ C 3^N ν⁻¹^(2N)` for `0 < ν ≤ 1`. -/
theorem polyP_le (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    polyP C N ν (trainPeriod 2 ν) ≤ C * 3 ^ N * (ν⁻¹) ^ (2 * N) := by
  rw [trainPeriod_two_eq hν]
  unfold polyP
  have hq1 : 1 ≤ ν⁻¹ := (one_le_inv_iff₀).2 ⟨hν, hν1⟩
  have h1 : 1 + (ν⁻¹) ^ 2 + ν⁻¹ ≤ 3 * (ν⁻¹) ^ 2 := by nlinarith
  have hbase : 0 ≤ 1 + (ν⁻¹) ^ 2 + ν⁻¹ := by nlinarith [sq_nonneg (ν⁻¹)]
  have h2 := pow_le_pow_left₀ hbase h1 N
  have h3 : (3 * (ν⁻¹) ^ 2) ^ N = 3 ^ N * (ν⁻¹) ^ (2 * N) := by
    rw [mul_pow, ← pow_mul]
  calc C * (1 + (ν⁻¹) ^ 2 + ν⁻¹) ^ N ≤ C * (3 * (ν⁻¹) ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left h2 hC
    _ = C * 3 ^ N * (ν⁻¹) ^ (2 * N) := by rw [h3, mul_assoc]

/-- `(1+x)² e^{-x} ≤ 4` for `x ≥ 0`. -/
theorem sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ 2 * Real.exp (-x) ≤ 4 := by
  have h1 : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2)
    linarith
  have h2 : (1 + x / 2) ^ 2 ≤ Real.exp x := by
    have h3 : Real.exp (x / 2) ^ 2 = Real.exp x := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [← h3]
    exact pow_le_pow_left₀ (by linarith) h1 2
  have h4 : (1 + x) ^ 2 ≤ 4 * Real.exp x := by nlinarith
  have h5 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  have h6 := mul_le_mul_of_nonneg_right h4 he.le
  linarith

/-- The fluctuation factor: `√s (1+2s) e^{-κνs/c²} ≤ 8 (1+κ⁻¹)² ν⁻¹^10` with `c = ν⁻²`,
`0 < ν ≤ 1`, `s ≥ 0`. -/
theorem fluct_factor {κ ν s c : ℝ} (hc : c = (ν⁻¹) ^ 2) (hκ : 0 < κ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hs : 0 ≤ s) :
    Real.sqrt s * (1 + 2 * s) * Real.exp (-(κ * ν * s / c ^ 2)) ≤
      8 * (1 + κ⁻¹) ^ 2 * (ν⁻¹) ^ 10 := by
  subst hc
  set q := ν⁻¹ with hq
  have hq1 : 1 ≤ q := (one_le_inv_iff₀).2 ⟨hν, hν1⟩
  have hq0 : 0 < q := by linarith
  set x := κ * ν * s / (q ^ 2) ^ 2 with hx
  set A := q ^ 5 * κ⁻¹ with hA
  have hνq : ν = q⁻¹ := by rw [hq, inv_inv]
  have hsA : s = A * x := by
    rw [hx, hA, hνq]
    field_simp
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hsq : Real.sqrt s ≤ 1 + s := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 := Real.sqrt_nonneg s
  have h1 : Real.sqrt s * (1 + 2 * s) ≤ 2 * (1 + s) ^ 2 := by
    calc Real.sqrt s * (1 + 2 * s) ≤ (1 + s) * (2 * (1 + s)) :=
          mul_le_mul hsq (by linarith) (by linarith) (by linarith)
      _ = 2 * (1 + s) ^ 2 := by ring
  have h2 : 1 + s ≤ (1 + A) * (1 + x) := by
    rw [hsA]
    nlinarith [mul_nonneg hA0 hx0]
  have h3 : (1 + s) ^ 2 ≤ (1 + A) ^ 2 * (1 + x) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h2 2
  have h4 : 1 + A ≤ (1 + κ⁻¹) * q ^ 5 := by
    have hq5 : 1 ≤ q ^ 5 := one_le_pow₀ hq1
    rw [hA]
    have hk : 0 ≤ κ⁻¹ := inv_nonneg.2 hκ.le
    nlinarith
  have h5 : (1 + A) ^ 2 ≤ (1 + κ⁻¹) ^ 2 * q ^ 10 := by
    calc (1 + A) ^ 2 ≤ ((1 + κ⁻¹) * q ^ 5) ^ 2 := pow_le_pow_left₀ (by linarith) h4 2
      _ = (1 + κ⁻¹) ^ 2 * q ^ 10 := by ring
  have he := Real.exp_pos (-x)
  have h6 := sq_mul_exp_neg_le hx0
  calc Real.sqrt s * (1 + 2 * s) * Real.exp (-x) ≤ 2 * (1 + s) ^ 2 * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h1 he.le
    _ ≤ 2 * ((1 + A) ^ 2 * (1 + x) ^ 2) * Real.exp (-x) := by
        apply mul_le_mul_of_nonneg_right _ he.le
        linarith
    _ = 2 * (1 + A) ^ 2 * ((1 + x) ^ 2 * Real.exp (-x)) := by ring
    _ ≤ 2 * (1 + A) ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ ≤ 2 * ((1 + κ⁻¹) ^ 2 * q ^ 10) * 4 := by linarith
    _ = 8 * (1 + κ⁻¹) ^ 2 * q ^ 10 := by ring

/-- `√s (1+s)^{-1/2} ≤ 1`. -/
theorem sqrt_mul_rpow_half {s e : ℝ} (hs : 0 ≤ s) (he : e = -(1 / 2)) :
    Real.sqrt s * (1 + s) ^ e ≤ 1 := by
  subst he
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 1 + s by linarith), ← Real.sqrt_eq_rpow,
    ← div_eq_mul_inv]
  have hp : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
  rw [div_le_one hp]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `√s · 2s (1+s)^{-3/2} ≤ 2`. -/
theorem sqrt_mul_rpow_three_half {s e : ℝ} (hs : 0 ≤ s) (he : e = -(3 / 2)) :
    Real.sqrt s * (2 * s * (1 + s) ^ e) ≤ 2 := by
  subst he
  have h1s : 0 < 1 + s := by linarith
  have hsplit : (1 + s) ^ (-(3 / 2) : ℝ) = (1 + s) ^ (-1 : ℝ) * (1 + s) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add h1s]
    norm_num
  rw [hsplit, Real.rpow_neg_one]
  have hA : s * (1 + s)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one h1s]
    linarith
  have hB := sqrt_mul_rpow_half (e := -(1 / 2)) hs rfl
  have hA0 : 0 ≤ s * (1 + s)⁻¹ := mul_nonneg hs (inv_nonneg.2 h1s.le)
  have hB0 : 0 ≤ Real.sqrt s * (1 + s) ^ (-(1 / 2) : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg h1s.le _)
  calc Real.sqrt s * (2 * s * ((1 + s)⁻¹ * (1 + s) ^ (-(1 / 2) : ℝ)))
      = 2 * (s * (1 + s)⁻¹) * (Real.sqrt s * (1 + s) ^ (-(1 / 2) : ℝ)) := by ring
    _ ≤ 2 * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB hB0 (by norm_num)
    _ = 2 := by ring

/-! ## Jet helpers -/

/-- `‖∂_s⁰D⁰F(s)(z)‖ = ‖F(s, z)‖`. -/
theorem norm_ageJet_zero_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → Plane → E) (s : ℝ) (z : Plane) : ‖ageJet 0 0 F s z‖ = ‖F s z‖ := by
  unfold ageJet UnforcedLeray.Train.jet
  rw [norm_iteratedFDeriv_zero, iteratedDeriv_zero]

/-- `|∂_sψ(s, z)| = ‖∂_s¹D⁰ψ(s)(z)‖`. -/
theorem abs_deriv_age_eq (ψ : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) :
    |deriv (fun r => ψ r z) s| = ‖ageJet 1 0 ψ s z‖ := by
  unfold ageJet UnforcedLeray.Train.jet
  rw [norm_iteratedFDeriv_zero, iteratedDeriv_one, Real.norm_eq_abs]

/-- `|∂_ηψ(s, q, η)| ≤ ‖D¹ψ(s)(q, η)‖` where `ψ(s)` is differentiable. -/
theorem abs_deriv_eta_le (ψ : ℝ → Plane → ℝ) (s q η : ℝ)
    (hf : DifferentiableAt ℝ (ψ s) (q, η)) :
    |deriv (fun t => ψ s (q, t)) η| ≤ ‖ageJet 0 1 ψ s (q, η)‖ := by
  have hj : ageJet 0 1 ψ s (q, η) = iteratedFDeriv ℝ 1 (ψ s) (q, η) := by
    unfold ageJet UnforcedLeray.Train.jet
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

/-! ## The Part I inputs, read pointwise -/

/-- The mean-stream bound of `sct:expansion` at `p = ∞`, read pointwise along a continuous slice. -/
theorem mean_pt (hM : TrainMeanExpansion) (m b ℓ : ℕ) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ c : ℝ, c = trainPeriod 2 ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
        ∀ s : ℝ, 0 < s →
          Continuous (fun η : ℝ => η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η) →
          ∀ η : ℝ, |η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
            polyP C M ν c * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  obtain ⟨C, M, ν₀, hC, hν₀, hb⟩ := hM 2 (by norm_num) 0 m b ℓ ⊤ le_top
  refine ⟨C, M, ν₀, hC, hν₀, ?_⟩
  intro ν hν hνle c hc tr htr s hs hcont η
  subst hc
  obtain ⟨-, -, -, hb2⟩ := hb ν hν hνle tr htr
  have hb3 := hb2 s hs.le
  simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero] at hb3
  have hB : 0 ≤ polyP C M ν (trainPeriod 2 ν) * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) :=
    mul_nonneg (polyP_nonneg hC.le M hν) (Real.rpow_nonneg (by linarith) _)
  have := norm_le_of_eLpNorm_top hcont hB hb3 η
  rwa [Real.norm_eq_abs] at this

/-- The fluctuation bound of `sct:fluctuation` for the stream, read pointwise. -/
theorem fluct_pt (hF : TrainFluctuationDecay) (m ℓ j : ℕ) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ c : ℝ, c = trainPeriod 2 ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → ∀ z : Plane,
          Real.sqrt (UnforcedLeray.Train.jap m z) *
            ‖ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s z‖ ≤
            polyP C N ν c * Real.exp (-(κ * ν * s / c ^ 2)) := by
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, hb⟩ := hF 2 (by norm_num) m ℓ j
  refine ⟨C, N, κ, ν₀, hC, hκ, hν₀, ?_⟩
  intro ν hν hνle c hc tr htr s hs z
  subst hc
  have h := (hb ν hν hνle tr htr s hs).1.2
  exact le_of_wSupNorm (mul_nonneg (polyP_nonneg hC.le N hν) (Real.exp_pos _).le) h z

/-- `C a^i ≤ C a^K` for `a ≥ 1`, `C ≥ 0`, `i ≤ K`. -/
theorem le_pow_max {a C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C) {i K : ℕ} (h : i ≤ K) :
    C * a ^ i ≤ C * a ^ K :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha h) hC

theorem abs_six_le (a1 a2 a3 a4 a5 a6 s : ℝ) (hs : 0 ≤ s) :
    |(a1 + a2) - (a3 + a4 + 2 * s * (a5 + a6))| ≤
      |a1| + |a2| + |a3| + |a4| + 2 * s * |a5| + 2 * s * |a6| := by
  have h5 : |2 * s * a5| = 2 * s * |a5| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s)]
  have h6 : |2 * s * a6| = 2 * s * |a6| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s)]
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a1, neg_abs_le a1, le_abs_self a2, neg_abs_le a2,
      le_abs_self a3, neg_abs_le a3, le_abs_self a4, neg_abs_le a4,
      le_abs_self (2 * s * a5), neg_abs_le (2 * s * a5),
      le_abs_self (2 * s * a6), neg_abs_le (2 * s * a6)]

/-! ## The bound for one train -/

set_option maxHeartbeats 1000000 in
/-- For a BUC train at `c = ν⁻²` with jointly smooth stream, `√s |H(s, ξ, η)| ≤ Cν^{-k}` for every
age `s > 0` and point `(ξ, η)`, `ν ≤ ν₀`. -/
theorem raised_core (hM : TrainMeanExpansion) (hF : TrainFluctuationDecay) :
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ν ≤ 1 →
      ∀ c : ℝ, c = trainPeriod 2 ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) →
      ∀ s ξ η : ℝ, 0 < s →
        Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s ξ η| ≤ C * ν⁻¹ ^ k := by
  obtain ⟨CA, MA, νA, hCA, hνA, hA⟩ := mean_pt hM 0 0 0
  obtain ⟨CB, MB, νB, hCB, hνB, hB⟩ := mean_pt hM 1 1 0
  obtain ⟨CC, MC, νC, hCC, hνC, hC⟩ := mean_pt hM 0 0 1
  obtain ⟨CF0, N0, κ0, ν0, hCF0, hκ0, hν0, hF0⟩ := fluct_pt hF 0 0 0
  obtain ⟨CF1, N1, κ1, ν1, hCF1, hκ1, hν1, hF1⟩ := fluct_pt hF 1 0 1
  obtain ⟨CF2, N2, κ2, ν2, hCF2, hκ2, hν2, hF2⟩ := fluct_pt hF 0 1 0
  refine ⟨CA * 3 ^ MA + CB * 3 ^ MB + 2 * (CC * 3 ^ MC) +
      CF0 * 3 ^ N0 * (8 * (1 + κ0⁻¹) ^ 2) + CF1 * 3 ^ N1 * (8 * (1 + κ1⁻¹) ^ 2) +
      CF2 * 3 ^ N2 * (8 * (1 + κ2⁻¹) ^ 2),
    2 * (MA + MB + MC + N0 + N1 + N2) + 10,
    min (min (min νA νB) (min νC ν0)) (min ν1 ν2),
    lt_min (lt_min (lt_min hνA hνB) (lt_min hνC hν0)) (lt_min hν1 hν2), ?_⟩
  intro ν hν hνle hνone c hc tr htr hψ s ξ η hs
  simp only [le_min_iff] at hνle
  obtain ⟨⟨⟨eA, eB⟩, ⟨eC, eF0⟩⟩, ⟨eF1, eF2⟩⟩ := hνle
  set K := 2 * (MA + MB + MC + N0 + N1 + N2) + 10 with hK
  have hcpos : 0 < c := by rw [hc]; exact trainPeriod_two_pos hν
  have ha1 : 1 ≤ ν⁻¹ := (one_le_inv_iff₀).2 ⟨hν, hνone⟩
  have hca : c = ν⁻¹ ^ 2 := hc.trans (trainPeriod_two_eq hν)
  -- smoothness of the mean stream
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hcpos tr.ψ hψ
  have hSs : ContDiff ℝ ∞ (fun e : ℝ => meanStream tr s e) := t01_contDiff_slice hS hs
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hopen1 : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hopen2 : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  -- differentiability facts
  have dSη : DifferentiableAt ℝ (fun e : ℝ => meanStream tr s e) η :=
    (hSs.differentiable hne) η
  have dSs : DifferentiableAt ℝ (fun r : ℝ => meanStream tr r η) s := by
    have hm : ((s, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ _⟩
    have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (s, η) :=
      hS.contDiffAt (hopen1.mem_nhds hm)
    have hl : DifferentiableAt ℝ (fun r : ℝ => ((r, η) : ℝ × ℝ)) s :=
      differentiableAt_id.prodMk (differentiableAt_const η)
    have h2 := (h0.differentiableAt hne).comp s hl
    exact h2
  have dψz : DifferentiableAt ℝ (tr.ψ s) (ξ, η) :=
    (tr.isTrain.stream_differentiable s hs.le) (ξ, η)
  have dψη : DifferentiableAt ℝ (fun t : ℝ => tr.ψ s (ξ, t)) η := by
    have hl : DifferentiableAt ℝ (fun t : ℝ => ((ξ, t) : Plane)) η :=
      (differentiableAt_const ξ).prodMk differentiableAt_id
    have h2 := dψz.comp η hl
    exact h2
  have dψs : DifferentiableAt ℝ (fun r : ℝ => tr.ψ r (ξ, η)) s := by
    have hm : ((s, (ξ, η)) : ℝ × Plane) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) :=
      ⟨hs, mem_univ _⟩
    have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (s, (ξ, η)) :=
      hψ.contDiffAt (hopen2.mem_nhds hm)
    have hl : DifferentiableAt ℝ (fun r : ℝ => ((r, (ξ, η)) : ℝ × Plane)) s :=
      differentiableAt_id.prodMk (differentiableAt_const (ξ, η))
    have h2 := (h0.differentiableAt hne).comp s hl
    exact h2
  -- the fluctuation `ψ̃ = ψ - S`
  set F : ℝ → Plane → ℝ := fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2 with hFdef
  have dFz : DifferentiableAt ℝ (F s) (ξ, η) := by
    have hsnd : DifferentiableAt ℝ (fun z : Plane => z.2) (ξ, η) := differentiableAt_snd
    have h1 := dSη.comp (ξ, η) hsnd
    have h3 := dψz.sub h1
    exact h3
  -- splitting `ψ`, `∂_ηψ`, `∂_sψ`
  have sψ : tr.ψ s (ξ, η) = F s (ξ, η) + meanStream tr s η := by
    show tr.ψ s (ξ, η) = (tr.ψ s (ξ, η) - hmean c (tr.ψ s) η) + hmean c (tr.ψ s) η
    ring
  have sη : deriv (fun t => tr.ψ s (ξ, t)) η =
      deriv (fun t => F s (ξ, t)) η + deriv (fun e => meanStream tr s e) η := by
    have hfun : (fun t => F s (ξ, t)) = fun t => tr.ψ s (ξ, t) - meanStream tr s t := rfl
    rw [hfun, deriv_fun_sub dψη dSη]
    ring
  have ss : deriv (fun r => tr.ψ r (ξ, η)) s =
      deriv (fun r => F r (ξ, η)) s + deriv (fun r => meanStream tr r η) s := by
    have hfun : (fun r => F r (ξ, η)) = fun r => tr.ψ r (ξ, η) - meanStream tr r η := rfl
    rw [hfun, deriv_fun_sub dψs dSs]
    ring
  have hH : UnforcedLeray.Cons.C03.raisedStream tr.ψ s ξ η =
      (F s (ξ, η) + meanStream tr s η) -
        (η * deriv (fun t => F s (ξ, t)) η + η * deriv (fun e => meanStream tr s e) η +
          2 * s * (deriv (fun r => F r (ξ, η)) s + deriv (fun r => meanStream tr r η) s)) := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    rw [sψ, sη, ss]
    ring
  have hHle : |UnforcedLeray.Cons.C03.raisedStream tr.ψ s ξ η| ≤
      |F s (ξ, η)| + |meanStream tr s η| + |η| * |deriv (fun t => F s (ξ, t)) η| +
        |η * deriv (fun e => meanStream tr s e) η| + 2 * s * |deriv (fun r => F r (ξ, η)) s| +
        2 * s * |deriv (fun r => meanStream tr r η) s| := by
    rw [hH, ← abs_mul]
    exact abs_six_le _ _ _ _ _ _ s hs.le
  -- the mean bounds
  have mA : |meanStream tr s η| ≤ polyP CA MA ν c * (1 + s) ^ (-(1 / 2) : ℝ) := by
    have hcont : Continuous (fun η : ℝ => η ^ 0 * iteratedDeriv 0
        (fun e => iteratedDeriv 0 (fun r => meanStream tr r e) s) η) := by
      simp only [pow_zero, one_mul, iteratedDeriv_zero]
      exact hSs.continuous
    have h := hA ν hν eA c hc tr htr s hs hcont η
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    convert h using 3
    norm_num
  have mB : |η * deriv (fun e => meanStream tr s e) η| ≤
      polyP CB MB ν c * (1 + s) ^ (-(1 / 2) : ℝ) := by
    have hcont : Continuous (fun η : ℝ => η ^ 1 * iteratedDeriv 1
        (fun e => iteratedDeriv 0 (fun r => meanStream tr r e) s) η) := by
      simp only [pow_one, iteratedDeriv_one, iteratedDeriv_zero]
      exact continuous_id.mul (hSs.continuous_deriv hone)
    have h := hB ν hν eB c hc tr htr s hs hcont η
    simp only [pow_one, iteratedDeriv_one, iteratedDeriv_zero] at h
    convert h using 3
    norm_num
  have mC : |deriv (fun r => meanStream tr r η) s| ≤
      polyP CC MC ν c * (1 + s) ^ (-(3 / 2) : ℝ) := by
    have hcont : Continuous (fun η : ℝ => η ^ 0 * iteratedDeriv 0
        (fun e => iteratedDeriv 1 (fun r => meanStream tr r e) s) η) := by
      simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one]
      exact t01_continuous_deriv_slice hS hs
    have h := hC ν hν eC c hc tr htr s hs hcont η
    simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one] at h
    convert h using 3
    norm_num
  -- the fluctuation bounds
  have hj0 : Real.sqrt (UnforcedLeray.Train.jap 0 (ξ, η)) = 1 := by
    simp [UnforcedLeray.Train.jap]
  have fA : |F s (ξ, η)| ≤ polyP CF0 N0 ν c * Real.exp (-(κ0 * ν * s / c ^ 2)) := by
    have h : Real.sqrt (UnforcedLeray.Train.jap 0 (ξ, η)) * ‖ageJet 0 0 F s (ξ, η)‖ ≤
        polyP CF0 N0 ν c * Real.exp (-(κ0 * ν * s / c ^ 2)) :=
      hF0 ν hν eF0 c hc tr htr s hs (ξ, η)
    rw [hj0, one_mul, norm_ageJet_zero_zero, Real.norm_eq_abs] at h
    exact h
  have fB : |η| * |deriv (fun t => F s (ξ, t)) η| ≤
      polyP CF1 N1 ν c * Real.exp (-(κ1 * ν * s / c ^ 2)) := by
    have h : Real.sqrt (UnforcedLeray.Train.jap 1 (ξ, η)) * ‖ageJet 0 1 F s (ξ, η)‖ ≤
        polyP CF1 N1 ν c * Real.exp (-(κ1 * ν * s / c ^ 2)) :=
      hF1 ν hν eF1 c hc tr htr s hs (ξ, η)
    have hj := abs_deriv_eta_le F s ξ η dFz
    have hη : |η| ≤ Real.sqrt (UnforcedLeray.Train.jap 1 (ξ, η)) := by
      apply Real.abs_le_sqrt
      show η ^ 2 ≤ (1 + η ^ 2) ^ 1
      rw [pow_one]
      linarith
    calc |η| * |deriv (fun t => F s (ξ, t)) η|
        ≤ Real.sqrt (UnforcedLeray.Train.jap 1 (ξ, η)) * ‖ageJet 0 1 F s (ξ, η)‖ :=
          mul_le_mul hη hj (abs_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ _ := h
  have fC : |deriv (fun r => F r (ξ, η)) s| ≤
      polyP CF2 N2 ν c * Real.exp (-(κ2 * ν * s / c ^ 2)) := by
    have h : Real.sqrt (UnforcedLeray.Train.jap 0 (ξ, η)) * ‖ageJet 1 0 F s (ξ, η)‖ ≤
        polyP CF2 N2 ν c * Real.exp (-(κ2 * ν * s / c ^ 2)) :=
      hF2 ν hν eF2 c hc tr htr s hs (ξ, η)
    rw [hj0, one_mul, ← abs_deriv_age_eq] at h
    exact h
  -- the scalar factors
  have hsq0 := Real.sqrt_nonneg s
  have qA := sqrt_mul_rpow_half (e := (-(1 / 2) : ℝ)) hs.le rfl
  have qC := sqrt_mul_rpow_three_half (e := (-(3 / 2) : ℝ)) hs.le rfl
  have pA : polyP CA MA ν c ≤ CA * 3 ^ MA * ν⁻¹ ^ (2 * MA) := by
    rw [hc]; exact polyP_le CA hCA.le MA ν hν hνone
  have pB : polyP CB MB ν c ≤ CB * 3 ^ MB * ν⁻¹ ^ (2 * MB) := by
    rw [hc]; exact polyP_le CB hCB.le MB ν hν hνone
  have pC : polyP CC MC ν c ≤ CC * 3 ^ MC * ν⁻¹ ^ (2 * MC) := by
    rw [hc]; exact polyP_le CC hCC.le MC ν hν hνone
  have pF0 : polyP CF0 N0 ν c ≤ CF0 * 3 ^ N0 * ν⁻¹ ^ (2 * N0) := by
    rw [hc]; exact polyP_le CF0 hCF0.le N0 ν hν hνone
  have pF1 : polyP CF1 N1 ν c ≤ CF1 * 3 ^ N1 * ν⁻¹ ^ (2 * N1) := by
    rw [hc]; exact polyP_le CF1 hCF1.le N1 ν hν hνone
  have pF2 : polyP CF2 N2 ν c ≤ CF2 * 3 ^ N2 * ν⁻¹ ^ (2 * N2) := by
    rw [hc]; exact polyP_le CF2 hCF2.le N2 ν hν hνone
  have xF0 := fluct_factor hca hκ0 hν hνone hs.le
  have xF1 := fluct_factor hca hκ1 hν hνone hs.le
  have xF2 := fluct_factor hca hκ2 hν hνone hs.le
  have P0A : 0 ≤ polyP CA MA ν c := by
    rw [hc]; exact polyP_nonneg hCA.le MA hν
  have P0B : 0 ≤ polyP CB MB ν c := by
    rw [hc]; exact polyP_nonneg hCB.le MB hν
  have P0C : 0 ≤ polyP CC MC ν c := by
    rw [hc]; exact polyP_nonneg hCC.le MC hν
  have P0F0 : 0 ≤ polyP CF0 N0 ν c := by
    rw [hc]; exact polyP_nonneg hCF0.le N0 hν
  have P0F1 : 0 ≤ polyP CF1 N1 ν c := by
    rw [hc]; exact polyP_nonneg hCF1.le N1 hν
  have P0F2 : 0 ≤ polyP CF2 N2 ν c := by
    rw [hc]; exact polyP_nonneg hCF2.le N2 hν
  have hex0 := Real.exp_pos (-(κ0 * ν * s / c ^ 2))
  have hex1 := Real.exp_pos (-(κ1 * ν * s / c ^ 2))
  have hex2 := Real.exp_pos (-(κ2 * ν * s / c ^ 2))
  have h12 : Real.sqrt s ≤ Real.sqrt s * (1 + 2 * s) := by
    have : 1 ≤ 1 + 2 * s := by linarith
    nlinarith
  have h2s : Real.sqrt s * (2 * s) ≤ Real.sqrt s * (1 + 2 * s) := by
    apply mul_le_mul_of_nonneg_left _ hsq0
    linarith
  -- term by term
  have TA : Real.sqrt s * |meanStream tr s η| ≤ CA * 3 ^ MA * ν⁻¹ ^ (2 * MA) := by
    calc Real.sqrt s * |meanStream tr s η|
        ≤ Real.sqrt s * (polyP CA MA ν c * (1 + s) ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left mA hsq0
      _ = polyP CA MA ν c * (Real.sqrt s * (1 + s) ^ (-(1 / 2) : ℝ)) := by ring
      _ ≤ polyP CA MA ν c * 1 := mul_le_mul_of_nonneg_left qA P0A
      _ ≤ CA * 3 ^ MA * ν⁻¹ ^ (2 * MA) := by rw [mul_one]; exact pA
  have TB : Real.sqrt s * |η * deriv (fun e => meanStream tr s e) η| ≤
      CB * 3 ^ MB * ν⁻¹ ^ (2 * MB) := by
    calc Real.sqrt s * |η * deriv (fun e => meanStream tr s e) η|
        ≤ Real.sqrt s * (polyP CB MB ν c * (1 + s) ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left mB hsq0
      _ = polyP CB MB ν c * (Real.sqrt s * (1 + s) ^ (-(1 / 2) : ℝ)) := by ring
      _ ≤ polyP CB MB ν c * 1 := mul_le_mul_of_nonneg_left qA P0B
      _ ≤ CB * 3 ^ MB * ν⁻¹ ^ (2 * MB) := by rw [mul_one]; exact pB
  have TC : Real.sqrt s * (2 * s * |deriv (fun r => meanStream tr r η) s|) ≤
      2 * (CC * 3 ^ MC * ν⁻¹ ^ (2 * MC)) := by
    calc Real.sqrt s * (2 * s * |deriv (fun r => meanStream tr r η) s|)
        ≤ Real.sqrt s * (2 * s * (polyP CC MC ν c * (1 + s) ^ (-(3 / 2) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hsq0
          exact mul_le_mul_of_nonneg_left mC (by linarith)
      _ = polyP CC MC ν c * (Real.sqrt s * (2 * s * (1 + s) ^ (-(3 / 2) : ℝ))) := by ring
      _ ≤ polyP CC MC ν c * 2 := mul_le_mul_of_nonneg_left qC P0C
      _ ≤ 2 * (CC * 3 ^ MC * ν⁻¹ ^ (2 * MC)) := by linarith
  have TF0 : Real.sqrt s * |F s (ξ, η)| ≤
      CF0 * 3 ^ N0 * ν⁻¹ ^ (2 * N0) * (8 * (1 + κ0⁻¹) ^ 2 * ν⁻¹ ^ 10) := by
    calc Real.sqrt s * |F s (ξ, η)|
        ≤ Real.sqrt s * (polyP CF0 N0 ν c * Real.exp (-(κ0 * ν * s / c ^ 2))) :=
          mul_le_mul_of_nonneg_left fA hsq0
      _ = polyP CF0 N0 ν c * (Real.sqrt s * Real.exp (-(κ0 * ν * s / c ^ 2))) := by ring
      _ ≤ polyP CF0 N0 ν c *
            (Real.sqrt s * (1 + 2 * s) * Real.exp (-(κ0 * ν * s / c ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ P0F0
          exact mul_le_mul_of_nonneg_right h12 hex0.le
      _ ≤ CF0 * 3 ^ N0 * ν⁻¹ ^ (2 * N0) * (8 * (1 + κ0⁻¹) ^ 2 * ν⁻¹ ^ 10) :=
          mul_le_mul pF0 xF0 (by positivity) (by positivity)
  have TF1 : Real.sqrt s * (|η| * |deriv (fun t => F s (ξ, t)) η|) ≤
      CF1 * 3 ^ N1 * ν⁻¹ ^ (2 * N1) * (8 * (1 + κ1⁻¹) ^ 2 * ν⁻¹ ^ 10) := by
    calc Real.sqrt s * (|η| * |deriv (fun t => F s (ξ, t)) η|)
        ≤ Real.sqrt s * (polyP CF1 N1 ν c * Real.exp (-(κ1 * ν * s / c ^ 2))) :=
          mul_le_mul_of_nonneg_left fB hsq0
      _ = polyP CF1 N1 ν c * (Real.sqrt s * Real.exp (-(κ1 * ν * s / c ^ 2))) := by ring
      _ ≤ polyP CF1 N1 ν c *
            (Real.sqrt s * (1 + 2 * s) * Real.exp (-(κ1 * ν * s / c ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ P0F1
          exact mul_le_mul_of_nonneg_right h12 hex1.le
      _ ≤ CF1 * 3 ^ N1 * ν⁻¹ ^ (2 * N1) * (8 * (1 + κ1⁻¹) ^ 2 * ν⁻¹ ^ 10) :=
          mul_le_mul pF1 xF1 (by positivity) (by positivity)
  have TF2 : Real.sqrt s * (2 * s * |deriv (fun r => F r (ξ, η)) s|) ≤
      CF2 * 3 ^ N2 * ν⁻¹ ^ (2 * N2) * (8 * (1 + κ2⁻¹) ^ 2 * ν⁻¹ ^ 10) := by
    calc Real.sqrt s * (2 * s * |deriv (fun r => F r (ξ, η)) s|)
        ≤ Real.sqrt s * (2 * s * (polyP CF2 N2 ν c * Real.exp (-(κ2 * ν * s / c ^ 2)))) := by
          apply mul_le_mul_of_nonneg_left _ hsq0
          exact mul_le_mul_of_nonneg_left fC (by linarith)
      _ = polyP CF2 N2 ν c * (Real.sqrt s * (2 * s) * Real.exp (-(κ2 * ν * s / c ^ 2))) := by
          ring
      _ ≤ polyP CF2 N2 ν c *
            (Real.sqrt s * (1 + 2 * s) * Real.exp (-(κ2 * ν * s / c ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ P0F2
          exact mul_le_mul_of_nonneg_right h2s hex2.le
      _ ≤ CF2 * 3 ^ N2 * ν⁻¹ ^ (2 * N2) * (8 * (1 + κ2⁻¹) ^ 2 * ν⁻¹ ^ 10) :=
          mul_le_mul pF2 xF2 (by positivity) (by positivity)
  -- raising every power to the common exponent `K`
  have gA : CA * 3 ^ MA * ν⁻¹ ^ (2 * MA) ≤ CA * 3 ^ MA * ν⁻¹ ^ K :=
    le_pow_max ha1 (by positivity) (by rw [hK]; omega)
  have gB : CB * 3 ^ MB * ν⁻¹ ^ (2 * MB) ≤ CB * 3 ^ MB * ν⁻¹ ^ K :=
    le_pow_max ha1 (by positivity) (by rw [hK]; omega)
  have gC : CC * 3 ^ MC * ν⁻¹ ^ (2 * MC) ≤ CC * 3 ^ MC * ν⁻¹ ^ K :=
    le_pow_max ha1 (by positivity) (by rw [hK]; omega)
  have gpow : ∀ i : ℕ, i ≤ 2 * (MA + MB + MC + N0 + N1 + N2) → ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y →
      X * ν⁻¹ ^ i * (Y * ν⁻¹ ^ 10) ≤ X * Y * ν⁻¹ ^ K := by
    intro i hi X Y hX hY
    have hp : ν⁻¹ ^ i * ν⁻¹ ^ 10 ≤ ν⁻¹ ^ K := by
      rw [← pow_add]
      exact pow_le_pow_right₀ ha1 (by rw [hK]; omega)
    calc X * ν⁻¹ ^ i * (Y * ν⁻¹ ^ 10) = X * Y * (ν⁻¹ ^ i * ν⁻¹ ^ 10) := by ring
      _ ≤ X * Y * ν⁻¹ ^ K := mul_le_mul_of_nonneg_left hp (mul_nonneg hX hY)
  have g0 := gpow (2 * N0) (by omega) (CF0 * 3 ^ N0) (8 * (1 + κ0⁻¹) ^ 2) (by positivity)
    (by positivity)
  have g1 := gpow (2 * N1) (by omega) (CF1 * 3 ^ N1) (8 * (1 + κ1⁻¹) ^ 2) (by positivity)
    (by positivity)
  have g2 := gpow (2 * N2) (by omega) (CF2 * 3 ^ N2) (8 * (1 + κ2⁻¹) ^ 2) (by positivity)
    (by positivity)
  calc Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s ξ η|
      ≤ Real.sqrt s * (|F s (ξ, η)| + |meanStream tr s η| +
          |η| * |deriv (fun t => F s (ξ, t)) η| + |η * deriv (fun e => meanStream tr s e) η| +
          2 * s * |deriv (fun r => F r (ξ, η)) s| +
          2 * s * |deriv (fun r => meanStream tr r η) s|) :=
        mul_le_mul_of_nonneg_left hHle hsq0
    _ = Real.sqrt s * |F s (ξ, η)| + Real.sqrt s * |meanStream tr s η| +
          Real.sqrt s * (|η| * |deriv (fun t => F s (ξ, t)) η|) +
          Real.sqrt s * |η * deriv (fun e => meanStream tr s e) η| +
          Real.sqrt s * (2 * s * |deriv (fun r => F r (ξ, η)) s|) +
          Real.sqrt s * (2 * s * |deriv (fun r => meanStream tr r η) s|) := by ring
    _ ≤ (CA * 3 ^ MA + CB * 3 ^ MB + 2 * (CC * 3 ^ MC) +
          CF0 * 3 ^ N0 * (8 * (1 + κ0⁻¹) ^ 2) + CF1 * 3 ^ N1 * (8 * (1 + κ1⁻¹) ^ 2) +
          CF2 * 3 ^ N2 * (8 * (1 + κ2⁻¹) ^ 2)) * ν⁻¹ ^ K := by
        linarith [TA, TB, TC, TF0, TF1, TF2, gA, gB, gC, g0, g1, g2]

end RaisedSupAux

/-- `ε = e^{-d/ν} ≤ 1` at a regime level (`d ≥ d₋ > 0`). -/
theorem RaisedSupAux.eps_le_one_of {L : ReturnLevel} {d dm : ℝ}
    (hε : L.ε = Real.exp (-d / L.ν)) (hdm : 0 < dm) (hd : dm ≤ d) : L.ε ≤ 1 := by
  rw [hε, Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) L.ν_pos.le

/-- **Weighted sup bound of the raised stream** (source 2076-2077, 5461-5463, 2715-2725), from
the Part I mean-stream expansion (`sct:expansion`, 447-459) and fluctuation decay
(`sct:fluctuation`, 439-446), the standing Part I hypotheses: for large `n`,
`√s · ε|H(s, ξ, η)| ≤ Cν^{-k}` at every age `s > 0` and plane point. -/
theorem raisedWeightedSup_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (D : SeqData) {dm dp : Real} (hst : D.RepairStanding dm dp) :
    RawSupOrg.RaisedWeightedSup D := by
  obtain ⟨C, k, ν₀, hν₀, H⟩ := RaisedSupAux.raised_core hM hF
  have hνt : Tendsto (fun n => retNu D.Pl D.σ₀ n) atTop (𝓝 0) :=
    retNu_tendsto D.σ₀ hst.omega_ne
  have hev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₀ 1 :=
    hνt.eventually (ge_mem_nhds (lt_min hν₀ one_pos))
  refine ⟨C, k, ?_⟩
  filter_upwards [hev, hst.actual] with n hn hact s ξ η hs
  have hν : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
  have hνa : retNu D.Pl D.σ₀ n ≤ ν₀ := hn.trans (min_le_left _ _)
  have hν1 : retNu D.Pl D.σ₀ n ≤ 1 := hn.trans (min_le_right _ _)
  have hcEq : cOf (retNu D.Pl D.σ₀ n) = UnforcedLeray.Short.PartI.trainPeriod 2 (retNu D.Pl D.σ₀ n) := by
    unfold cOf UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  have hε1 : (D.level n).ε ≤ 1 :=
    RaisedSupAux.eps_le_one_of (d := _) hact.regime.eps_eq hact.regime.dm_pos hact.regime.dm_le
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have h := H (retNu D.Pl D.σ₀ n) hν hνa hν1 (cOf (retNu D.Pl D.σ₀ n)) hcEq (D.train n)
    (D.train_buc n) (D.train_stream_smooth n) s ξ η hs
  have hX : 0 ≤ Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  calc Real.sqrt s * ((D.level n).ε * |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η|)
      = (D.level n).ε * (Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η|) := by
        ring
    _ ≤ 1 * (Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η|) :=
        mul_le_mul_of_nonneg_right hε1 hX
    _ = Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η| := one_mul _
    _ ≤ C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k := h
    _ = C * (D.level n).ν⁻¹ ^ k := rfl

end UnforcedLeray.Short.PartIIIb.Concrete
