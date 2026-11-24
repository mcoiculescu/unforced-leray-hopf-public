import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Tasks.OverlapRescaling

/-!
# Part I: overlap and transverse-tail design (`ORG:PartI/overlap-and-tails-design`)

Source of record: `the November 2 reference manuscript` (SP), lines 304-325,
379-436 (proof of Lemma `sct:train`), and 438-551 (Lemma `sct:heat` and proof).

This module provides:
1. Exact `Prop` definitions for the intermediate steps of the overlap and heat-tail chain:
   * `OverlapHighNormUniform` (`PartI:T12`, SP lines 379-389, 429-435 / old 350-358):
     uniform `H^N` (`cellL2 1` and `supNormD`) bounds on the overlap-rescaled velocity
     `U(T) = overlapField ν c tr.v T` on the unit cylinder for all `T ≥ 0`.
   * `OverlapFluctuationDecay` (`PartI:T13`, SP lines 304-313, 389-396 / old 354-362):
     exponential decay in `T ≥ 0` of all spatial jets of `W(T) = hfluct 1 (U T)` in `cellL2 1`
     and `supNormD` (the last two clauses of `TrainOverlap`).
   * `OverlapMeanPrimitive` (`PartI:T14`, SP lines 398-420):
     smoothness, forced 1D heat equation `∂_T 𝖲 - ∂_Y² 𝖲 = e_c \overline{W₁ W₂}`, relation
     `b = -∂_Y 𝖲`, `\bar U₂ = 0`, and initial `L¹_Y` bound `‖𝖲(0)‖_{L¹_Y} ≤ C` for the
     overlap-rescaled mean stream `𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)`.
   * `OverlapMeanDecay` (`PartI:T15`, SP lines 304-313, 415-425 / old 425-436):
     smoothness and `L²_Y` / `L^∞_Y` algebraic decay `(1 + T)^{-1 - j/2 + 1/(2p)}` of
     `∂_Y^j b(T)` for all `T ≥ 0` (the mean-flow clauses of `TrainOverlap`).
   * `TrainVorticityGaussianTail` (`PartI:T20`, SP lines 483-497, 523-526 / old 484-492):
     pointwise Gaussian transverse tail for the vorticity `ω = curl v` and its mixed
     age/spatial jets `∂_s^ℓ D^j ω` at all ages `s > 0`.
   * `TrainStreamVelocityPressureTails` (`PartI:T21`, SP lines 499-526 / old 493-515):
     evenness of the mean stream `S`, transverse tails for `(ψ, v, p)` on `0 < s ≤ S_*`,
     and polynomial-in-`(c, ν⁻¹, 1 + s)` weighted `L²` and `L^∞` bounds (`wCellL2`, `wSupNorm`)
     for the mixed age/spatial jets of `(ψ̃, ṽ, v, ω, p)` at every age `s > 0`.
2. Conditional assembly `trainOverlap_of : TrainMeanEquations → OverlapFluctuationDecay →
   OverlapMeanDecay → TrainOverlap` (`PartI:T16`, per R9), plus `trainTransverseTails_of`
   assembling `TrainTransverseTails` (`PartI:T24`) from `TrainVorticityGaussianTail` and
   `TrainStreamVelocityPressureTails`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)

/-! ### 1. Intermediate `Prop` definitions for `PartI:T12..T21` -/

/-- **Uniform high-order overlap norm (`PartI:T12`)** (source lines 379-389, 429-435; old 350-358):
for every `ρ > 1/2` and derivative budget `N : ℕ`, there exist `C > 0` and `ν₀ > 0` such that
for all `0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, every overlap
time `T ≥ 0`, and every `j ≤ N`, the overlap-rescaled velocity `U(T) = overlapField ν c tr.v T`
on the unit cylinder satisfies `cellL2 1 (jet j U) ≤ ofReal C` and `supNormD j U ≤ ofReal C`. -/
def OverlapHighNormUniform : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ N : ℕ, ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ T : ℝ, 0 ≤ T → ∀ j : ℕ, j ≤ N →
          let U := overlapField ν (trainPeriod ρ ν) tr.v T
          cellL2 1 (jet j U) ≤ ENNReal.ofReal C ∧
          B0277.supNormD j U ≤ ENNReal.ofReal C

/-- **Exponential decay of the overlap fluctuation (`PartI:T13`)** (source lines 304-313, 389-396;
old 354-362): the last two clauses of `TrainOverlap` (`sct:overlap`). For every `ρ > 1/2` and
spatial derivative order `j : ℕ`, there exist `C > 0`, `lam > 0`, and `ν₀ > 0` such that for all
`0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, and every `T ≥ 0`, the
horizontal fluctuation `W(T) = hfluct 1 (overlapField ν c tr.v T)` on the unit cylinder satisfies
`cellL2 1 (jet j (W T)) ≤ ofReal (C e^{-lam T})` and
`supNormD j (W T) ≤ ofReal (C e^{-lam T})`. -/
def OverlapFluctuationDecay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ T : ℝ, 0 ≤ T →
          let U := overlapField ν (trainPeriod ρ ν) tr.v T
          cellL2 1 (jet j (hfluct 1 U)) ≤ ENNReal.ofReal (C * Real.exp (-(lam * T))) ∧
          B0277.supNormD j (hfluct 1 U) ≤ ENNReal.ofReal (C * Real.exp (-(lam * T)))

/-- **The overlap-rescaled mean stream primitive (`PartI:T14`)** (source lines 398-420):
for every `ρ > 1/2`, there exist `C > 0` and `ν₀ > 0` such that for all `0 < ν ≤ ν₀` and every
`BUC` train `tr` at period `c = trainPeriod ρ ν`, the rescaled mean primitive
`𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)` (`S = meanStream tr`) is `C^∞` on `[0, ∞) × ℝ`, solves
`∂_T 𝖲 - ∂_Y² 𝖲 = e_c \overline{W₁ W₂}` with `b = -∂_Y 𝖲` and `\bar U₂ = 0` for all `T ≥ 0`,
and satisfies the initial `L¹_Y` bound `‖𝖲(0)‖_{L¹_Y} ≤ C`. -/
def OverlapMeanPrimitive : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        let U := overlapField ν c tr.v
        let W := fun T => hfluct 1 (U T)
        let b := fun T Y => (hmean 1 (U T) Y) 0
        let S_ov : ℝ → ℝ → ℝ := fun T Y =>
          c ^ 2 * meanStream tr (B0146.overlapAge ν c + c ^ 2 * T / ν) (c * Y)
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => S_ov x.1 x.2) (Ici 0 ×ˢ univ) ∧
        (∀ T : ℝ, 0 ≤ T → ∀ Y : ℝ,
          deriv (fun T' => S_ov T' Y) T -
              deriv (deriv (fun Y' => S_ov T Y')) Y =
            eC ν c * hmean 1 (fun y : Plane => W T y 0 * W T y 1) Y ∧
          b T Y = -deriv (fun Y' => S_ov T Y') Y ∧
          (hmean 1 (U T) Y) 1 = 0) ∧
        eLpNorm (S_ov 0) 1 volume ≤ ENNReal.ofReal C

/-- **Algebraic decay of the overlap horizontal mean (`PartI:T15`)** (source lines 304-313,
415-425; old 425-436): the mean-flow clauses of `TrainOverlap` (`sct:overlap`). For every
`ρ > 1/2` and derivative order `j : ℕ`, there exist `C > 0` and `ν₀ > 0` such that for all
`0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, and every `T ≥ 0`, the
horizontal mean profile `b(Y) = hmean 1 (overlapField ν c tr.v T) Y 0` is smooth
(`ContDiff ℝ ∞ b`) and satisfies `‖∂_Y^j b‖₂ ≤ C (1 + T)^{-1 - j/2 + 1/4}` and
`‖∂_Y^j b‖_∞ ≤ C (1 + T)^{-1 - j/2}`. -/
def OverlapMeanDecay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ T : ℝ, 0 ≤ T →
          let U := overlapField ν (trainPeriod ρ ν) tr.v T
          let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
          ContDiff ℝ ∞ b ∧
          eLpNorm (iteratedDeriv j b) 2 volume ≤
              ENNReal.ofReal (C * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) ∧
          eLpNorm (iteratedDeriv j b) ⊤ volume ≤
              ENNReal.ofReal (C * (1 + T) ^ (-1 - (j : ℝ) / 2))

/-- **Gaussian transverse tail of the train vorticity (`PartI:T20`)** (source lines 483-497,
523-526; old 484-492): for every `ρ > 1/2` and mixed age/spatial derivative orders `ℓ, j : ℕ`,
there exist `b > 0`, `C₀ > 0`, `C' > 0`, `C > 0`, `N : ℕ`, and `ν₀ > 0` such that for all
`0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, every age `s > 0`, and
every `z : Plane`,
`‖∂_s^ℓ D^j ω(s, z)‖ ≤ polyP C N ν c * exp(-b (max (|z.2| - C'/ν) 0)² / (C₀ + ν s))`. -/
def TrainVorticityGaussianTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            let c := trainPeriod ρ ν
            let d := max (|z.2| - C' / ν) 0
            ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
              polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))

/-- **Transverse tails and polynomial weighted bounds for stream, velocity, and pressure
(`PartI:T21`)** (source lines 499-526; old 493-515):
1. Evenness of the mean stream `S(s, -η) = S(s, η)` for all `s ≥ 0`;
2. Transverse tails on `0 < s ≤ S_*` for `|z.2| ≥ C'/ν + 2 + l` (`l ≥ 0`) for the mixed
   age/spatial jets `∂_s^ℓ D^j` of `(ψ, v, p)` with constants `b, C₀, C', C, N, ν₀` uniform in `S_*`;
3. Polynomial-in-`(c, ν⁻¹, 1 + s)` weighted `L²` (`wCellL2 c m`) and `L^∞` (`wSupNorm m`) bounds
   at every age `s > 0` for the mixed age/spatial jets `∂_s^ℓ D^j` of `(ψ̃, ṽ, v, ω, p)`. -/
def TrainStreamVelocityPressureTails : Prop :=
  (∀ ρ : ℝ, 1 / 2 < ρ → ∀ ν : ℝ, 0 < ν →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 ≤ s → ∀ η : ℝ, meanStream tr s (-η) = meanStream tr s η) ∧
  (∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K : ℝ := polyPS C N ν c S_ *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
          ‖ageJet ℓ j tr.ψ s z‖ ≤ K ∧ ‖ageJet ℓ j tr.v s z‖ ≤ K ∧ ‖ageJet ℓ j tr.p s z‖ ≤ K) ∧
  (∀ ρ : ℝ, 1 / 2 < ρ → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
        let c := trainPeriod ρ ν
        let K : ℝ≥0∞ := ENNReal.ofReal (polyPS C N ν c s)
        (wCellL2 c m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j tr.v s) ≤ K ∧ wSupNorm m (ageJet ℓ j tr.v s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j tr.p s) ≤ K ∧ wSupNorm m (ageJet ℓ j tr.p s) ≤ K))

/-! ### 2. Private helpers and conditional assembly `trainOverlap_of` (`PartI:T16`) -/

namespace OverlapAndTailsDesign

private theorem hmean_scale_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) (F : Plane → E) (Y : ℝ) :
    hmean 1 (fun y : Plane => F (c • y)) Y = hmean c F (c * Y) := by
  unfold hmean
  have hle1 : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hlec : -c / 2 ≤ c / 2 := by linarith
  rw [inv_one, one_smul, ← intervalIntegral.integral_of_le hle1,
    ← intervalIntegral.integral_of_le hlec]
  have hcomp := intervalIntegral.integral_comp_mul_left (fun q : ℝ => F (q, c * Y)) hc.ne'
    (a := -1 / 2) (b := 1 / 2)
  have ha : c * (-1 / 2) = -c / 2 := by ring
  have hb : c * (1 / 2) = c / 2 := by ring
  rw [ha, hb] at hcomp
  simpa [Prod.smul_mk, smul_eq_mul] using hcomp

private theorem hmean_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c a : ℝ) (F : Plane → E) (Y : ℝ) :
    hmean c (fun y : Plane => a • F y) Y = a • hmean c F Y := by
  unfold hmean
  rw [integral_smul, smul_comm]

private theorem hmean_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (j : Fin 2) :
    (hmean c a η) j = hmean c (fun z => a z j) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

private theorem continuous_overlapField_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {T : ℝ}
    (hs : 0 ≤ B0146.overlapAge ν c + c ^ 2 * T / ν) :
    Continuous (overlapField ν c tr.v T) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hmap : Continuous (fun y : Plane => ((s, c • y) : ℝ × Plane)) :=
    continuous_const.prodMk (continuous_id.const_smul c)
  have hv : Continuous (fun y : Plane => tr.v s (c • y)) :=
    hcont.comp_continuous hmap (fun y => ⟨hs, mem_univ _⟩)
  exact hv.const_smul (c ^ 3)

private theorem overlapField_hmean_snd_eq_zero (hMean : TrainMeanEquations)
    {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (Y : ℝ) :
    (hmean 1 (overlapField ν c tr.v T) Y) 1 = 0 := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hs0 : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hs : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν := by
    have hT0 : 0 ≤ c ^ 2 * T / ν := div_nonneg (mul_nonneg (sq_nonneg c) hT) hν.le
    linarith
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hv2 := ((hMean ν c hν hc0 tr htr).2 s hs (c * Y)).2.2
  have h1 : hmean 1 (fun y : Plane => overlapField ν c tr.v T y 1) Y = 0 := by
    have hfun : (fun y : Plane => overlapField ν c tr.v T y 1) =
        fun y : Plane => c ^ 3 • (fun z : Plane => tr.v s z 1) (c • y) := by
      funext y
      simp [overlapField, s, smul_eq_mul]
    rw [hfun, hmean_const_smul, hmean_scale_unit hc0 (fun z : Plane => tr.v s z 1) Y, hv2,
      smul_zero]
  rw [hmean_apply_vec (continuous_overlapField_slice tr hs.le) Y 1, h1]

end OverlapAndTailsDesign

/-- **Conditional assembly of `TrainOverlap` (`PartI:T16`)** (source lines 304-313, 389-425):
combines `\bar U₂ = 0` from `TrainMeanEquations` (`PartI:T01`), the fluctuation bounds from
`OverlapFluctuationDecay` (`PartI:T13`), and the mean-flow bounds from `OverlapMeanDecay`
(`PartI:T15`). -/
theorem trainOverlap_of (hMean : TrainMeanEquations)
    (hFluct : OverlapFluctuationDecay) (hMeanDec : OverlapMeanDecay) :
    TrainOverlap := by
  intro ρ hρ j
  obtain ⟨CF, lam, νF, hCF, hlam, hνF, hF⟩ := hFluct ρ hρ j
  obtain ⟨CM, νM, hCM, hνM, hM⟩ := hMeanDec ρ hρ j
  refine ⟨max CF CM, lam, min (min νF νM) (1 / 2), lt_max_of_lt_left hCF, hlam,
    lt_min (lt_min hνF hνM) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr T hT
  have hν_F : ν ≤ νF := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_M : ν ≤ νM := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hc1 : 1 < trainPeriod ρ ν := by
    unfold trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  obtain ⟨hFl2, hFsup⟩ := hF ν hν hν_F tr htr T hT
  obtain ⟨hb_smooth, hMl2, hMsup⟩ := hM ν hν hν_M tr htr T hT
  have h1T : 0 ≤ 1 + T := by linarith
  have hCF_le : CF ≤ max CF CM := le_max_left _ _
  have hCM_le : CM ≤ max CF CM := le_max_right _ _
  refine ⟨fun Y => OverlapAndTailsDesign.overlapField_hmean_snd_eq_zero hMean hν hc1 tr htr hT Y,
    hb_smooth, ?_, ?_, ?_, ?_⟩
  · exact hMl2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCM_le (Real.rpow_nonneg h1T _)))
  · exact hMsup.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCM_le (Real.rpow_nonneg h1T _)))
  · exact hFl2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCF_le (Real.exp_nonneg _)))
  · exact hFsup.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCF_le (Real.exp_nonneg _)))

/-- **Conditional assembly of `TrainTransverseTails` (`PartI:T24`)** (source lines 460-467,
484-515): combines the Gaussian vorticity tail (`TrainVorticityGaussianTail`, `PartI:T20`) and
the stream/velocity/pressure transverse tails (`TrainStreamVelocityPressureTails`, `PartI:T21`). -/
theorem trainTransverseTails_of (hVort : TrainVorticityGaussianTail)
    (hTails : TrainStreamVelocityPressureTails) :
    TrainTransverseTails := by
  intro ρ hρ ℓ j
  obtain ⟨b₁, C₀₁, C'₁, hb₁, hC₀₁, hC'₁, C₁, N₁, ν₁, hC₁, hν₁, hV⟩ := hVort ρ hρ ℓ j
  obtain ⟨b₂, C₀₂, C'₂, hb₂, hC₀₂, hC'₂, C₂, N₂, ν₂, hC₂, hν₂, hT⟩ := hTails.2.1 ρ hρ ℓ j
  clear hVort hTails
  refine ⟨min b₁ b₂, max C₀₁ C₀₂, max C'₁ C'₂, lt_min hb₁ hb₂, lt_max_of_lt_left hC₀₁,
    lt_max_of_lt_left hC'₁, max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁,
    lt_min hν₁ hν₂, ?_⟩
  intro S_ hS_ ν hν hν_le tr htr l hl s hs hsS z hz
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have hc0 : 0 ≤ trainPeriod ρ ν := by
    unfold trainPeriod
    exact Real.rpow_nonneg hν.le _
  let c := trainPeriod ρ ν
  have hbase : 1 ≤ (1 + c + ν⁻¹) * (1 + S_) := by
    have h1 : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
      linarith
    have h2 : 1 ≤ 1 + S_ := by linarith
    nlinarith
  have hpoly₁ : polyP C₁ N₁ ν c ≤ polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ := by
    unfold polyP polyPS
    have h1 : 1 + c + ν⁻¹ ≤ (1 + c + ν⁻¹) * (1 + S_) := by
      have : 0 ≤ 1 + c + ν⁻¹ := by
        have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
        linarith
      nlinarith
    have hpow1 : (1 + c + ν⁻¹) ^ N₁ ≤ ((1 + c + ν⁻¹) * (1 + S_)) ^ N₁ :=
      pow_le_pow_left₀ (by positivity) h1 N₁
    have hpow2 : ((1 + c + ν⁻¹) * (1 + S_)) ^ N₁ ≤
        ((1 + c + ν⁻¹) * (1 + S_)) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hbase (le_max_left _ _)
    exact mul_le_mul (le_max_left _ _) (hpow1.trans hpow2) (by positivity)
      (le_trans hC₁.le (le_max_left _ _))
  have hpoly₂ : polyPS C₂ N₂ ν c S_ ≤ polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ := by
    unfold polyPS
    have hpow : ((1 + c + ν⁻¹) * (1 + S_)) ^ N₂ ≤
        ((1 + c + ν⁻¹) * (1 + S_)) ^ max N₁ N₂ :=
      pow_le_pow_right₀ hbase (le_max_right _ _)
    exact mul_le_mul (le_max_right _ _) hpow (by positivity)
      (le_trans hC₁.le (le_max_left _ _))
  have hz₂ : C'₂ / ν + 2 + l ≤ |z.2| := by
    have hC' : C'₂ / ν ≤ max C'₁ C'₂ / ν :=
      div_le_div_of_nonneg_right (le_max_right _ _) hν.le
    linarith
  obtain ⟨hψ, hv, hp⟩ := hT S_ hS_ ν hν hν₂_le tr htr l hl s hs hsS z hz₂
  have hω₀ := hV ν hν hν₁_le tr htr s hs z
  clear hV hT
  have hb_min1 : min b₁ b₂ ≤ b₁ := min_le_left _ _
  have hb_min2 : min b₁ b₂ ≤ b₂ := min_le_right _ _
  have hC₀_max1 : C₀₁ ≤ max C₀₁ C₀₂ := le_max_left _ _
  have hC₀_max2 : C₀₂ ≤ max C₀₁ C₀₂ := le_max_right _ _
  have hC₀s_pos : 0 < C₀₁ + ν * s := by nlinarith
  have hC₀S_pos2 : 0 < C₀₂ + ν * S_ := by nlinarith
  have hC₀S_pos : 0 < max C₀₁ C₀₂ + ν * S_ := by
    have : 0 < max C₀₁ C₀₂ := lt_max_of_lt_left hC₀₁
    nlinarith
  have hc_pos : 0 < c := by
    unfold c trainPeriod
    exact Real.rpow_pos_of_pos hν _
  have hexp_l : Real.exp (-(b₂ * l / c)) ≤ Real.exp (-(min b₁ b₂ * l / c)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb_min2 hl) hc_pos.le
  have hexp_g2 : Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_))) ≤
      Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have hnum : min b₁ b₂ * l ^ 2 ≤ b₂ * l ^ 2 :=
      mul_le_mul_of_nonneg_right hb_min2 (sq_nonneg l)
    have hden : C₀₂ + ν * S_ ≤ max C₀₁ C₀₂ + ν * S_ := add_le_add hC₀_max2 le_rfl
    exact div_le_div₀ (by positivity) hnum hC₀S_pos2 hden
  have hK_le : polyPS C₂ N₂ ν c S_ *
        (Real.exp (-(b₂ * l / c)) + Real.exp (-(b₂ * l ^ 2 / (C₀₂ + ν * S_)))) ≤
      polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ *
        (Real.exp (-(min b₁ b₂ * l / c)) +
          Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_)))) := by
    apply mul_le_mul hpoly₂ (add_le_add hexp_l hexp_g2) (by positivity)
    unfold polyPS
    have : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
    positivity
  have hω : ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
      polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ *
        (Real.exp (-(min b₁ b₂ * l / c)) +
          Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_)))) := by
    have hd_ge : l ≤ max (|z.2| - C'₁ / ν) 0 := by
      have hC' : C'₁ / ν ≤ max C'₁ C'₂ / ν :=
        div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      exact le_max_of_le_left (by linarith)
    have hd_sq : l ^ 2 ≤ (max (|z.2| - C'₁ / ν) 0) ^ 2 :=
      pow_le_pow_left₀ hl hd_ge 2
    have hexp_ω : Real.exp (-(b₁ * (max (|z.2| - C'₁ / ν) 0) ^ 2 / (C₀₁ + ν * s))) ≤
        Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hnum : min b₁ b₂ * l ^ 2 ≤ b₁ * (max (|z.2| - C'₁ / ν) 0) ^ 2 :=
        mul_le_mul hb_min1 hd_sq (sq_nonneg l) hb₁.le
      have hden : C₀₁ + ν * s ≤ max C₀₁ C₀₂ + ν * S_ :=
        add_le_add hC₀_max1 (mul_le_mul_of_nonneg_left hsS hν.le)
      exact div_le_div₀ (by positivity) hnum hC₀s_pos hden
    have hpoly_pos : 0 ≤ polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ := by
      unfold polyPS
      have : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
      positivity
    calc ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖
        ≤ polyP C₁ N₁ ν c *
            Real.exp (-(b₁ * (max (|z.2| - C'₁ / ν) 0) ^ 2 / (C₀₁ + ν * s))) := hω₀
      _ ≤ polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ *
            Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_))) :=
          mul_le_mul hpoly₁ hexp_ω (Real.exp_nonneg _) hpoly_pos
      _ ≤ polyPS (max C₁ C₂) (max N₁ N₂) ν c S_ *
            (Real.exp (-(min b₁ b₂ * l / c)) +
              Real.exp (-(min b₁ b₂ * l ^ 2 / (max C₀₁ C₀₂ + ν * S_)))) := by
          apply mul_le_mul_of_nonneg_left _ hpoly_pos
          exact le_add_of_nonneg_left (Real.exp_nonneg _)
  exact ⟨hψ.trans hK_le, hv.trans hK_le, hω, hp.trans hK_le⟩

end UnforcedLeray.Short.PartI
