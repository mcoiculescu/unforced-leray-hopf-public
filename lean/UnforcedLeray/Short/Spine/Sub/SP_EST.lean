import UnforcedLeray.Short.Spine.PartI
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Units.B0277

/-!
# Spine: the train estimates of Part I as one bundle (task `Spine:SP-EST`)

Source of record: `the November 2 reference manuscript`, Lemma `sct:train`
(lines 290-437) and Lemma `sct:heat` (lines 438-554), together with the uniform derivative bound
`short-bg:train-uniform` (line 2053).

`Spine:SP-EST` is a coordination task: the train estimates are not proved in the Spine. Each of
the ten statements of the Part I area (`Short/PartI/StatementsTrain.lean`) has its own task of the
Part I train area, and the eleventh (`Spine.TrainUniform`) follows from two of them:

| statement | source lines | task |
| --- | --- | --- |
| `PartI.TrainMeanEquations` | 397-404 | `PartI:T01` |
| `PartI.TrainComparison` | 291-303 | `PartI:T10` |
| `PartI.TrainOverlap` | 304-313 | `PartI:T16` |
| `PartI.TrainL2Decay` | 314-317 | `PartI:T17` |
| `PartI.TrainStrainIntegral` | 318-319 | `PartI:T18` |
| `PartI.TrainFluctuationIntegral` | 320-322 | `PartI:T19` |
| `PartI.TrainFluctuationDecay` | 439-446 | `PartI:T22` |
| `PartI.TrainMeanExpansion` | 447-459 | `PartI:T23` |
| `PartI.TrainTransverseTails` | 460-467 | `PartI:T24` |
| `PartI.TrainFixedBand` | 468-478 | `PartI:T25` |
| `Spine.TrainUniform` | 2038-2053 | `Spine:SP-EST/1`, `/2`, `/3` below (from `T10`, `T16`) |

`Spine.TrainUniform` (`sup_s ∑_{j ≤ 3} ‖D^j v_c(s)‖_∞ ≤ C`, source line 2053) is reduced here, via the
library's `B0277.supNormD_le_orderConst` (`mixed-background:C.8`), to the three train-derivative
inputs `VcRegularity` (`SP-EST/1`, `eq:st18-t00145`, source lines 2205-2234), `TrainPreError`
(`SP-EST/2`, from `PartI:T10` and the sup-form of `eq:st18-t00148`, source lines 291-303) and
`TrainPostBound` (`SP-EST/3`, from `PartI:T16`, source lines 304-313).

`trainEstimates_of` is the conditional bundle theorem: thirteen hypotheses (the ten Part I statements
and `VcRegularity`, `TrainPreError`, `TrainPostBound`), one conclusion `TrainEstimatesAll`. The unconditional `trainEstimates : TrainEstimatesAll` is the task
`Spine:SP-EST` (`Short/Spine/Proofs/TrainEstimates.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

/-- The ten train statements of the Part I area (lemmas `sct:train` and `sct:heat`, source lines
290-554), as one conjunction. -/
def PartITrainEstimates : Prop :=
  PartI.TrainComparison ∧ PartI.TrainOverlap ∧ PartI.TrainL2Decay ∧ PartI.TrainStrainIntegral ∧
    PartI.TrainFluctuationIntegral ∧ PartI.TrainMeanEquations ∧ PartI.TrainFluctuationDecay ∧
    PartI.TrainMeanExpansion ∧ PartI.TrainTransverseTails ∧ PartI.TrainFixedBand

/-- **`SP-EST/1`** (`eq:st18-t00145`, source lines 2205-2234, `B0151`, `Lib/Train/VortexBounds.lean`
`Vc_bounds` with `m = 0`): the periodized heat vortex `V_c(s)` is `C³` for `s ≥ 0`, and for every
order `j` there is a constant `C_g` (independent of `ν, c, s`) with
`‖D^j V_c(s)‖_∞ ≤ C_g a^{-(3+j)/2}` whenever `1 ≤ a = 1 + ν s ≤ c²` (`a = heatWidth ν s`). -/
def VcRegularity : Prop :=
  (∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → ContDiff ℝ 3 (Train.Vc ν c s)) ∧
  ∀ j : ℕ, ∃ Cg : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ B0113.heatWidth ν s →
    B0113.heatWidth ν s ≤ c ^ 2 → ∀ z,
      ‖iteratedFDeriv ℝ j (Train.Vc ν c s) z‖ ≤
        Cg * B0113.heatWidth ν s ^ (-((3 + j : ℝ) / 2))

/-- **`SP-EST/2`** (`sct:comparison`, source lines 291-303, `eq:st18-t00148`; from `PartI:T10` at
`ρ = 2`, `c = Train.per ν = ν^{-2}`): the pre-overlap error `v - V_c` satisfies, for `ν` small,
`0 ≤ s ≤ s_c` and `j ≤ 3`, the sup bound
`‖D^j (v - V_c)(s)‖_∞ ≤ Ce_j ν⁻¹ a^{-(5+j)/2} e^{-be_j c²/a}`, with constants `Ce_j, be_j > 0`
independent of `ν, s` and of the train. -/
def TrainPreError : Prop :=
  ∃ (Ce be : ℕ → ℝ) (ν₀ : ℝ), 0 < ν₀ ∧ (∀ j, 0 < be j) ∧
    ∀ ν ∈ Set.Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (Train.per ν), PartI.IsBUCTrain T → ∀ s : ℝ, 0 ≤ s →
      s ≤ B0146.overlapAge ν (Train.per ν) → ∀ j : ℕ, j ≤ 3 → ∀ x,
        ‖iteratedFDeriv ℝ j (T.v s - Train.Vc ν (Train.per ν) s) x‖ ≤
          Ce j * ν⁻¹ * B0113.heatWidth ν s ^ (-((5 + j : ℝ) / 2)) *
            Real.exp (-be j * (Train.per ν) ^ 2 / B0113.heatWidth ν s)

/-- **`SP-EST/3`** (`sct:overlap`, source lines 304-313; from `PartI:T16` at `ρ = 2`): the
overlap-rescaled field `U(T) = c³ v(s_c + c² T/ν, c ·)` has `‖D^j U(T)‖_∞ ≤ Cu_j` for all
`T ≥ 0`, `j ≤ 3`, `ν` small, with `Cu_j` independent of `ν, T` and of the train
(`U = b e₁ + W`, `‖∂_Y^j b‖_∞ ≤ C (1+T)^{-1-j/2}`, `‖D^j W‖_∞ ≤ C e^{-λ T}`). -/
def TrainPostBound : Prop :=
  ∃ (Cu : ℕ → ℝ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν ∈ Set.Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (Train.per ν), PartI.IsBUCTrain T → ∀ t : ℝ, 0 ≤ t →
      ∀ j : ℕ, j ≤ 3 → ∀ y,
        ‖iteratedFDeriv ℝ j (PartI.overlapField ν (Train.per ν) T.v t) y‖ ≤ Cu j

/-- The input of `B0277.supNormD_le_orderConst` for the actual train at `c = Train.per ν`: the
bundle `TrainDerivativeEstimates` (pre-overlap Gaussian and error bounds, post-overlap rescaled
field) with constants independent of `ν` and of the train. -/
def TrainDerivativeEstimatesFamily : Prop :=
  ∃ (Cg Ce be Cu : ℕ → ℝ) (ν₀ : ℝ), 0 < ν₀ ∧ (∀ j, 0 < be j) ∧
    ∀ ν ∈ Set.Ioc 0 ν₀, ∀ T : B0140.TrainSol ν (Train.per ν), PartI.IsBUCTrain T →
      B0277.TrainDerivativeEstimates ν (Train.per ν) T.v (Train.Vc ν (Train.per ν))
        (PartI.overlapField ν (Train.per ν) T.v) Cg Ce be Cu

/-- The derivative bundle from its three analytic inputs; smoothness of `v`, the identity
`v(s, x) = c⁻³ U(T, x/c)` and the common `ν₀` are proved here. -/
theorem trainDerivativeEstimatesFamily_of (hVc : VcRegularity) (hPre : TrainPreError)
    (hPost : TrainPostBound) : TrainDerivativeEstimatesFamily := by
  obtain ⟨hVcS, hVcB⟩ := hVc
  choose Cg hCg using hVcB
  obtain ⟨Ce, be, ν₁, hν₁, hbe, hpre⟩ := hPre
  obtain ⟨Cu, ν₂, hν₂, hpost⟩ := hPost
  refine ⟨Cg, Ce, be, Cu, min (min ν₁ ν₂) 1, lt_min (lt_min hν₁ hν₂) one_pos, hbe, ?_⟩
  intro ν hν T hT
  have hν0 : 0 < ν := hν.1
  have h1 : ν ≤ ν₁ := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ν ≤ ν₂ := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hc0 : 0 < Train.per ν := Train.per_pos hν0
  have hc1 : 1 ≤ Train.per ν := Train.one_le_per hν0 hν1
  have hvS : ∀ s : ℝ, 0 ≤ s → ContDiff ℝ 3 (T.v s) := by
    intro s hs
    have h := T.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := Set.univ) (fun z _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ z⟩)
    exact (contDiffOn_univ.1 h).of_le (WithTop.coe_le_coe.2 le_top)
  have hage : 0 ≤ B0146.overlapAge ν (Train.per ν) := by
    unfold B0146.overlapAge
    have : 1 ≤ Train.per ν ^ 2 := by nlinarith
    exact div_nonneg (by linarith) hν0.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs _
    exact ⟨hvS s hs, hVcS ν _ s hν0 hc0 hs⟩
  · intro s hs hsc j _ x
    have ha1 : 1 ≤ B0113.heatWidth ν s := by
      unfold B0113.heatWidth
      nlinarith
    have hw : B0113.heatWidth ν s ≤ Train.per ν ^ 2 := by
      unfold B0146.overlapAge at hsc
      rw [le_div_iff₀ hν0] at hsc
      unfold B0113.heatWidth
      nlinarith
    exact hCg j ν _ s hc0 ha1 hw x
  · intro s hs hsc j hj x
    exact hpre ν ⟨hν0, h1⟩ T hT s hs hsc j hj x
  · intro s hs x
    have hc0' : Train.per ν ≠ 0 := hc0.ne'
    have hν0' : ν ≠ 0 := hν0.ne'
    have e1 : B0146.overlapAge ν (Train.per ν) +
        Train.per ν ^ 2 * (ν * (s - B0146.overlapAge ν (Train.per ν)) / Train.per ν ^ 2) / ν
          = s := by
      field_simp
      ring
    have e2 : Train.per ν • (Train.per ν)⁻¹ • x = x := by
      rw [smul_smul, mul_inv_cancel₀ hc0', one_smul]
    simp only [PartI.overlapField, e1, e2, smul_smul, inv_mul_cancel₀ (pow_ne_zero 3 hc0'),
      one_smul]
  · intro t ht
    have hnn : 0 ≤ B0146.overlapAge ν (Train.per ν) + Train.per ν ^ 2 * t / ν :=
      add_nonneg hage (div_nonneg (by positivity) hν0.le)
    show ContDiff ℝ 3 (fun y => Train.per ν ^ 3 •
      T.v (B0146.overlapAge ν (Train.per ν) + Train.per ν ^ 2 * t / ν) (Train.per ν • y))
    have hV : ContDiff ℝ 3 (fun y => T.v (B0146.overlapAge ν (Train.per ν) +
        Train.per ν ^ 2 * t / ν) (Train.per ν • y)) :=
      (hvS _ hnn).comp (contDiff_id.const_smul (Train.per ν))
    exact hV.const_smul (Train.per ν ^ 3)
  · intro t ht j hj y
    exact hpost ν ⟨hν0, h2⟩ T hT t ht j hj y

/-- **`TrainUniform` from the derivative bundle** (`mixed-background:C.8`, source line 2053),
through the library's `B0277.supNormD_le_orderConst`. -/
theorem trainUniform_of_estimates (h : TrainDerivativeEstimatesFamily) : TrainUniform := by
  obtain ⟨Cg, Ce, be, Cu, ν₀, hν₀, hbe, hT⟩ := h
  refine ⟨∑ j ∈ Finset.range 4, B0277.orderConst Cg Ce be Cu j, min ν₀ 1,
    lt_min hν₀ one_pos, ?_⟩
  intro ν hν T hTb s hs j hj z
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have h1 : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hsup := B0277.supNormD_le_orderConst (ρ := 2) hν0 hν1 (by norm_num)
    (Train.per_eq_rpow hν0) hbe (hT ν ⟨hν0, h1⟩ T hTb) hs hj
  have hz : ‖iteratedFDeriv ℝ j (T.v s) z‖ₑ ≤ B0277.supNormD j (T.v s) :=
    le_iSup (fun x => ‖iteratedFDeriv ℝ j (T.v s) x‖ₑ) z
  have hz' : ‖iteratedFDeriv ℝ j (T.v s) z‖ ≤ B0277.orderConst Cg Ce be Cu j := by
    have := hz.trans hsup
    rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (B0277.orderConst_nonneg Cg Ce be Cu j)]
      at this
  refine hz'.trans ?_
  exact Finset.single_le_sum (f := fun j => B0277.orderConst Cg Ce be Cu j)
    (fun i _ => B0277.orderConst_nonneg Cg Ce be Cu i) (Finset.mem_range.2 (by omega))

/-- Everything `Spine:SP-EST` asks for: the ten Part I train statements and the uniform bound
`sup_s ∑_{j ≤ 3} ‖D^j v_c(s)‖_∞ ≤ C` (`Spine.TrainUniform`, source line 2053). -/
def TrainEstimatesAll : Prop :=
  PartITrainEstimates ∧ TrainUniform

/-- **Conditional bundle**: the ten Part I train statements and the three analytic inputs of the
uniform derivative bound give `TrainEstimatesAll`. -/
theorem trainEstimates_of (hComparison : PartI.TrainComparison) (hOverlap : PartI.TrainOverlap)
    (hL2Decay : PartI.TrainL2Decay) (hStrain : PartI.TrainStrainIntegral)
    (hFluctInt : PartI.TrainFluctuationIntegral) (hMean : PartI.TrainMeanEquations)
    (hFluctDecay : PartI.TrainFluctuationDecay) (hExpansion : PartI.TrainMeanExpansion)
    (hTails : PartI.TrainTransverseTails) (hBand : PartI.TrainFixedBand)
    (hVc : VcRegularity) (hPre : TrainPreError) (hPost : TrainPostBound) : TrainEstimatesAll :=
  ⟨⟨hComparison, hOverlap, hL2Decay, hStrain, hFluctInt, hMean, hFluctDecay, hExpansion, hTails,
    hBand⟩, trainUniform_of_estimates (trainDerivativeEstimatesFamily_of hVc hPre hPost)⟩

end UnforcedLeray.Short.Spine

end
