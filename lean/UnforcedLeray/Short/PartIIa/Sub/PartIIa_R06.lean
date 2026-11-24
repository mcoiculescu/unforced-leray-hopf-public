import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_1_1_org
import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HalfSpaceFlatExt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermParity
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.ParChartJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.ParCompWeightJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.ParWeightJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RawStreamProfile
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RingProfileJet
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound.StreamDuhamel
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.StressMomentsAllOrders
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.PressStep

/-!
# Part II-a, task `PartII-a:R06` (`RingAxisSmooth`): decomposition and conditional proof

Source of record: `the November 2 reference manuscript`, lines 1214 and
1305–1322 (Proposition `sct:lift`, "smooth through the axis for positive time"), together with
lines 429–435 ("All higher-order versions of the argument therefore hold at fixed parameters,
without requiring a new smallness condition for each order") and Lemma `sct:heat` /
`sct:fluctuation` / `sct:expansion` (lines 438–459, 515–551).

## Mathematical Overview and Reuse of Existing Infrastructure

`RingAxisSmooth` (`Short/PartII-a/StatementsRing.lean:206`) asserts that for every `ρ > 1/2` there
exists a single threshold `ν₀ > 0` such that for all `ν ∈ (0, ν₀]`, every BUC planar train
`(ψ, p)` of period `c = ν ^ (-ρ)`, and every ring radius `R ≥ 2`, the lifted velocity
`liftVelocity R ψ` and raw pressure `liftPressure R p` agree off the symmetry axis `Axi.axis`
with Cartesian fields `(u, π)` that are jointly `C^∞` on `{z : ℝ × Space | 0 < z.1}`.

In this organizer file we prove **unconditionally** (reusing the compiled `RawParityForm/*` and
`TrainHeatFixed/*` infrastructure):
1. `trainFluctFixed : PartI.TrainFluctFixed` (`PartI:HF/4`): fixed-parameter all-order exponential
   decay of the full `(s, q, η)`-derivatives of `ψ - meanStream`, proved from
   `PartI.trainFluctAgeJetFixed` (`PartI:HF/2`) and `PartI.jointFromAgeJets` (`PartI:HF/3`).
2. `trainPressureFixed : TrainPressureFixed`: fixed-parameter all-order exponential decay of the
   full `(s, q, η)`-derivatives of `tr.p`, proved from
   `PartI.TrainFluctAgeJetFixedAux.uniform_pressure_spatial` and `PartI.jointFromAgeJets`.
3. `meanStress_weighted_zero_fixed`: fixed-parameter all-weight exponential decay
   `(1 + η ^ 2) ^ k * |meanStress tr t η| ≤ C * exp (-(κ * t))` at a single threshold `ν₀`.
4. `meanStress_unweighted_jet_fixed`: fixed-parameter all-order mixed-derivative exponential decay
   `|∂_η^b ∂_t^ℓ (meanStress tr) t η| ≤ C * exp (-(κ * t))` at a single threshold `ν₀`.
5. `parityOfExpansion : IIb.ParityOfExpansion`: assembled from the 7 compiled `RawParityForm/*`
   leaf files and `IIb.parityOfExpansion_of` / `IIb.remainderParity_of`.
6. `pressureParity`: smooth zero-extension across `w = 0` of `(R / w) * P (parChart R x)` for any
   `P` with exponential decay in `s`, proved from `IIb.parCompWeightJet`, `IIb.parWeightJet`, and
   `IIb.halfSpaceFlatExt`.
7. `ringAxisSmooth_of_heatFixed`: deduces `RingAxisSmooth` from `PartI.TrainHeatFixed` and
   `TrainPressureFixed` by composing the smooth parity coefficients `(G, H)` of `parityOfExpansion`
   and the smooth pressure parity coefficient of `pressureParity` with the spacetime-to-parity map
   `(t, x) ↦ (log t, (t⁻¹ (x₀² + x₁²), t^{-1/2} x₂))`.
8. `ringAxisSmooth_of`: deduces `RingAxisSmooth` from the four fixed-parameter 1D heat-expansion
   remainder sub-claims (`MeanDatumRemainderMixedFixed`, `MeanSourceFarBoundFixed`,
   `MeanSourceNearDiffBoundFixed`, `MeanSourceRemainderHeatStep`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short

/-! ### 1. Shared definitions and the four 1D heat-remainder sub-claims -/

/-- The far-time (`s / 2 ≤ t ≤ s`) part of the 1D inhomogeneous heat Duhamel integral
`meanSourceDuhamel tr s η`, written in the shifted Gaussian variable `z = (η - ξ) / √(ν (s - t))`
so `∂_η` lands directly on `meanStress tr t` (source lines 453–455, 535–538). -/
def meanSourceFar {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  ∫ t in (s / 2)..s, ∫ z : ℝ,
    PartI.heatKernel1 1 z * PartI.meanStress tr t (η - Real.sqrt (ν * (s - t)) * z)

/-- **Sub-claim 1 (`PartII-a:R06/1`): fixed-parameter mixed-derivative Taylor remainder bound for
the initial-datum part `meanDatumRemainder`** (source lines 429–435, 451–458, 528–535; cf.
`Short/PartI/Tasks/TrainMeanExpansion/RemainderLpBound/DatumRemainderBound.lean` at `m = 0`):
for any `0 < ν ≤ 1`, `1 ≤ c`, and `tr : B0140.TrainSol ν c`, Taylor-expanding `G_{1 + ν s}(η)`
around `G_{ν s}(η)` to order `N` gives
`|∂_η^b ∂_s^ℓ R_N^{(0)}(s, η)| ≤ C * s ^ ((-b - 2N - 3)/2 - ℓ)` for `s ≥ 1`. -/
def MeanDatumRemainderMixedFixed : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ c → ∀ (tr : B0140.TrainSol ν c) (N b ℓ : ℕ),
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η| ≤
        C * s ^ ((-(b : ℝ) - 2 * N - 3) / 2 - ℓ)

/-- **Sub-claim 2 (`PartII-a:R06/2`): fixed-parameter spatial-derivative bound for the far-time
source Duhamel integral `meanSourceFar`** (source lines 429–435, 453–455, 535–538; cf.
`iteratedDeriv_D_far` and `bound_D_far` in
`Short/PartI/Tasks/TrainMeanExpansion/RemainderLpBound/SourceRemainderBound.lean` at `m = 0`):
if all spatial derivatives of `meanStress tr t` decay exponentially in `t`, then for every
`N, b : ℕ` and `s ≥ 1`, `meanSourceFar tr s` is `C^b` on `ℝ` with
`|∂_η^b (meanSourceFar tr s) η| ≤ C * s ^ ((-b - 2N - 3)/2)`. -/
def MeanSourceFarBoundFixed : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, PartI.IsBUCTrain tr →
    (∀ k : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      |iteratedDeriv k (PartI.meanStress tr t) η| ≤ C * Real.exp (-(κ * t))) →
    ∀ N b : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s →
      ContDiff ℝ b (meanSourceFar tr s) ∧
      ∀ η : ℝ, |iteratedDeriv b (meanSourceFar tr s) η| ≤
        C * s ^ ((-(b : ℝ) - 2 * N - 3) / 2)

/-- **Sub-claim 3 (`PartII-a:R06/3`): fixed-parameter spatial-derivative bound for the near-time
Taylor remainder and far-time polynomial tail `meanSourceRemainder tr N s - meanSourceFar tr s`**
(source lines 429–435, 451–458, 531–538; cf. `iteratedDeriv_D_near`, `near_time_slice_eq`, and
`trainMeanSourceRemainderBound_zero` in
`Short/PartI/Tasks/TrainMeanExpansion/RemainderLpBound/SourceRemainderBound.lean` at `m = 0`):
if `(1 + η ^ 2) ^ k * |meanStress tr t η|` decays exponentially in `t` for every `k : ℕ`, then for
every `N, b : ℕ` and `s ≥ 1`, `e ↦ meanSourceRemainder tr N s e - meanSourceFar tr s e` is `C^b`
on `ℝ` with `|∂_η^b (meanSourceRemainder tr N s - meanSourceFar tr s) η| ≤ C * s ^ ((-b - 2N - 3)/2)`. -/
def MeanSourceNearDiffBoundFixed : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, PartI.IsBUCTrain tr →
    (∀ k : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      (1 + η ^ 2) ^ k * |PartI.meanStress tr t η| ≤ C * Real.exp (-(κ * t))) →
    ∀ N b : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s →
      ContDiff ℝ b (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) ∧
      ∀ η : ℝ,
        |iteratedDeriv b (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) η| ≤
          C * s ^ ((-(b : ℝ) - 2 * N - 3) / 2)

/-- **Sub-claim 4 (`PartII-a:R06/4`): 1D inhomogeneous heat PDE step for nested slice derivatives
of `meanSourceRemainder`** (source lines 450, 534; cf. `slice_meanSourceRemainder_succ` in Section 7
of `Short/PartI/Tasks/TrainMeanExpansion/RemainderLpBound/SourceRemainderBound.lean`):
under the Duhamel decomposition `meanStream = meanDatumDuhamel + meanSourceDuhamel`,
`∂_η^b ∂_s^{ℓ+1} R_N^{(g)}(s, η) = ν ∂_η^{b+2} ∂_s^ℓ R_N^{(g)}(s, η) + ∂_η^b ∂_s^ℓ g(s, η)`. -/
def MeanSourceRemainderHeatStep : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, PartI.IsBUCTrain tr →
    (∀ r : ℝ, 0 < r → ∀ e : ℝ,
      PartI.meanStream tr r e = PartI.meanDatumDuhamel tr r e + PartI.meanSourceDuhamel tr r e) →
    ∀ (N b ℓ : ℕ) (s : ℝ), 0 < s → ∀ η : ℝ,
      iteratedDeriv b (fun e => iteratedDeriv (ℓ + 1) (fun r => PartI.meanSourceRemainder tr N r e) s) η =
        ν * iteratedDeriv (b + 2) (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η +
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) s) η

/-- Fixed-parameter all-order exponential decay of the full `(s, q, η)`-derivatives of the train
pressure `tr.p` (SP lines 429–435, 439–446). -/
def TrainPressureFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (PartI.trainPeriod ρ ν), PartI.IsBUCTrain tr →
      ∀ i : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => tr.p x.1 x.2) y‖ ≤
          C * Real.exp (-(κ * y.1))

/-! ### 2. Unconditional fixed-parameter fluctuation, pressure, and `meanStress` decay -/

/-- Joint `C^∞` smoothness of `tr.ψ - meanStream tr` on `(0, ∞) × Plane`. -/
theorem contDiffOn_streamFluct_meanStream {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2 - PartI.meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) := by
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    PartI.trainStreamSmooth ν c hν hc tr htr
  have hm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => PartI.meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (PartI.trainMeanEquations_proof ν c hν hc tr htr).1
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  exact hψ.sub (hm.comp hproj.contDiffOn fun x hx => ⟨hx.1, trivial⟩)

/-- **Unconditional proof of `PartI.TrainFluctFixed` (`PartI:HF/4`)** from
`PartI.trainFluctAgeJetFixed` (`PartI:HF/2`) and `PartI.jointFromAgeJets` (`PartI:HF/3`). -/
theorem trainFluctFixed : PartI.TrainFluctFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, hAge⟩ := PartI.trainFluctAgeJetFixed ρ hρ
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr i => ?_⟩
  obtain ⟨K, hK0, hJ⟩ := PartI.jointFromAgeJets i
  have hc0 : 0 < PartI.trainPeriod ρ ν := Real.rpow_pos_of_pos hν (-ρ)
  have hF_eq : (fun r (z : Plane) => tr.ψ r z - PartI.meanStream tr r z.2) =
      fun r (z : Plane) => tr.ψ r z - PartI.hmean (PartI.trainPeriod ρ ν) (tr.ψ r) z.2 := rfl
  choose Cℓ κℓ hκℓ hbdℓ using fun ℓ : ℕ => hAge ν hν hν_le tr htr ℓ (i - ℓ)
  set S : Finset ℕ := Finset.range (i + 1)
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos i)⟩
  set κ : ℝ := S.inf' hS_ne κℓ
  have hκ : 0 < κ := (Finset.lt_inf'_iff hS_ne).2 fun ℓ _ => hκℓ ℓ
  set C : ℝ := K * ∑ ℓ ∈ S, |Cℓ ℓ|
  refine ⟨C, κ, hκ, fun y hy => ?_⟩
  have hy0 : 0 < y.1 := zero_lt_one.trans_le hy
  have hsm := contDiffOn_streamFluct_meanStream hν hc0 tr htr
  have h1 := hJ (fun r z => tr.ψ r z - PartI.meanStream tr r z.2) hsm y hy0
  have hsum : ∑ ℓ ∈ S, ‖PartI.ageJet ℓ (i - ℓ)
      (fun r z => tr.ψ r z - PartI.meanStream tr r z.2) y.1 y.2‖ ≤
      (∑ ℓ ∈ S, |Cℓ ℓ|) * Real.exp (-(κ * y.1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have hκ_le : κ ≤ κℓ ℓ := Finset.inf'_le κℓ hℓ
    have hexp : Real.exp (-(κℓ ℓ * y.1)) ≤ Real.exp (-(κ * y.1)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hκ_le hy0.le))
    have hb := hbdℓ ℓ y.1 hy0 y.2
    rw [← hF_eq] at hb
    calc ‖PartI.ageJet ℓ (i - ℓ) (fun r z => tr.ψ r z - PartI.meanStream tr r z.2) y.1 y.2‖
        ≤ Cℓ ℓ * Real.exp (-(κℓ ℓ * y.1)) := hb
      _ ≤ |Cℓ ℓ| * Real.exp (-(κℓ ℓ * y.1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
      _ ≤ |Cℓ ℓ| * Real.exp (-(κ * y.1)) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => tr.ψ x.1 x.2 - PartI.meanStream tr x.1 x.2.2) y‖
      ≤ K * ∑ ℓ ∈ S, ‖PartI.ageJet ℓ (i - ℓ)
          (fun r z => tr.ψ r z - PartI.meanStream tr r z.2) y.1 y.2‖ := h1
    _ ≤ K * ((∑ ℓ ∈ S, |Cℓ ℓ|) * Real.exp (-(κ * y.1))) :=
        mul_le_mul_of_nonneg_left hsum hK0
    _ = C * Real.exp (-(κ * y.1)) := by dsimp [C]; ring

/-- Fixed-parameter all-order age-jet exponential decay for both `hfluct c tr.v` and `tr.p`
at a single threshold `ν₀` depending only on `ρ > 1/2` (extracted from the components proved in
`Short/PartI/Tasks/TrainHeatFixed/TrainFluctAgeJetFixed.lean`). -/
theorem trainVelPressAgeJetFixed (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (PartI.trainPeriod ρ ν), PartI.IsBUCTrain tr →
        (∀ ℓ : ℕ, PartI.TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr ℓ) ∧
        (∀ ℓ j : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
          ‖PartI.ageJet ℓ j tr.p s z‖ ≤ C * Real.exp (-(κ * s))) := by
  have hFD : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD
      (PartI.overlap_mean_decay_of PartI.overlapHighNormUniform_proof hFD
        PartI.overlap_mean_primitive PartI.overlap_mean_duhamel_split)
  obtain ⟨C₀, lam₀, ν_fl0, hC₀, hlam₀, hν_fl0, hJ0⟩ :=
    PartI.PartI_T13.overlapFluctuation_jetEnergy_zero_decay
      PartI.overlapFluctuationSmoothL2_proof
      (PartI.overlapFluctuationEnergyBalance_proof PartI.overlapFluctuationSmoothL2_proof)
      PartI.overlapHighNormUniform_proof ρ hρ
  obtain ⟨Cj, ν_bd, hCj, hν_bd, hbd1⟩ := PartI.supNormD_pointwise_bound_j hOv ρ hρ 1 le_rfl
  obtain ⟨ν_HF1, hν_HF1, hHF1⟩ := PartI.trainJetsBoundedFixed ρ hρ
  let ν₀ : ℝ := min (min ν_fl0 ν_bd) (min ν_HF1 (1 / 2))
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_fl0 hν_bd) (lt_min hν_HF1 (by norm_num))
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr => ?_⟩
  have hν_fl0_le : ν ≤ ν_fl0 := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_bd_le : ν ≤ ν_bd := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_HF1_le : ν ≤ ν_HF1 := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := by linarith
  let c := PartI.trainPeriod ρ ν
  have hc1 : 1 < c := by
    change 1 < PartI.trainPeriod ρ ν
    unfold PartI.trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  let s_c := UnforcedLeray.B0146.overlapAge ν c
  have hsc_pos : 0 < s_c := by
    dsimp [s_c]
    unfold UnforcedLeray.B0146.overlapAge
    have hc2 : 1 < c ^ 2 := one_lt_pow₀ hc1 (by norm_num)
    exact div_pos (by linarith) hν
  have hGrad : ∀ t : ℝ, 0 ≤ t →
      UnforcedLeray.B0277.supNormD 1 (PartI.overlapField ν c tr.v t) ≤
        ENNReal.ofReal (Cj * (1 + t) ^ (-(3 / 2 : ℝ))) := by
    intro t ht
    let s : ℝ := s_c + c ^ 2 * t / ν
    have hs_ge : s_c ≤ s := by
      dsimp [s]
      have : 0 ≤ c ^ 2 * t / ν := by positivity
      linarith
    have hs_nn : 0 ≤ s := hsc_pos.le.trans hs_ge
    have ht_eq : ν * (s - s_c) / c ^ 2 = t := by
      dsimp [s]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    have hpost1 := (hbd1 ν hν hν_bd_le tr htr s hs_nn).2 hs_ge
    rw [ht_eq] at hpost1
    have hscale : PartI.overlapField ν c tr.v t = PartI.scaleField c (tr.v s) := rfl
    calc UnforcedLeray.B0277.supNormD 1 (PartI.overlapField ν c tr.v t)
        = UnforcedLeray.B0277.supNormD 1 (PartI.scaleField c (tr.v s)) := by rw [hscale]
      _ ≤ ENNReal.ofReal (c ^ 3 * c ^ 1) * UnforcedLeray.B0277.supNormD 1 (tr.v s) :=
          PartI.supNormD_scaleField_le hc0.le 1 (tr.v s)
      _ ≤ ENNReal.ofReal (c ^ 3 * c ^ 1) *
            ENNReal.ofReal (Cj * (c ^ 4)⁻¹ * (1 + t) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = ENNReal.ofReal (Cj * (1 + t) ^ (-(3 / 2 : ℝ))) := by
          have h1t : 0 ≤ 1 + t := by linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hc4_ne : c ^ 4 ≠ 0 := pow_ne_zero 4 hc0.ne'
          field_simp
  have hV_all : ∀ r : ℕ, PartI.VelOrderBoundedFixed tr r :=
    fun r i => hHF1 ν hν hν_HF1_le tr htr r i
  have hFl0 : PartI.TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr 0 :=
    PartI.TrainFluctAgeJetFixedAux.velFluctOrderDecayFixed_zero hν hc1 tr htr hC₀ hlam₀ hCj.le
      (hJ0 ν hν hν_fl0_le tr htr) hGrad (hV_all 0)
  have hFl_all : ∀ r : ℕ, PartI.TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr r :=
    PartI.TrainFluctAgeJetFixedAux.velFluctOrderDecayFixed_all hν hν1 hc1 tr htr hV_all hFl0
  refine ⟨hFl_all, fun ℓ j => ?_⟩
  obtain ⟨C, κ, hC, hκ, hP⟩ :=
    PartI.TrainFluctAgeJetFixedAux.uniform_pressure_spatial hν hc1 tr htr ℓ
      (fun m _ => hV_all m) (fun m _ => hFl_all m) j
  exact ⟨C, κ, hC, hκ, fun s hs z => hP s hs z j le_rfl⟩

/-- **Unconditional proof of `TrainPressureFixed`** from `trainVelPressAgeJetFixed` and
`PartI.jointFromAgeJets`. -/
theorem trainPressureFixed : TrainPressureFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, hVP⟩ := trainVelPressAgeJetFixed ρ hρ
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr i => ?_⟩
  have hAge := (hVP ν hν hν_le tr htr).2
  obtain ⟨K, hK0, hJ⟩ := PartI.jointFromAgeJets i
  choose Cℓ κℓ _hCℓ hκℓ hbdℓ using fun ℓ : ℕ => hAge ℓ (i - ℓ)
  set S : Finset ℕ := Finset.range (i + 1)
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos i)⟩
  set κ : ℝ := S.inf' hS_ne κℓ
  have hκ : 0 < κ := (Finset.lt_inf'_iff hS_ne).2 fun ℓ _ => hκℓ ℓ
  set C : ℝ := K * ∑ ℓ ∈ S, |Cℓ ℓ|
  refine ⟨C, κ, hκ, fun y hy => ?_⟩
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have h1 := hJ tr.p hsm y hy
  have hsum : ∑ ℓ ∈ S, ‖PartI.ageJet ℓ (i - ℓ) tr.p y.1 y.2‖ ≤
      (∑ ℓ ∈ S, |Cℓ ℓ|) * Real.exp (-(κ * y.1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have hκ_le : κ ≤ κℓ ℓ := Finset.inf'_le κℓ hℓ
    have hexp : Real.exp (-(κℓ ℓ * y.1)) ≤ Real.exp (-(κ * y.1)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hκ_le hy.le))
    calc ‖PartI.ageJet ℓ (i - ℓ) tr.p y.1 y.2‖
        ≤ Cℓ ℓ * Real.exp (-(κℓ ℓ * y.1)) := hbdℓ ℓ y.1 hy y.2
      _ ≤ |Cℓ ℓ| * Real.exp (-(κℓ ℓ * y.1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
      _ ≤ |Cℓ ℓ| * Real.exp (-(κ * y.1)) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => tr.p x.1 x.2) y‖
      ≤ K * ∑ ℓ ∈ S, ‖PartI.ageJet ℓ (i - ℓ) tr.p y.1 y.2‖ := h1
    _ ≤ K * ((∑ ℓ ∈ S, |Cℓ ℓ|) * Real.exp (-(κ * y.1))) :=
        mul_le_mul_of_nonneg_left hsum hK0
    _ = C * Real.exp (-(κ * y.1)) := by dsimp [C]; ring

/-- Leibniz expansion of `fluctProd` at any positive period `c > 0`. -/
theorem leib_inst_c (hL : MixedLeibniz) (hSm : MeanStressSmooth)
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (tr : B0140.TrainSol ν c) (hb : PartI.IsBUCTrain tr)
    (q s η : ℝ) (hs : 0 < s) (a k : ℕ) :
    iteratedDeriv a (fun e => iteratedDeriv k (fun r => fluctProd tr r (q, e)) s) η =
      ∑ p ∈ meanPairs a k, ((a.choose p.1 : ℝ) * (k.choose p.2 : ℝ)) *
        (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
            (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) s) η *
          iteratedDeriv (a - p.1) (fun e => iteratedDeriv (k - p.2)
            (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) s) η) := by
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1, (q, x.2)) : ℝ × (ℝ × ℝ))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hA : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => PartI.hfluct c (fun w => tr.v x.1 w 0) (q, x.2))
      (Ioi 0 ×ˢ univ) :=
    ((hSm ν c hν hc tr hb).2.2 0).comp hg.contDiffOn
      (fun x hx => ⟨(Set.mem_prod.mp hx).1, Set.mem_univ _⟩)
  have hB : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => PartI.hfluct c (fun w => tr.v x.1 w 1) (q, x.2))
      (Ioi 0 ×ˢ univ) :=
    ((hSm ν c hν hc tr hb).2.2 1).comp hg.contDiffOn
      (fun x hx => ⟨(Set.mem_prod.mp hx).1, Set.mem_univ _⟩)
  have hL' := hL
    (fun r e => PartI.hfluct c (fun w => tr.v r w 0) (q, e))
    (fun r e => PartI.hfluct c (fun w => tr.v r w 1) (q, e))
    hA hB a k s η hs
  refine hL'.trans ?_
  unfold meanPairs
  rw [Finset.sum_product]

/-- Fixed-parameter all-order unweighted mixed-derivative exponential decay for `meanStress`:
from `VelFluctOrderDecayFixed` (proved in `trainVelPressAgeJetFixed`), for every `b, ℓ : ℕ`
there exist `C, κ > 0` such that `|∂_η^b ∂_t^ℓ (meanStress tr) t η| ≤ C * exp (-(κ * t))`. -/
theorem meanStress_unweighted_jet_of_velFluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr)
    (hFl : ∀ r : ℕ, PartI.TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr r) :
    ∀ b ℓ : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) t) η| ≤
        C * Real.exp (-(κ * t)) := by
  intro b ℓ
  let hSm := meanStressSmooth_of PartI.hmeanContDiff
  let hMix := hmeanMixedDeriv_of ageDerivSmooth
    (hmeanAgeIter_of PartI.hmeanDerivS ageDerivSmooth) hmeanEtaDeriv
  let hDF := meanStressDerivForm_of PartI.trainMeanEquations_proof hmeanMulFluct hMix hSm
  let hL := mixedLeibniz_of ageDerivSmooth
  let hSJ := sliceJetBound_of profileDict
  obtain ⟨C_F, κ_F, hCF, hκF, hF_rect⟩ :=
    PartI.TrainFluctAgeJetFixedAux.uniform_velFluct_rect b ℓ (fun r _ => hFl r)
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => PartI.hfluct c (tr.v x.1) x.2)
      (Ioi 0 ×ˢ univ) := by
    refine (contDiffOn_piLp 2).2 fun k => ?_
    refine ((hSm ν c hν hc tr htr).2.2 k).congr fun x hx => ?_
    exact (fvs_hfluct_apply c (tr.v x.1)
      (fvs_slice_continuous tr (le_of_lt (Set.mem_Ioi.mp hx.1))) k x.2).symm
  have hcomp_bd : ∀ (j : Fin 2) (i r : ℕ), i ≤ b → r ≤ ℓ → ∀ (t : ℝ), 0 < t → ∀ (q η : ℝ),
      |iteratedDeriv i (fun e => iteratedDeriv r
        (fun s => PartI.hfluct c (fun w => tr.v s w j) (q, e)) t) η| ≤
        C_F * Real.exp (-(κ_F * t)) := by
    intro j i r hi hr t ht q η
    have hFG : ∀ s : ℝ, 0 < s → ∀ z : ℝ × ℝ,
        PartI.hfluct c (fun w => tr.v s w j) z = (PartI.hfluct c (tr.v s) z) j :=
      fun s hs z => fvs_hfluct_apply c (tr.v s) (fvs_slice_continuous tr hs.le) j z
    have hprof := contDiffOn_trainProfile_of
      (F := fun s z => PartI.hfluct c (fun w => tr.v s w j) z)
      ((hSm ν c hν hc tr htr).2.2 j)
    have hslice := hSJ (fun s z => PartI.hfluct c (fun w => tr.v s w j) z) hprof i 0 r q η t ht
    simp only [iteratedDeriv_zero, Nat.add_zero] at hslice
    have hkey := fvs_ageJet_proj_le (G := fun s z => PartI.hfluct c (tr.v s) z) hG j
      (fun s z => PartI.hfluct c (fun w => tr.v s w j) z) hFG i r ht (q, η)
    exact (hslice.trans hkey).trans (hF_rect t ht (q, η) r hr i hi)
  set C_sum : ℝ := ∑ p ∈ meanPairs b ℓ, |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)|
  set C_out : ℝ := max (C_sum * C_F ^ 2) 1
  refine ⟨C_out, κ_F, lt_max_of_lt_right one_pos, hκF, fun t ht η => ?_⟩
  rw [hDF ν c hν hc tr htr b ℓ t η ht]
  have hpt : ∀ q ∈ Ioc (-c / 2) (c / 2),
      1 * |iteratedDeriv b (fun e => iteratedDeriv ℓ
        (fun r => fluctProd tr r (q, e)) t) η| ≤
        (C_sum * C_F ^ 2) * Real.exp (-(κ_F * t)) := by
    intro q _
    rw [one_mul, leib_inst_c hL hSm ν c hν hc tr htr q t η ht b ℓ]
    calc |∑ p ∈ meanPairs b ℓ, ((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)) *
          (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
              (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η *
            iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η)|
        ≤ ∑ p ∈ meanPairs b ℓ, |((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)) *
          (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
              (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η *
            iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ meanPairs b ℓ,
          |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| * (C_F ^ 2 * Real.exp (-(κ_F * t))) := by
          refine Finset.sum_le_sum fun p (hp : p ∈ meanPairs b ℓ) => ?_
          have hp_mem : p.1 < b + 1 ∧ p.2 < ℓ + 1 := by
            simpa [meanPairs] using hp
          have hp1 : p.1 ≤ b := Nat.lt_succ_iff.1 hp_mem.1
          have hp2 : p.2 ≤ ℓ := Nat.lt_succ_iff.1 hp_mem.2
          have h0 := hcomp_bd 0 p.1 p.2 hp1 hp2 t ht q η
          have h1' := hcomp_bd 1 (b - p.1) (ℓ - p.2) (Nat.sub_le b p.1) (Nat.sub_le ℓ p.2) t ht q η
          have hexp_le1 : Real.exp (-(κ_F * t)) ≤ 1 :=
            Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκF.le ht.le))
          have h1_const : |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) t) η| ≤ C_F :=
            h1'.trans (mul_le_of_le_one_right hCF.le hexp_le1)
          rw [abs_mul ((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)),
            abs_mul (iteratedDeriv p.1 _ η)]
          calc |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                    (fun s => PartI.hfluct c (fun w => tr.v s w 0) (q, e)) t) η| *
                  |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                    (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) t) η|)
              ≤ |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                  ((C_F * Real.exp (-(κ_F * t))) * C_F) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul h0 h1_const (abs_nonneg _) (by positivity)) (abs_nonneg _)
            _ = |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| * (C_F ^ 2 * Real.exp (-(κ_F * t))) := by
                ring
      _ = (C_sum * C_F ^ 2) * Real.exp (-(κ_F * t)) := by
          dsimp [C_sum]
          rw [← Finset.sum_mul, mul_assoc]
  have havg := avg_bound (c := c) (η := η) hc zero_le_one
    (fun q η' => iteratedDeriv b (fun e => iteratedDeriv ℓ
      (fun r => fluctProd tr r (q, e)) t) η') hpt
  rw [one_mul] at havg
  exact havg.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))

/-- If `0 ≤ X`, `0 ≤ A`, `0 ≤ B`, `X ≤ A ^ 2`, and `X ≤ B ^ 2`, then `X ≤ A * B`. -/
theorem le_mul_of_le_sq {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : X ≤ A ^ 2) (h2 : X ≤ B ^ 2) : X ≤ A * B := by
  have hsq : X ^ 2 ≤ (A * B) ^ 2 := by
    calc X ^ 2 = X * X := sq X
      _ ≤ A ^ 2 * B ^ 2 := mul_le_mul h1 h2 hX (sq_nonneg A)
      _ = (A * B) ^ 2 := (mul_pow A B 2).symm
  exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hA hB)).2

/-- For `x ≥ 0` and `α > 0`, `(1 + x) ^ (m + 1) ≤ (1 + ((m + 1 : ℕ) : ℝ) / α) ^ (m + 1) * exp (α * x)`. -/
theorem one_add_pow_le_exp {x α : ℝ} (hx : 0 ≤ x) (hα : 0 < α) (m : ℕ) :
    (1 + x) ^ (m + 1) ≤ (1 + (((m + 1 : ℕ) : ℝ) / α)) ^ (m + 1) * Real.exp (α * x) := by
  set M : ℝ := ((m + 1 : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  set δ : ℝ := α / M
  have hδ : 0 < δ := div_pos hα hM
  have hδ_inv : δ⁻¹ = M / α := inv_div α M
  have h1 : 1 + x ≤ (1 + δ⁻¹) * (1 + δ * x) := by
    have hmul : δ⁻¹ * (δ * x) = x := by field_simp [hδ.ne']
    have hnn1 : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
    have hnn2 : 0 ≤ δ * x := mul_nonneg hδ.le hx
    nlinarith
  have h2 : 1 + δ * x ≤ Real.exp (δ * x) := by
    linarith [Real.add_one_le_exp (δ * x)]
  have h3 : 1 + x ≤ (1 + (M / α)) * Real.exp (δ * x) := by
    rw [← hδ_inv]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc (1 + x) ^ (m + 1)
      ≤ ((1 + (M / α)) * Real.exp (δ * x)) ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) h3 (m + 1)
    _ = (1 + (M / α)) ^ (m + 1) * (Real.exp (δ * x)) ^ (m + 1) := mul_pow _ _ _
    _ = (1 + (M / α)) ^ (m + 1) * Real.exp (α * x) := by
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        change M * (α / M * x) = α * x
        field_simp [hM.ne']

/-- Pointwise bound on `meanStress tr t η` from a uniform bound on `‖tr.v t (q, η)‖`. -/
theorem norm_meanStress_le_of_norm_v_le {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {t η M : ℝ} (_hM : 0 ≤ M)
    (hv : ∀ q : ℝ, ‖tr.v t (q, η)‖ ≤ M) :
    ‖PartI.meanStress tr t η‖ ≤ M ^ 2 := by
  unfold PartI.meanStress PartI.hmean
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  have hbd : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖tr.v t (q, η) 0 * tr.v t (q, η) 1‖ ≤ M ^ 2 := by
    intro q _
    rw [norm_mul]
    have h0 := PiLp.norm_apply_le (tr.v t (q, η)) 0
    have h1 := PiLp.norm_apply_le (tr.v t (q, η)) 1
    calc ‖tr.v t (q, η) 0‖ * ‖tr.v t (q, η) 1‖
        ≤ ‖tr.v t (q, η)‖ * ‖tr.v t (q, η)‖ :=
          mul_le_mul h0 h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖tr.v t (q, η)‖ ^ 2 := (sq _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hv q) 2
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (-c / 2) (c / 2)) measure_Ioc_lt_top hbd
  rw [Real.volume_real_Ioc_of_le (by linarith)] at hint
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1‖
      ≤ c⁻¹ * (M ^ 2 * (c / 2 - -c / 2)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc.le)
    _ = M ^ 2 := by
        rw [show c / 2 - -c / 2 = c by ring]
        field_simp [hc.ne']

/-- Combining the linear and Gaussian transverse tail exponentials into a single linear exponential
in `l ≥ 0` with denominator `D = c + C₀ + ν * t`. -/
theorem tail_exp_sum_le {b c C₀ ν t l : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hC₀ : 0 < C₀) (hν : 0 < ν) (ht : 0 < t) (hl : 0 ≤ l) :
    Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t))) ≤
      (1 + Real.exp (b / C₀)) * Real.exp (-(b * l / (c + C₀ + ν * t))) := by
  set D : ℝ := c + C₀ + ν * t
  have hνt : 0 < ν * t := mul_pos hν ht
  have hCt : 0 < C₀ + ν * t := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h1 : Real.exp (-(b * l / c)) ≤ Real.exp (-(b * l / D)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) hc (by dsimp [D]; linarith)
  have h2_exp : -(b * l ^ 2 / (C₀ + ν * t)) ≤ b / C₀ - b * l / D := by
    rcases le_total l 1 with hl1 | hl1
    · have h_le : b * l / D ≤ b / C₀ := by
        calc b * l / D ≤ b * 1 / D := by gcongr
          _ = b / D := by ring
          _ ≤ b / C₀ := div_le_div_of_nonneg_left hb.le hC₀ (by dsimp [D]; linarith)
      have h_nn : 0 ≤ b * l ^ 2 / (C₀ + ν * t) := by positivity
      linarith
    · have h_le : b * l / D ≤ b * l ^ 2 / (C₀ + ν * t) := by
        calc b * l / D ≤ b * l / (C₀ + ν * t) :=
              div_le_div_of_nonneg_left (by positivity) hCt (by dsimp [D]; linarith)
          _ ≤ b * l ^ 2 / (C₀ + ν * t) := by
              gcongr
              nlinarith
      have h_nn : 0 ≤ b / C₀ := by positivity
      linarith
  have h2 : Real.exp (-(b * l ^ 2 / (C₀ + ν * t))) ≤
      Real.exp (b / C₀) * Real.exp (-(b * l / D)) := by
    rw [← Real.exp_add, ← sub_eq_add_neg]
    exact Real.exp_le_exp.2 h2_exp
  calc Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t)))
      ≤ Real.exp (-(b * l / D)) + Real.exp (b / C₀) * Real.exp (-(b * l / D)) :=
        add_le_add h1 h2
    _ = (1 + Real.exp (b / C₀)) * Real.exp (-(b * l / D)) := by ring

/-- Even-power polynomial weight absorption into `exp (-(b * |η| / D))` with an integrable
`(1 + η ^ 2)⁻¹` factor remaining. -/
theorem pow_mul_exp_eta_le_inv_one_add_sq {b D : ℝ} (hb : 0 < b) (hD : 0 < D)
    (k : ℕ) (η : ℝ) :
    η ^ (2 * k) * Real.exp (-(b * |η| / D)) ≤
      (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹ := by
  have hα : 0 < b / D := div_pos hb hD
  have h_one_add := one_add_pow_le_exp (abs_nonneg η) hα (2 * k + 1)
  have h_lhs : η ^ (2 * k) * (1 + η ^ 2) ≤ (1 + |η|) ^ (2 * k + 1 + 1) := by
    have h_even : η ^ (2 * k) = |η| ^ (2 * k) := by
      rw [pow_mul, pow_mul, sq_abs]
    have h_sq : 1 + η ^ 2 ≤ (1 + |η|) ^ 2 := by
      have : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
      have : 0 ≤ |η| := abs_nonneg η
      nlinarith
    have h_pow : |η| ^ (2 * k) ≤ (1 + |η|) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg η) (by linarith) (2 * k)
    rw [h_even, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    exact mul_le_mul h_pow h_sq (by positivity) (by positivity)
  have h_exp_eq : (b / D) * |η| = b * |η| / D := by ring
  rw [h_exp_eq] at h_one_add
  have h_comb : η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D)) ≤
      (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) := by
    calc η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D))
        ≤ (1 + |η|) ^ (2 * k + 1 + 1) * Real.exp (-(b * |η| / D)) :=
          mul_le_mul_of_nonneg_right h_lhs (Real.exp_nonneg _)
      _ ≤ ((1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) *
            Real.exp (b * |η| / D)) * Real.exp (-(b * |η| / D)) :=
          mul_le_mul_of_nonneg_right h_one_add (Real.exp_nonneg _)
      _ = (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h_pos : 0 < 1 + η ^ 2 := by positivity
  calc η ^ (2 * k) * Real.exp (-(b * |η| / D))
      = (η ^ (2 * k) * (1 + η ^ 2) * Real.exp (-(b * |η| / D))) * (1 + η ^ 2)⁻¹ := by
        field_simp [h_pos.ne']
    _ ≤ (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h_comb (inv_nonneg.2 h_pos.le)

/-- Absorption `(1 + t) ^ M * exp (-(κ₀ * t)) ≤ C * exp (-((κ₀ / 2) * t))` for `t ≥ 0`. -/
theorem one_add_pow_mul_exp_le {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1 + t) ^ M * Real.exp (-(κ₀ * t)) ≤ C * Real.exp (-((κ₀ / 2) * t)) := by
  set α : ℝ := κ₀ / 2
  have hα : 0 < α := half_pos hκ₀
  set K : ℝ := (1 + (((M + 1 : ℕ) : ℝ) / α)) ^ (M + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun t ht => ?_⟩
  have h1 : (1 + t) ^ M ≤ (1 + t) ^ (M + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ M)
  have h2 := one_add_pow_le_exp ht hα M
  have h3 : (1 + t) ^ M ≤ K * Real.exp (α * t) := h1.trans h2
  calc (1 + t) ^ M * Real.exp (-(κ₀ * t))
      ≤ (K * Real.exp (α * t)) * Real.exp (-(κ₀ * t)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = K * Real.exp (α * t + -(κ₀ * t)) := by rw [mul_assoc, ← Real.exp_add]
    _ = K * Real.exp (-((κ₀ / 2) * t)) := by
        congr 2
        dsimp [α]
        ring

/-- Fixed-parameter all-weight exponential decay `(1 + η ^ 2) ^ k * |meanStress tr t η| ≤ C * exp (-(κ * t))`
at a single threshold `ν₀` depending only on `ρ > 1/2` (from the `(0, 0)` transverse velocity tail
and `meanStress_unweighted_jet_of_velFluct` at `(0, 0)`, as in `StressMomentsAllOrders.lean`). -/
theorem meanStress_weighted_zero_fixed (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (PartI.trainPeriod ρ ν), PartI.IsBUCTrain tr →
        ∀ k : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
          (1 + η ^ 2) ^ k * |PartI.meanStress tr t η| ≤ C * Real.exp (-(κ * t)) := by
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
      (PartI.overlap_mean_decay_of PartI.overlapHighNormUniform_proof
        (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
        PartI.overlap_mean_primitive PartI.overlap_mean_duhamel_split)
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv (PartI.train_vorticity_gaussian_tail hOv)
  obtain ⟨b, C₀, C', hb, hC₀, hC', C₁, N₁, ν₁, hC₁, hν₁, hTail⟩ := hTails.2.1 ρ hρ 0 0
  obtain ⟨ν₂, hν₂, hVP⟩ := trainVelPressAgeJetFixed ρ hρ
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν hν_le tr htr k => ?_⟩
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := PartI.trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  obtain ⟨C₂, κ₂, hC₂, hκ₂, hUnw⟩ :=
    meanStress_unweighted_jet_of_velFluct hν hc tr htr (hVP ν hν hν₂_le tr htr).1 0 0
  set R₀ : ℝ := C' / ν + 2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  set P₂ : ℝ := Real.sqrt C₂
  have hP₂ : 0 < P₂ := Real.sqrt_pos.2 hC₂
  set P₁ : ℝ := C₁ * (1 + c + ν⁻¹) ^ N₁ * (1 + Real.exp (b / C₀))
  have hP₁ : 0 < P₁ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    dsimp [P₁]; positivity
  set B₀ : ℝ := P₂ * (P₂ + P₁) * Real.exp (b * R₀ / c)
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  set κ₀ : ℝ := κ₂ / 2
  have hκ₀ : 0 < κ₀ := half_pos hκ₂
  have h_stress_bd : ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      |PartI.meanStress tr t η| ≤
        B₀ * (1 + t) ^ N₁ * Real.exp (-(κ₀ * t)) *
          Real.exp (-(b * |η| / (c + C₀ + ν * t))) := by
    intro t ht η
    set D : ℝ := c + C₀ + ν * t
    have hνt : 0 < ν * t := mul_pos hν ht
    have hD : 0 < D := by dsimp [D]; positivity
    have hc_le_D : c ≤ D := by dsimp [D]; linarith
    let A₁ : ℝ := P₂ * Real.exp (-(κ₀ * t))
    have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
    have hbd1 : ‖PartI.meanStress tr t η‖ ≤ A₁ ^ 2 := by
      have h0 := hUnw t ht η
      simp only [iteratedDeriv_zero] at h0
      rw [Real.norm_eq_abs]
      refine h0.trans (le_of_eq ?_)
      dsimp [A₁, P₂, κ₀]
      rw [mul_pow, Real.sq_sqrt hC₂.le, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    let A₂ : ℝ := (P₂ + P₁) * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ *
      Real.exp (-(b * |η| / D))
    have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
    have hbd2 : ‖PartI.meanStress tr t η‖ ≤ A₂ ^ 2 := by
      rcases le_total |η| R₀ with hη | hη
      · have h_exp1 : Real.exp (-(κ₀ * t)) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
        have h_t1 : 1 ≤ (1 + t) ^ N₁ := one_le_pow₀ (by linarith)
        have h_eta_le : b * |η| / D ≤ b * R₀ / c := by
          calc b * |η| / D ≤ b * R₀ / D := by gcongr
            _ ≤ b * R₀ / c := div_le_div_of_nonneg_left (by positivity) hc hc_le_D
        have h_exp2 : 1 ≤ Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D)) := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
          exact Real.one_le_exp (by linarith)
        have hA₁_le_A₂ : A₁ ≤ A₂ := by
          calc A₁ = P₂ * Real.exp (-(κ₀ * t)) := rfl
            _ ≤ P₂ * 1 := mul_le_mul_of_nonneg_left h_exp1 hP₂.le
            _ ≤ (P₂ + P₁) * 1 := by linarith
            _ ≤ (P₂ + P₁) * (Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D))) :=
                mul_le_mul_of_nonneg_left h_exp2 (by positivity)
            _ = (P₂ + P₁) * Real.exp (b * R₀ / c) * 1 * Real.exp (-(b * |η| / D)) := by ring
            _ ≤ (P₂ + P₁) * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ *
                  Real.exp (-(b * |η| / D)) := by gcongr
        exact hbd1.trans (pow_le_pow_left₀ hA₁ hA₁_le_A₂ 2)
      · set l : ℝ := |η| - R₀
        have hl : 0 ≤ l := sub_nonneg.2 hη
        let M : ℝ := P₁ * Real.exp (b * R₀ / c) * (1 + t) ^ N₁ * Real.exp (-(b * |η| / D))
        have hM_nn : 0 ≤ M := by dsimp [M]; positivity
        have hv_pt : ∀ q : ℝ, ‖tr.v t (q, η)‖ ≤ M := by
          intro q
          have hz : C' / ν + 2 + l ≤ |((q, η) : Plane).2| := by
            change C' / ν + 2 + (|η| - (C' / ν + 2)) ≤ |η|
            linarith
          have h_tail_q := (hTail t ht.le ν hν hν₁_le tr htr l hl t ht le_rfl (q, η) hz).2.1
          rw [PartI.PartI_T23.norm_ageJet_zero_zero] at h_tail_q
          have h_sum := tail_exp_sum_le hb hc hC₀ hν ht hl
          have h_poly : PartI.polyPS C₁ N₁ ν c t * (1 + Real.exp (b / C₀)) =
              P₁ * (1 + t) ^ N₁ := by
            dsimp [PartI.polyPS, P₁]
            rw [mul_pow]
            ring
          have h_l_exp : Real.exp (-(b * l / D)) ≤
              Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            have hR_le : b * R₀ / D ≤ b * R₀ / c :=
              div_le_div_of_nonneg_left (by positivity) hc hc_le_D
            have h_eq : -(b * l / D) = b * R₀ / D + -(b * |η| / D) := by
              dsimp [l]; ring
            linarith
          calc ‖tr.v t (q, η)‖
              ≤ PartI.polyPS C₁ N₁ ν c t *
                  (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * t)))) := h_tail_q
            _ ≤ PartI.polyPS C₁ N₁ ν c t *
                  ((1 + Real.exp (b / C₀)) * Real.exp (-(b * l / D))) :=
                mul_le_mul_of_nonneg_left h_sum
                  (by unfold PartI.polyPS; have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le; positivity)
            _ = (PartI.polyPS C₁ N₁ ν c t * (1 + Real.exp (b / C₀))) *
                  Real.exp (-(b * l / D)) := by ring
            _ = P₁ * (1 + t) ^ N₁ * Real.exp (-(b * l / D)) := by rw [h_poly]
            _ ≤ P₁ * (1 + t) ^ N₁ * (Real.exp (b * R₀ / c) * Real.exp (-(b * |η| / D))) :=
                mul_le_mul_of_nonneg_left h_l_exp (by positivity)
            _ = M := by dsimp [M]; ring
        have hM_le_A₂ : M ≤ A₂ := by
          dsimp [M, A₂]; gcongr; linarith
        exact (norm_meanStress_le_of_norm_v_le hc tr hM_nn hv_pt).trans
          (pow_le_pow_left₀ hM_nn hM_le_A₂ 2)
    have h_prod := le_mul_of_le_sq (norm_nonneg _) hA₁ hA₂ hbd1 hbd2
    rw [← Real.norm_eq_abs]
    calc ‖PartI.meanStress tr t η‖ ≤ A₁ * A₂ := h_prod
      _ = B₀ * (1 + t) ^ N₁ * Real.exp (-(κ₀ * t)) *
            Real.exp (-(b * |η| / D)) := by dsimp [A₁, A₂, B₀]; ring
  set L₀ : ℝ := 1 + ((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  set K_k : ℝ := (2 : ℝ) ^ k * B₀ * (1 + L₀ ^ (2 * k + 1 + 1))
  have hK_k : 0 < K_k := by dsimp [K_k]; positivity
  obtain ⟨C_abs, hC_abs, hAbs⟩ := one_add_pow_mul_exp_le hκ₀ (N₁ + (2 * k + 1 + 1))
  refine ⟨K_k * C_abs, κ₀ / 2, mul_pos hK_k hC_abs, half_pos hκ₀, fun t ht η => ?_⟩
  set D : ℝ := c + C₀ + ν * t
  have hνt : 0 < ν * t := mul_pos hν ht
  have hD : 0 < D := by dsimp [D]; positivity
  have hD_le : D ≤ (c + C₀ + ν) * (1 + t) := by dsimp [D]; nlinarith
  have h_str := h_stress_bd t ht η
  have h_eta := pow_mul_exp_eta_le_inv_one_add_sq hb hD k η
  have h_inv_le1 : (1 + η ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [sq_nonneg η])
  have h_factor_le : 1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D)) ≤ L₀ * (1 + t) := by
    rw [div_div_eq_mul_div]
    have h1 : ((2 * k + 1 + 1 : ℕ) : ℝ) * D / b ≤
        (((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b) * (1 + t) := by
      calc ((2 * k + 1 + 1 : ℕ) : ℝ) * D / b
          ≤ ((2 * k + 1 + 1 : ℕ) : ℝ) * ((c + C₀ + ν) * (1 + t)) / b := by gcongr
        _ = (((2 * k + 1 + 1 : ℕ) : ℝ) * (c + C₀ + ν) / b) * (1 + t) := by ring
    dsimp [L₀]
    linarith
  have h_eta' : η ^ (2 * k) * Real.exp (-(b * |η| / D)) ≤
      L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1) := by
    calc η ^ (2 * k) * Real.exp (-(b * |η| / D))
        ≤ (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * (1 + η ^ 2)⁻¹ := h_eta
      _ ≤ (1 + (((2 * k + 1 + 1 : ℕ) : ℝ) / (b / D))) ^ (2 * k + 1 + 1) * 1 :=
          mul_le_mul_of_nonneg_left h_inv_le1 (by positivity)
      _ ≤ (L₀ * (1 + t)) ^ (2 * k + 1 + 1) := by
          rw [mul_one]
          exact pow_le_pow_left₀ (by positivity) h_factor_le _
      _ = L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1) := mul_pow _ _ _
  have h_jap : (1 + η ^ 2) ^ k ≤ (2 : ℝ) ^ k * (1 + η ^ (2 * k)) := by
    have h1 := pow_one_add_le k (sq_nonneg η)
    rwa [← pow_mul] at h1
  have h_exp_le1 : Real.exp (-(b * |η| / D)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  have h_t1 : 1 ≤ (1 + t) ^ (2 * k + 1 + 1) := one_le_pow₀ (by linarith)
  have h_comb_eta : (1 + η ^ 2) ^ k * Real.exp (-(b * |η| / D)) ≤
      (2 : ℝ) ^ k * (1 + L₀ ^ (2 * k + 1 + 1)) * (1 + t) ^ (2 * k + 1 + 1) := by
    calc (1 + η ^ 2) ^ k * Real.exp (-(b * |η| / D))
        ≤ (2 : ℝ) ^ k * (1 + η ^ (2 * k)) * Real.exp (-(b * |η| / D)) :=
          mul_le_mul_of_nonneg_right h_jap (Real.exp_nonneg _)
      _ = (2 : ℝ) ^ k * (Real.exp (-(b * |η| / D)) + η ^ (2 * k) * Real.exp (-(b * |η| / D))) := by
          ring
      _ ≤ (2 : ℝ) ^ k * (1 * (1 + t) ^ (2 * k + 1 + 1) +
            L₀ ^ (2 * k + 1 + 1) * (1 + t) ^ (2 * k + 1 + 1)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ h_eta') (by positivity)
          exact h_exp_le1.trans (by linarith)
      _ = (2 : ℝ) ^ k * (1 + L₀ ^ (2 * k + 1 + 1)) * (1 + t) ^ (2 * k + 1 + 1) := by ring
  calc (1 + η ^ 2) ^ k * |PartI.meanStress tr t η|
      ≤ (1 + η ^ 2) ^ k *
          (B₀ * (1 + t) ^ N₁ * Real.exp (-(κ₀ * t)) * Real.exp (-(b * |η| / D))) :=
        mul_le_mul_of_nonneg_left h_str (by positivity)
    _ = B₀ * (1 + t) ^ N₁ * Real.exp (-(κ₀ * t)) *
          ((1 + η ^ 2) ^ k * Real.exp (-(b * |η| / D))) := by ring
    _ ≤ B₀ * (1 + t) ^ N₁ * Real.exp (-(κ₀ * t)) *
          ((2 : ℝ) ^ k * (1 + L₀ ^ (2 * k + 1 + 1)) * (1 + t) ^ (2 * k + 1 + 1)) :=
        mul_le_mul_of_nonneg_left h_comb_eta (by positivity)
    _ = K_k * ((1 + t) ^ (N₁ + (2 * k + 1 + 1)) * Real.exp (-(κ₀ * t))) := by
        dsimp [K_k]; rw [pow_add]; ring
    _ ≤ K_k * (C_abs * Real.exp (-((κ₀ / 2) * t))) :=
        mul_le_mul_of_nonneg_left (hAbs t ht.le) hK_k.le
    _ = (K_k * C_abs) * Real.exp (-((κ₀ / 2) * t)) := by ring

/-! ### 3. Deduction of `TrainMeanRemMixedFixed`, `TrainMeanRemFixed`, and `TrainHeatFixed` -/

/-- `exp (-(κ * s)) ≤ K * s ^ α` for `s ≥ 1`, for any exponent `α : ℝ` and `κ > 0`. -/
theorem exp_neg_le_rpow_any (κ : ℝ) (hκ : 0 < κ) (α : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 1 ≤ s → Real.exp (-(κ * s)) ≤ K * s ^ α := by
  set M : ℕ := Nat.ceil (max (-α) 0)
  obtain ⟨C₀, _hC₀, h0⟩ := IIb.exp_neg_le_rpow κ hκ M
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos, fun s hs => ?_⟩
  have hM : -α ≤ (M : ℝ) := (le_max_left (-α) 0).trans (Nat.le_ceil _)
  have hexp_le : -(M : ℝ) - 3 / 2 ≤ α := by linarith
  have hrpow : s ^ (-(M : ℝ) - 3 / 2) ≤ s ^ α :=
    Real.rpow_le_rpow_of_exponent_le hs hexp_le
  have hs_pos : 0 ≤ s ^ (-(M : ℝ) - 3 / 2) := Real.rpow_nonneg (zero_le_one.trans hs) _
  calc Real.exp (-(κ * s))
      ≤ C₀ * s ^ (-(M : ℝ) - 3 / 2) := h0 s hs
    _ ≤ max C₀ 1 * s ^ (-(M : ℝ) - 3 / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hs_pos
    _ ≤ max C₀ 1 * s ^ α :=
        mul_le_mul_of_nonneg_left hrpow (le_of_lt (lt_max_of_lt_right one_pos))

/-- **Deduction of `PartI.TrainMeanRemMixedFixed` (`PartI:HF/6`)** from the four 1D heat-expansion
remainder sub-claims (`MeanDatumRemainderMixedFixed`, `MeanSourceFarBoundFixed`,
`MeanSourceNearDiffBoundFixed`, `MeanSourceRemainderHeatStep`). -/
theorem trainMeanRemMixedFixed_of
    (hDatum : MeanDatumRemainderMixedFixed)
    (hFar : MeanSourceFarBoundFixed)
    (hNear : MeanSourceNearDiffBoundFixed)
    (hStep : MeanSourceRemainderHeatStep) :
    PartI.TrainMeanRemMixedFixed := by
  intro ρ hρ
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
      (PartI.overlap_mean_decay_of PartI.overlapHighNormUniform_proof
        (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
        PartI.overlap_mean_primitive PartI.overlap_mean_duhamel_split)
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv (PartI.train_vorticity_gaussian_tail hOv)
  have hFD : PartI.TrainFluctuationDecay :=
    PartI.trainFluctuationDecay_proof hTails
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof) hOv
  obtain ⟨ν_duh, hν_duh, hDuhAll⟩ :=
    PartI.trainMeanStreamDuhamel_proof hTails hFD PartI.overlap_mean_primitive ρ hρ
  obtain ⟨ν₁, hν₁, hVP⟩ := trainVelPressAgeJetFixed ρ hρ
  obtain ⟨ν₂, hν₂, hW⟩ := meanStress_weighted_zero_fixed ρ hρ
  let ν₀ : ℝ := min (min ν₁ ν₂) (min ν_duh (1 / 2))
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁ hν₂) (lt_min hν_duh (by norm_num))
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr N b ℓ => ?_⟩
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_duh_le : ν ≤ ν_duh := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := by linarith
  let c := PartI.trainPeriod ρ ν
  have hc1 : 1 < c := by
    change 1 < PartI.trainPeriod ρ ν
    unfold PartI.trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  have hDuh : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      PartI.meanStream tr r e = PartI.meanDatumDuhamel tr r e + PartI.meanSourceDuhamel tr r e :=
    hDuhAll ν hν hν_duh_le tr htr
  have hStressJet := meanStress_unweighted_jet_of_velFluct hν hc0 tr htr (hVP ν hν hν₁_le tr htr).1
  have hStressSpatial : ∀ k : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      |iteratedDeriv k (PartI.meanStress tr t) η| ≤ C * Real.exp (-(κ * t)) := by
    intro k
    obtain ⟨C, κ, hC, hκ, hbd⟩ := hStressJet k 0
    exact ⟨C, κ, hC, hκ, fun t ht η => by simpa [iteratedDeriv_zero] using hbd t ht η⟩
  have hStressWeight := hW ν hν hν₂_le tr htr
  -- Base case `ℓ = 0` for `meanSourceRemainder` for all `b' : ℕ`
  have hSrcZero : ∀ b' : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      |iteratedDeriv b' (PartI.meanSourceRemainder tr N s) η| ≤
        C * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2) := by
    intro b'
    obtain ⟨C_far, hC_far⟩ := hFar ν c hν hν1 hc1.le tr htr hStressSpatial N b'
    obtain ⟨C_near, hC_near⟩ := hNear ν c hν hν1 hc1.le tr htr hStressWeight N b'
    refine ⟨C_near + C_far, fun s hs η => ?_⟩
    obtain ⟨hcd_far, hbd_far⟩ := hC_far s hs
    obtain ⟨hcd_near, hbd_near⟩ := hC_near s hs
    have hfun : (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) +
        meanSourceFar tr s = PartI.meanSourceRemainder tr N s := by
      funext e; simp [Pi.add_apply]
    have h_add : iteratedDeriv b' (PartI.meanSourceRemainder tr N s) η =
        iteratedDeriv b' (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) η +
          iteratedDeriv b' (meanSourceFar tr s) η := by
      have h1 := iteratedDeriv_add (x := η) hcd_near.contDiffAt hcd_far.contDiffAt
      rwa [hfun] at h1
    rw [h_add]
    calc |iteratedDeriv b' (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) η +
            iteratedDeriv b' (meanSourceFar tr s) η|
        ≤ |iteratedDeriv b' (fun e => PartI.meanSourceRemainder tr N s e - meanSourceFar tr s e) η| +
            |iteratedDeriv b' (meanSourceFar tr s) η| := abs_add_le _ _
      _ ≤ C_near * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2) +
            C_far * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2) :=
          add_le_add (hbd_near η) (hbd_far η)
      _ = (C_near + C_far) * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2) := by ring
  -- Induction on `ℓ` for `meanSourceRemainder`
  have hSrcAll : ∀ ℓ' b' : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      |iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanSourceRemainder tr N r e) s) η| ≤
        C * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ℓ') := by
    intro ℓ'
    induction ℓ' with
    | zero =>
      intro b'
      obtain ⟨C₀, hC₀⟩ := hSrcZero b'
      refine ⟨C₀, fun s hs η => ?_⟩
      simpa [iteratedDeriv_zero] using hC₀ s hs η
    | succ ℓ' ih =>
      intro b'
      obtain ⟨C_ih, hC_ih⟩ := ih (b' + 2)
      obtain ⟨C_st, κ_st, hC_st, hκ_st, hbd_st⟩ := hStressJet b' ℓ'
      obtain ⟨K_exp, hK_exp, h_exp⟩ :=
        exp_neg_le_rpow_any κ_st hκ_st ((-(b' : ℝ) - 2 * N - 3) / 2 - (ℓ' + 1 : ℕ))
      refine ⟨ν * C_ih + C_st * K_exp, fun s hs η => ?_⟩
      have hs0 : 0 < s := zero_lt_one.trans_le hs
      have h_eq := hStep ν c hν hc1.le tr htr hDuh N b' ℓ' s hs0 η
      have h_exp_eq : (-(↑(b' + 2) : ℝ) - 2 * ↑N - 3) / 2 - ↑ℓ' =
          (-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1) := by
        push_cast; ring
      have h1 := hC_ih s hs η
      rw [h_exp_eq] at h1
      have h2 : |iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanStress tr r e) s) η| ≤
          (C_st * K_exp) * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1)) := by
        calc |iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanStress tr r e) s) η|
            ≤ C_st * Real.exp (-(κ_st * s)) := hbd_st s hs0 η
          _ ≤ C_st * (K_exp * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1))) :=
              mul_le_mul_of_nonneg_left (h_exp s hs) hC_st.le
          _ = (C_st * K_exp) * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1)) := by ring
      rw [h_eq]
      calc |ν * iteratedDeriv (b' + 2)
              (fun e => iteratedDeriv ℓ' (fun r => PartI.meanSourceRemainder tr N r e) s) η +
            iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanStress tr r e) s) η|
          ≤ |ν * iteratedDeriv (b' + 2)
              (fun e => iteratedDeriv ℓ' (fun r => PartI.meanSourceRemainder tr N r e) s) η| +
            |iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanStress tr r e) s) η| :=
            abs_add_le _ _
        _ = ν * |iteratedDeriv (b' + 2)
              (fun e => iteratedDeriv ℓ' (fun r => PartI.meanSourceRemainder tr N r e) s) η| +
            |iteratedDeriv b' (fun e => iteratedDeriv ℓ' (fun r => PartI.meanStress tr r e) s) η| := by
            rw [abs_mul, abs_of_pos hν]
        _ ≤ ν * (C_ih * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1))) +
            (C_st * K_exp) * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hν.le) h2
        _ = (ν * C_ih + C_st * K_exp) * s ^ ((-(b' : ℝ) - 2 * N - 3) / 2 - ↑(ℓ' + 1)) := by ring
  obtain ⟨C_dat, hC_dat⟩ := hDatum ν c hν hν1 hc1.le tr N b ℓ
  obtain ⟨C_src, hC_src⟩ := hSrcAll ℓ b
  refine ⟨C_dat + C_src, fun s hs η => ?_⟩
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have h_split :=
    PartI.PartI_T23.meanRemainder_slice_eq_add_of_duhamel hν hc1.le tr htr hDuh N b ℓ hs0 η
  rw [Real.norm_eq_abs, h_split]
  calc |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η +
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η|
      ≤ |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η| +
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η| :=
        abs_add_le _ _
    _ ≤ C_dat * s ^ ((-(b : ℝ) - 2 * N - 3) / 2 - ℓ) +
          C_src * s ^ ((-(b : ℝ) - 2 * N - 3) / 2 - ℓ) :=
        add_le_add (hC_dat s hs η) (hC_src s hs η)
    _ = (C_dat + C_src) * s ^ ((-(b : ℝ) - 2 * N - 3) / 2 - ℓ) := by ring

/-- **Deduction of `PartI.TrainMeanRemFixed` (`PartI:HF/8`)** from `PartI.TrainMeanRemMixedFixed`
and `PartI.jointFromMixed1D` (`PartI:HF/7`). -/
theorem trainMeanRemFixed_of (hMix : PartI.TrainMeanRemMixedFixed) : PartI.TrainMeanRemFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, hM⟩ := hMix ρ hρ
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr N i => ?_⟩
  obtain ⟨K, hK0, hJ⟩ := PartI.jointFromMixed1D i
  let c := PartI.trainPeriod ρ ν
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => PartI.meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    meanRemainderSmooth_of PartI.trainMeanEquations_proof heatKernelIterSmooth ν c hν hc0 tr htr N
  choose Cℓ hbdℓ using fun ℓ : ℕ => hM ν hν hν_le tr htr N (i - ℓ) ℓ
  set S : Finset ℕ := Finset.range (i + 1)
  set C : ℝ := K * ∑ ℓ ∈ S, |Cℓ ℓ|
  refine ⟨C, fun y hy => ?_⟩
  have hy0 : 0 < y.1 := zero_lt_one.trans_le hy
  have h1 := hJ (PartI.meanRemainder tr N) hsm y hy0
  have hsum : ∑ ℓ ∈ S, ‖iteratedDeriv (i - ℓ)
      (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) y.1) y.2‖ ≤
      (∑ ℓ ∈ S, |Cℓ ℓ|) * y.1 ^ (-(N : ℝ) - 3 / 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    have hexp : (-((i - ℓ : ℕ) : ℝ) - 2 * (N : ℝ) - 3) / 2 - (ℓ : ℝ) ≤ -(N : ℝ) - 3 / 2 := by
      have hb_nn : (0 : ℝ) ≤ ((i - ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      linarith
    have hrpow : y.1 ^ ((-((i - ℓ : ℕ) : ℝ) - 2 * (N : ℝ) - 3) / 2 - (ℓ : ℝ)) ≤
        y.1 ^ (-(N : ℝ) - 3 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hy hexp
    have hrpow_nn : 0 ≤ y.1 ^ ((-((i - ℓ : ℕ) : ℝ) - 2 * (N : ℝ) - 3) / 2 - (ℓ : ℝ)) :=
      Real.rpow_nonneg hy0.le _
    calc ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) y.1) y.2‖
        ≤ Cℓ ℓ * y.1 ^ ((-((i - ℓ : ℕ) : ℝ) - 2 * (N : ℝ) - 3) / 2 - (ℓ : ℝ)) := hbdℓ ℓ y.1 hy y.2
      _ ≤ |Cℓ ℓ| * y.1 ^ ((-((i - ℓ : ℕ) : ℝ) - 2 * (N : ℝ) - 3) / 2 - (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hrpow_nn
      _ ≤ |Cℓ ℓ| * y.1 ^ (-(N : ℝ) - 3 / 2) :=
          mul_le_mul_of_nonneg_left hrpow (abs_nonneg _)
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => PartI.meanRemainder tr N x.1 x.2) y‖
      ≤ K * ∑ ℓ ∈ S, ‖iteratedDeriv (i - ℓ)
          (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) y.1) y.2‖ := h1
    _ ≤ K * ((∑ ℓ ∈ S, |Cℓ ℓ|) * y.1 ^ (-(N : ℝ) - 3 / 2)) :=
        mul_le_mul_of_nonneg_left hsum hK0
    _ = C * y.1 ^ (-(N : ℝ) - 3 / 2) := by dsimp [C]; ring

/-! ### 4. Parity extension of velocity and pressure and proof of `RingAxisSmooth` -/

/-- **Unconditional assembly of `IIb.ParityOfExpansion`** from the compiled `RawParityForm/*`
leaf theorems (`heatTermSmooth`, `heatTermParity`, `halfSpaceFlatExt`, `parWeightJet`,
`ringProfileJet`, `parCompWeightJet`). -/
theorem parityOfExpansion : IIb.ParityOfExpansion :=
  IIb.parityOfExpansion_of IIb.heatTermSmooth IIb.heatTermParity
    (IIb.remainderParity_of IIb.halfSpaceFlatExt IIb.parWeightJet
      IIb.ringProfileJet IIb.parCompWeightJet)

/-- **Smooth zero-extension across `w = 0` of the pressure parity coefficient**: if `1 ≤ R` and
`P` is `C^∞` on `(0, ∞) × Plane` with all-order exponential decay in `s`, then
`zeroExtW (fun x => R / x.2.1 * P (parChart R x))` is `C^∞` on `ℝ × (ℝ × ℝ)` (and in particular on
`parNonneg`). -/
theorem pressureParity {R : ℝ} (hR1 : 1 ≤ R) {P : ℝ × (ℝ × ℝ) → ℝ}
    (hP_sm : ContDiffOn ℝ ∞ P (Ioi 0 ×ˢ univ))
    (hP_bd : ∀ i : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ i P y‖ ≤ C * Real.exp (-(κ * y.1))) :
    ContDiff ℝ ∞ (IIb.zeroExtW (fun x => R / x.2.1 * P (IIb.parChart R x))) := by
  rw [contDiff_infty]
  intro k
  obtain ⟨hw1, _hw2, hwjet⟩ := IIb.parWeightJet R
  set β : ℝ := 2 * (k : ℝ) + 5 / 2
  have hk0 : 0 ≤ β := by dsimp [β]; positivity
  have hbP : ∀ (i : ℕ) (M : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ),
      1 ≤ y.1 → |y.2.2| ≤ M * Real.sqrt y.1 →
        ‖iteratedFDeriv ℝ i P y‖ ≤ C * y.1 ^ (-β) := by
    intro i _M
    obtain ⟨C₀, κ, hκ, hbd⟩ := hP_bd i
    obtain ⟨K, hK, hexp⟩ := exp_neg_le_rpow_any κ hκ (-β)
    refine ⟨|C₀| * K, fun y hy _ => ?_⟩
    have hy0 : 0 < y.1 := zero_lt_one.trans_le hy
    calc ‖iteratedFDeriv ℝ i P y‖
        ≤ C₀ * Real.exp (-(κ * y.1)) := hbd y hy0
      _ ≤ |C₀| * Real.exp (-(κ * y.1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)
      _ ≤ |C₀| * (K * y.1 ^ (-β)) :=
          mul_le_mul_of_nonneg_left (hexp y.1 hy) (abs_nonneg _)
      _ = (|C₀| * K) * y.1 ^ (-β) := by ring
  obtain ⟨hPs, hPb⟩ := IIb.parCompWeightJet R 1 β (fun x => R / x.2.1) P hR1 hk0 hw1 hP_sm
    (fun n => by
      obtain ⟨C, hC⟩ := hwjet n
      exact ⟨C, fun x hx hx1 i hi => (hC x hx hx1 i hi).1⟩) hbP
  refine IIb.halfSpaceFlatExt k ℝ (fun x => R / x.2.1 * P (IIb.parChart R x))
    (contDiffOn_infty.1 hPs k) ?_
  intro n hn M
  obtain ⟨C, hC⟩ := hPb n M
  refine ⟨max C 0, fun x hx hx1 hz => ?_⟩
  have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
  exact IIb.le_mul_of_rpow_bound hx hx1 (by dsimp [β]; linarith) (hC x hx hx1 hz)

/-- The spacetime-to-parity-chart map `(t, x) ↦ (log t, (t⁻¹ (x₀² + x₁²), t^{-1/2} x₂))`. -/
def physToPar (t : ℝ) (x : Space) : ℝ × (ℝ × ℝ) :=
  (Real.log t, (t⁻¹ * (x 0 ^ 2 + x 1 ^ 2), (Real.sqrt t)⁻¹ * x 2))

/-- `physToPar` is `C^∞` on `{z : ℝ × Space | 0 < z.1}`. -/
theorem contDiffOn_physToPar :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physToPar z.1 z.2) {z : ℝ × Space | 0 < z.1} := by
  have ht_ne : ∀ z ∈ ({z : ℝ × Space | 0 < z.1} : Set (ℝ × Space)), z.1 ≠ 0 :=
    fun _ hz => hz.ne'
  have hsq_ne : ∀ z ∈ ({z : ℝ × Space | 0 < z.1} : Set (ℝ × Space)), Real.sqrt z.1 ≠ 0 :=
    fun _ hz => (Real.sqrt_pos.2 hz).ne'
  have hlog : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Real.log z.1) {z : ℝ × Space | 0 < z.1} :=
    contDiffOn_fst.log ht_ne
  have ht_inv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => z.1⁻¹) {z : ℝ × Space | 0 < z.1} :=
    contDiffOn_fst.inv ht_ne
  have hsq_inv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (Real.sqrt z.1)⁻¹)
      {z : ℝ × Space | 0 < z.1} :=
    (contDiffOn_fst.sqrt ht_ne).inv hsq_ne
  have hx0 : ContDiff ℝ ∞ (fun z : ℝ × Space => z.2 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hx1 : ContDiff ℝ ∞ (fun z : ℝ × Space => z.2 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hx2 : ContDiff ℝ ∞ (fun z : ℝ × Space => z.2 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hw : ContDiffOn ℝ ∞ (fun z : ℝ × Space => z.1⁻¹ * (z.2 0 ^ 2 + z.2 1 ^ 2))
      {z : ℝ × Space | 0 < z.1} :=
    ht_inv.mul ((hx0.pow 2).add (hx1.pow 2)).contDiffOn
  have hz2 : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (Real.sqrt z.1)⁻¹ * z.2 2)
      {z : ℝ × Space | 0 < z.1} :=
    hsq_inv.mul hx2.contDiffOn
  exact hlog.prodMk (hw.prodMk hz2)

/-- For `t > 0`, `physToPar t x ∈ IIb.parNonneg`. -/
theorem physToPar_mem_parNonneg {t : ℝ} (ht : 0 < t) (x : Space) :
    physToPar t x ∈ IIb.parNonneg := by
  change 0 ≤ t⁻¹ * (x 0 ^ 2 + x 1 ^ 2)
  positivity

/-- For `t > 0` and `x ∉ Axi.axis`, `physToPar t x ∈ IIb.parPos`. -/
theorem physToPar_mem_parPos {t : ℝ} (ht : 0 < t) {x : Space} (hx : x ∉ Axi.axis) :
    physToPar t x ∈ IIb.parPos := by
  change 0 < t⁻¹ * (x 0 ^ 2 + x 1 ^ 2)
  rw [← Axi.ϱ_sq]
  have hρ : 0 < Axi.ϱ x := Axi.ϱ_pos hx
  positivity

/-- For `t > 0`, `(Real.log t, (((Real.sqrt t)⁻¹ • x) 0 ^ 2 + ((Real.sqrt t)⁻¹ • x) 1 ^ 2, ((Real.sqrt t)⁻¹ • x) 2))`
equals `physToPar t x`. -/
theorem sim_par_eq_physToPar {t : ℝ} (ht : 0 < t) (x : Space) :
    (Real.log t, ((((Real.sqrt t)⁻¹ • x) 0 ^ 2 + ((Real.sqrt t)⁻¹ • x) 1 ^ 2),
      ((Real.sqrt t)⁻¹ • x) 2)) = physToPar t x := by
  unfold physToPar
  simp only [PiLp.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  rw [mul_pow, mul_pow, ← mul_add, inv_pow, Real.sq_sqrt ht.le]

/-- **Deduction of `RingAxisSmooth` from `PartI.TrainHeatFixed` and `TrainPressureFixed`**
(source lines 1214, 1305–1322): for every `ρ > 1/2`, taking the minimum of the velocity heat-expansion
threshold and the pressure threshold gives a single `ν₀ > 0` at which both the lifted velocity
`liftVelocity R ψ` and raw pressure `liftPressure R p` extend smoothly across `Axi.axis` for `t > 0`. -/
theorem ringAxisSmooth_of_heatFixed (hHeat : PartI.TrainHeatFixed) (hPress : TrainPressureFixed) :
    RingAxisSmooth := by
  have hExp : IIb.TrainHeatExpansion :=
    IIb.trainHeatExpansion_of PartI.trainStreamSmooth PartI.trainMeanEquations_proof
      IIb.heatTermSmooth hHeat
  intro ρ hρ
  obtain ⟨ν₁, hν₁, hE⟩ := hExp ρ hρ
  obtain ⟨ν₂, hν₂, hP⟩ := hPress ρ hρ
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν ⟨hν, hν_lt⟩ ψ p ⟨tr, htr, hψ_eq, hp_eq⟩ R hR2 => ?_⟩
  have hν_le : ν ≤ min ν₁ ν₂ := hν_lt.le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let c : ℝ := ν ^ (-ρ)
  have hc_period : c = PartI.trainPeriod ρ ν := rfl
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hΨ_sm : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) (Ioi 0 ×ˢ univ) :=
    PartI.trainStreamSmooth ν c hν hc0 tr htr
  have hP_sm : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => tr.p y.1 y.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  obtain ⟨G, H, hG_sm, hH_sm, hGH⟩ := parityOfExpansion ν R hν hR1
    (PartI.meanCoeff tr) (fun y => tr.ψ y.1 y.2) hΨ_sm
    (hE ν c hν hν₁_le hc_period tr htr)
  have hP_bd : ∀ i : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2) y‖ ≤
        C * Real.exp (-(κ * y.1)) :=
    hP ν hν hν₂_le tr htr
  set P_par : ℝ × (ℝ × ℝ) → ℝ :=
    IIb.zeroExtW (fun w => R / w.2.1 * tr.p (IIb.parChart R w).1 (IIb.parChart R w).2)
  have hP_par_sm : ContDiff ℝ ∞ P_par := pressureParity hR1 hP_sm hP_bd
  set u : ℝ × Space → Space := fun z =>
    (z.1⁻¹ * G (physToPar z.1 z.2)) • Axi.hor z.2 +
      ((Real.sqrt z.1)⁻¹ * H (physToPar z.1 z.2)) • Axi.e3
  set pr : ℝ × Space → ℝ := fun z =>
    R * z.1⁻¹ * P_par (physToPar z.1 z.2)
  have ht_ne : ∀ z ∈ ({z : ℝ × Space | 0 < z.1} : Set (ℝ × Space)), z.1 ≠ 0 :=
    fun _ hz => hz.ne'
  have hsq_ne : ∀ z ∈ ({z : ℝ × Space | 0 < z.1} : Set (ℝ × Space)), Real.sqrt z.1 ≠ 0 :=
    fun _ hz => (Real.sqrt_pos.2 hz).ne'
  have ht_inv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => z.1⁻¹) {z : ℝ × Space | 0 < z.1} :=
    contDiffOn_fst.inv ht_ne
  have hsq_inv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (Real.sqrt z.1)⁻¹)
      {z : ℝ × Space | 0 < z.1} :=
    (contDiffOn_fst.sqrt ht_ne).inv hsq_ne
  have hG_comp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => G (physToPar z.1 z.2))
      {z : ℝ × Space | 0 < z.1} :=
    hG_sm.comp contDiffOn_physToPar fun z hz => physToPar_mem_parNonneg hz z.2
  have hH_comp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => H (physToPar z.1 z.2))
      {z : ℝ × Space | 0 < z.1} :=
    hH_sm.comp contDiffOn_physToPar fun z hz => physToPar_mem_parNonneg hz z.2
  have hP_comp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => P_par (physToPar z.1 z.2))
      {z : ℝ × Space | 0 < z.1} :=
    hP_par_sm.contDiffOn.comp contDiffOn_physToPar (mapsTo_univ _ _)
  have hhor_sm : ContDiff ℝ ∞ (fun z : ℝ × Space => Axi.hor z.2) := by
    have h1 : Axi.hor = fun x => Axi.horL x := funext fun x => (Axi.horL_apply x).symm
    rw [h1]
    exact Axi.horL.contDiff.comp contDiff_snd
  have hu_sm : ContDiffOn ℝ ∞ u {z : ℝ × Space | 0 < z.1} :=
    ((ht_inv.mul hG_comp).smul hhor_sm.contDiffOn).add
      ((hsq_inv.mul hH_comp).smul contDiffOn_const)
  have hpr_sm : ContDiffOn ℝ ∞ pr {z : ℝ × Space | 0 < z.1} :=
    (contDiffOn_const.mul ht_inv).mul hP_comp
  refine ⟨u, pr, hu_sm, hpr_sm, fun t ht x hx => ?_⟩
  have hpos : physToPar t x ∈ IIb.parPos := physToPar_mem_parPos ht hx
  have hm_pos : 0 < (IIb.parChart R (physToPar t x)).1 :=
    (IIb.parChart_fst_pos hR0 hpos).1
  set y : Space := (Real.sqrt t)⁻¹ • x
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hy_ax : y ∉ Axi.axis := not_mem_axis_smul (inv_pos.2 hst) hx
  have hsim_par : (Real.log t, (y 0 ^ 2 + y 1 ^ 2, y 2)) = physToPar t x :=
    sim_par_eq_physToPar ht x
  constructor
  · -- Velocity equality off `Axi.axis`
    rw [hψ_eq, liftVelocity_eq_physNv hR0 ht (trainProfile tr.ψ) hx]
    unfold Axi.physNv Axi.selfSim
    rw [pow_one]
    have hchart_y : Axi.chart R (Real.log t) y = IIb.parChart R (physToPar t x) := by
      rw [IIb.chart_eq_parChart, hsim_par]
    have hmer_eq : merProfile R (trainProfile tr.ψ) (Axi.chart R (Real.log t) y) =
        Axi.ringStreamProfile R (fun z => tr.ψ z.1 z.2) (Axi.chart R (Real.log t) y) := by
      rw [hchart_y,
        ← IIb.rawProfile_eq_merProfile_of_smooth PartI.trainStreamSmooth hν hc0 tr htr rfl hm_pos,
        IIb.rawStreamProfile ν c R tr hR0 hΨ_sm _ hm_pos]
    have hNv_eq : Axi.Nv R (merProfile R (trainProfile tr.ψ)) (Real.log t) y =
        Axi.Nv R (Axi.ringStreamProfile R (fun z => tr.ψ z.1 z.2)) (Real.log t) y := by
      unfold Axi.Nv
      rw [hmer_eq]
    rw [hNv_eq, IIb.Nv_eq_parity hR0 (Axi.ringStreamProfile R (fun z => tr.ψ z.1 z.2))
      (Real.log t) hy_ax, hsim_par]
    obtain ⟨hGx, hHx⟩ := hGH (physToPar t x) hpos
    rw [← hGx, ← hHx]
    have hhor_y : Axi.hor y = (Real.sqrt t)⁻¹ • Axi.hor x := Axi.hor_smul (Real.sqrt t)⁻¹ x
    rw [hhor_y, smul_add, smul_smul, smul_smul, smul_smul]
    dsimp [u]
    congr 2
    calc t⁻¹ * G (physToPar t x)
        = ((Real.sqrt t) ^ 2)⁻¹ * G (physToPar t x) := by rw [Real.sq_sqrt ht.le]
      _ = (Real.sqrt t)⁻¹ * G (physToPar t x) * (Real.sqrt t)⁻¹ := by ring
  · -- Pressure equality off `Axi.axis`
    rw [hp_eq]
    unfold liftPressure
    rw [rawPressure_apply]
    have hpos' : 0 < (physToPar t x).2.1 := hpos
    have hP_par_pos : P_par (physToPar t x) =
        R / (physToPar t x).2.1 *
          tr.p (IIb.parChart R (physToPar t x)).1 (IIb.parChart R (physToPar t x)).2 := by
      simp only [P_par, IIb.zeroExtW, hpos', ↓reduceIte]
    have hchart_phys : IIb.parChart R (physToPar t x) =
        (RingLift.ageCoordinate R (Axi.ϱ x) t,
          (RingLift.logRadius R (Axi.ϱ x), RingLift.transverseCoordinate R (Axi.ϱ x) (x 2))) := by
      rw [← hsim_par, ← IIb.chart_eq_parChart]
      exact Axi.chart_similarity hR0 ht hx
    have htr_p : tr.p (IIb.parChart R (physToPar t x)).1 (IIb.parChart R (physToPar t x)).2 =
        trainProfile tr.p (profileChart R (Axi.ϱ x) (x 2) t) := by
      rw [hchart_phys]
      rfl
    have hρ_pos : 0 < Axi.ϱ x := Axi.ϱ_pos hx
    have hρ_ne : Axi.ϱ x ≠ 0 := hρ_pos.ne'
    have ht_ne' : t ≠ 0 := ht.ne'
    have hscale_eq : R * t⁻¹ * (R / (physToPar t x).2.1) =
        RingLift.radialScale R (Axi.ϱ x) ^ 2 := by
      change R * t⁻¹ * (R / (t⁻¹ * (x 0 ^ 2 + x 1 ^ 2))) = (R / Axi.ϱ x) ^ 2
      rw [← Axi.ϱ_sq]
      field_simp [ht_ne', hρ_ne]
    dsimp [pr]
    rw [hP_par_pos, htr_p, ← mul_assoc, hscale_eq]

/-- **Conditional proof of `RingAxisSmooth` (`PartII-a:R06`)** from the four 1D heat-expansion
remainder sub-claims (`MeanDatumRemainderMixedFixed`, `MeanSourceFarBoundFixed`,
`MeanSourceNearDiffBoundFixed`, `MeanSourceRemainderHeatStep`). -/
theorem ringAxisSmooth_of
    (hDatum : MeanDatumRemainderMixedFixed)
    (hFar : MeanSourceFarBoundFixed)
    (hNear : MeanSourceNearDiffBoundFixed)
    (hStep : MeanSourceRemainderHeatStep) :
    RingAxisSmooth :=
  ringAxisSmooth_of_heatFixed
    (PartI.trainHeatFixed_of trainFluctFixed
      (trainMeanRemFixed_of (trainMeanRemMixedFixed_of hDatum hFar hNear hStep)))
    trainPressureFixed

end UnforcedLeray.Short.PartIIa

