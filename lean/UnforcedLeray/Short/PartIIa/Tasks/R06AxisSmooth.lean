import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanDatumRemainderMixedFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceFarBoundFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceNearDiffBoundFixed
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.MeanSourceRemainderHeatStep
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.HeatExpansionLift
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth.SpacetimeAxisExt
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.FluctProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!


Target: `RingAxisSmooth` (`Short/PartII-a/StatementsRing.lean`, line 206).
Source of record: `the November 2 reference manuscript`, lines 1214, 1305–1322.

## Architecture
1. `HeatExpansionLift.lean` constructs the explicit parity-form Cartesian velocity lifts
   `heatTermVel ν R a j` of the even-parity heat expansion terms `a_{2j} ∂_η^{2j} G_{νs}(η)` and
   the global velocity extension
   `ringSmoothVel ν R a₀ ψ z = heatTermVel ν R a₀ 0 z + liftVelocity R (ψ - a₀ * lhP ν 0) z.1 z.2`,
   proves that every `heatTermVel ν R a j` is `C^∞` on `{z : ℝ × Space | 0 < z.1}` (including
   `Axi.axis`), that `ringSmoothVel` agrees with `liftVelocity R ψ` off `Axi.axis`, and that for
   every truncation order `N : ℕ`, `ringSmoothVel` decomposes on all of `{t > 0}` into the finite
   heat sum up to `N`, the remainder velocity `liftVelocity R (meanRemainder tr N)`, and the
   fluctuation velocity `liftVelocity R (ψ - meanStream tr)`.
2. `SpacetimeAxisExt.lean` proves the removable-axis-singularity theorems
   `contDiffOn_posTime_of_flat_bound` and `contDiffOn_posTime_of_poly_bound` on `{t > 0}`, together
   with off-axis `C^∞` regularity `contDiffOn_liftPressure_offAxis` and
   `contDiffOn_liftVelocity_offAxis`.
3. This file combines `HeatExpansionLift.lean`, `SpacetimeAxisExt.lean`, and the profile smoothness
   results from `PartI`/`R02` to reduce `RingAxisSmooth` to three local cylindrical-box derivative
   estimates on `localCylBox t₀ M`:
   - `FluctPressureBoxFlat`: exponential flatness near `r = 0` for `liftPressure R (trainProfile tr.p)`,
   - `FluctVelocityBoxFlat`: exponential flatness near `r = 0` for the fluctuation velocity lift,
   - `MeanRemainderVelocityBoxPoly`: `O(r)` vanishing near `r = 0` for derivatives of order `n ≤ N`
     of the order-`N` mean-remainder velocity lift.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream meanCoeff meanRemainder heatKernel1)

/-- **Leaf 1 (`FluctPressureBoxFlat`)**: On every bounded cylindrical box
`localCylBox t₀ M` (`t₀ / 2 < t < 2 t₀`, `|x₃| < M`, `0 < r < 1`), the `n`-th spacetime
derivative of the lifted train pressure `liftPressure R (trainProfile tr.p)` satisfies the
exponential flatness bound `C r^{-K} exp(-κ / r²)` (`s = r²/(4t) → 0`). -/
def FluctPressureBoxFlat : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))), IsBUCTrain tr →
      ∀ R : ℝ, 2 ≤ R → ∀ n : ℕ, ∀ t₀ M : ℝ, 0 < t₀ → 0 < M →
        ∃ (C : ℝ) (K : ℕ) (κ : ℝ), 0 < κ ∧
          ∀ z ∈ localCylBox t₀ M,
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ × Space => liftPressure R (trainProfile tr.p) z.1 z.2) z‖ ≤
              C / Axi.ϱ z.2 ^ K * Real.exp (-κ / Axi.ϱ z.2 ^ 2)

/-- **Leaf 2 (`FluctVelocityBoxFlat`)**: On every bounded cylindrical box
`localCylBox t₀ M`, the `n`-th spacetime derivative of the lifted fluctuation velocity
`liftVelocity R (trainProfile (ψ - meanStream tr))` satisfies the exponential flatness bound
`C r^{-K} exp(-κ / r²)`. -/
def FluctVelocityBoxFlat : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))), IsBUCTrain tr →
      ∀ R : ℝ, 2 ≤ R → ∀ n : ℕ, ∀ t₀ M : ℝ, 0 < t₀ → 0 < M →
        ∃ (C : ℝ) (K : ℕ) (κ : ℝ), 0 < κ ∧
          ∀ z ∈ localCylBox t₀ M,
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ × Space =>
                liftVelocity R
                  (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2) z.1 z.2) z‖ ≤
              C / Axi.ϱ z.2 ^ K * Real.exp (-κ / Axi.ϱ z.2 ^ 2)

/-- **Leaf 3 (`MeanRemainderVelocityBoxPoly`)**: On every bounded cylindrical box
`localCylBox t₀ M`, for every truncation order `N : ℕ` and derivative order `n ≤ N`, the `n`-th
spacetime derivative of the lifted mean-remainder velocity
`liftVelocity R (trainProfile (meanRemainder tr N))` is `O(r)` as `r = Axi.ϱ z.2 → 0`
(since `s^{(m-b-2N-3)/2-ℓ}` with `s = r²/(4t)` contributes `r^{2(N-n)+1} ≤ r` on `r < 1`). -/
def MeanRemainderVelocityBoxPoly : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))), IsBUCTrain tr →
      ∀ R : ℝ, 2 ≤ R → ∀ N : ℕ, ∀ n ≤ N, ∀ t₀ M : ℝ, 0 < t₀ → 0 < M →
        ∃ C : ℝ,
          ∀ z ∈ localCylBox t₀ M,
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ × Space =>
                liftVelocity R
                  (trainProfile fun s w => meanRemainder tr N s w.2) z.1 z.2) z‖ ≤
              C * Axi.ϱ z.2

/-- Joint profile smoothness of the order-`N` mean remainder `meanRemainder tr N` on `{0 < s}` for
any BUC train `tr`. -/
theorem contDiffOn_remProfile {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hb : IsBUCTrain tr) (N : ℕ) :
    ContDiffOn ℝ ∞ (trainProfile fun s (w : ℝ × ℝ) => meanRemainder tr N s w.2)
      {x : ProfilePoint | 0 < x.2.2} :=
  contDiffOn_trainProfile_of_eta
    (meanRemainderSmooth_of UnforcedLeray.Short.PartI.trainMeanEquations_proof
      heatKernelIterSmooth ν c hν hc tr hb N)

/-- **Reduction of `RingAxisSmooth` to the three local cylindrical-box derivative bounds.** -/
theorem ringAxisSmooth_of_box (hP : FluctPressureBoxFlat) (hF : FluctVelocityBoxFlat)
    (hR : MeanRemainderVelocityBoxPoly) : RingAxisSmooth := by
  intro ρ hρ
  rcases hP ρ hρ with ⟨ν₁, hν₁, hP₁⟩
  rcases hF ρ hρ with ⟨ν₂, hν₂, hF₂⟩
  rcases hR ρ hρ with ⟨ν₃, hν₃, hR₃⟩
  refine ⟨min (min ν₁ ν₂) ν₃, lt_min (lt_min hν₁ hν₂) hν₃, ?_⟩
  intro ν hν ψ p htr R hR2
  have hν_pos : 0 < ν := hν.1
  have hc_pos : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν_pos (-ρ)
  have hR_pos : 0 < R := by linarith
  have hν₁_mem : ν ∈ Ioo 0 ν₁ :=
    ⟨hν_pos, lt_of_lt_of_le hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hν₂_mem : ν ∈ Ioo 0 ν₂ :=
    ⟨hν_pos, lt_of_lt_of_le hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hν₃_mem : ν ∈ Ioo 0 ν₃ :=
    ⟨hν_pos, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  rcases htr with ⟨tr, hb, hψ_eq, hp_eq⟩
  refine ⟨ringSmoothVel ν R (meanCoeff tr 0) (trainProfile tr.ψ),
    ringSmoothPres R (trainProfile tr.p), ?_, ?_, ?_⟩
  · -- Smoothness of `ringSmoothVel` on `{z : ℝ × Space | 0 < z.1}`
    rw [contDiffOn_infty]
    intro k
    have hsum : ContDiffOn ℝ ∞
        (fun z : ℝ × Space => ∑ j ∈ Finset.range (k + 1), heatTermVel ν R (meanCoeff tr j) j z)
        posTime :=
      ContDiffOn.sum fun j _ => contDiffOn_heatTermVel hν_pos R (meanCoeff tr j) j
    have hfluct_prof : ContDiffOn ℝ ∞
        (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2)
        {x : ProfilePoint | 0 < x.2.2} :=
      fluctProfileSmooth_of hS UnforcedLeray.Short.PartI.hmeanContDiff ν (ν ^ (-ρ)) hν_pos hc_pos tr hb
    have hfluct : ContDiffOn ℝ ∞
        (fun z : ℝ × Space =>
          liftVelocity R (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2) z.1 z.2)
        posTime :=
      contDiffOn_posTime_of_flat_bound
        (fun z hz => liftVelocity_of_mem_axis R _ z.1 hz.2)
        (contDiffOn_liftVelocity_offAxis hR_pos.ne' hfluct_prof)
        (fun n t₀ M ht₀ hM => hF₂ ν hν₂_mem tr hb R hR2 n t₀ M ht₀ hM)
    have hrem_prof : ContDiffOn ℝ ∞
        (trainProfile fun s w => meanRemainder tr k s w.2)
        {x : ProfilePoint | 0 < x.2.2} :=
      contDiffOn_remProfile hν_pos hc_pos tr hb k
    have hrem : ContDiffOn ℝ k
        (fun z : ℝ × Space =>
          liftVelocity R (trainProfile fun s w => meanRemainder tr k s w.2) z.1 z.2)
        posTime :=
      contDiffOn_posTime_of_poly_bound
        (fun z hz => liftVelocity_of_mem_axis R _ z.1 hz.2)
        ((contDiffOn_liftVelocity_offAxis hR_pos.ne' hrem_prof).of_le (by exact_mod_cast le_top))
        (fun n hn t₀ M ht₀ hM => hR₃ ν hν₃_mem tr hb R hR2 k n hn t₀ M ht₀ hM)
    have htot : ContDiffOn ℝ k
        (fun z : ℝ × Space =>
          (∑ j ∈ Finset.range (k + 1), heatTermVel ν R (meanCoeff tr j) j z) +
            liftVelocity R (trainProfile fun s w => meanRemainder tr k s w.2) z.1 z.2 +
            liftVelocity R (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2) z.1 z.2)
        posTime :=
      ((hsum.of_le (by exact_mod_cast le_top)).add hrem).add
        (hfluct.of_le (by exact_mod_cast le_top))
    exact htot.congr fun z hz =>
      ringSmoothVel_decomp hν_pos hc_pos hR_pos tr hb hS
        UnforcedLeray.Short.PartI.trainMeanEquations_proof k hz
  · -- Smoothness of `ringSmoothPres` on `{z : ℝ × Space | 0 < z.1}`
    have hp_prof : ContDiffOn ℝ ∞ (trainProfile tr.p) {x : ProfilePoint | 0 < x.2.2} :=
      (hS ν (ν ^ (-ρ)) hν_pos hc_pos tr hb).2
    exact contDiffOn_posTime_of_flat_bound
      (fun z hz => liftPressure_of_mem_axis R (trainProfile tr.p) z.1 hz.2)
      (contDiffOn_liftPressure_offAxis hR_pos.ne' hp_prof)
      (fun n t₀ M ht₀ hM => hP₁ ν hν₁_mem tr hb R hR2 n t₀ M ht₀ hM)
  · -- Off-axis agreement with `liftVelocity R ψ` and `liftPressure R p`
    intro t ht x hx
    rw [hψ_eq, hp_eq]
    have hU : IsOpen {y : ProfilePoint | 0 < y.2.2} := isOpen_ageDomain
    have hψ_sm : ContDiffOn ℝ ∞ (trainProfile tr.ψ) {y : ProfilePoint | 0 < y.2.2} :=
      (hS ν (ν ^ (-ρ)) hν_pos hc_pos tr hb).1
    have hψ_d : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (trainProfile tr.ψ) y :=
      fun y hy => (hψ_sm.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    exact ⟨ringSmoothVel_eq_liftVelocity hR_pos (meanCoeff tr 0) hψ_d ht hx, rfl⟩

/-- **Unconditional proof of `RingAxisSmooth` (`PartII-a:R06`)** from the four 1D heat-expansion
remainder sub-claims (`MeanDatumRemainderMixedFixed`, `MeanSourceFarBoundFixed`,
`MeanSourceNearDiffBoundFixed`, `MeanSourceRemainderHeatStep`). -/
theorem ringAxisSmooth : RingAxisSmooth :=
  ringAxisSmooth_of
    meanDatumRemainderMixedFixed
    meanSourceFarBoundFixed
    meanSourceNearDiffBoundFixed
    meanSourceRemainderHeatStep

end UnforcedLeray.Short.PartIIa

