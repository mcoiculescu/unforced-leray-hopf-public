import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2

/-!
# `weightedTrainMeanRemMixedFixed` from Duhamel, stress decay, moments and a generic heat remainder

Source `the November 2 reference manuscript`
455-458 (weights `eta^m`, `p = infinity`), proof 527-551: the mean stream solves
`S_s - nu S_etaeta = g` (SP 397-404), hence is given by Duhamel's formula (SP 410-412, 541);
Taylor-expand `G_{nu s}(eta - xi)` through order `2N+1` (evenness removes odd terms), jointly in
`(xi, t)` for `t <= s/2`; for `t >= s/2` transfer derivatives to the exponentially decreasing source.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI

/-- Duhamel solution of `S_s - nu S_etaeta = g` with datum `S0` (SP 410-412, 541). -/
def genDuhamel (ν : ℝ) (S0 : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (s η : ℝ) : ℝ :=
  (∫ ξ : ℝ, heatKernel1 (ν * s) (η - ξ) * S0 ξ) +
    ∫ t in (0 : ℝ)..s, ∫ ξ : ℝ, heatKernel1 (ν * (s - t)) (η - ξ) * g t ξ

/-- The coefficient `a_{2j}` of `sct:expansion` (SP 450-453) for datum `S0` and source `g`
(same expression as `PartI.meanCoeff`). -/
def genCoeff (ν : ℝ) (S0 : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (j : ℕ) : ℝ :=
  (∫ η : ℝ, η ^ (2 * j) * S0 η) / ((2 * j).factorial : ℝ) +
    ∫ t in Ioi (0 : ℝ), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      ((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
        ∫ η : ℝ, η ^ (2 * kl.1) * g t η

/-- The remainder `R_N` of the Duhamel solution (SP 448-449). -/
def genRemainder (ν : ℝ) (S0 : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (N : ℕ) (s η : ℝ) : ℝ :=
  genDuhamel ν S0 g s η -
    ∑ j ∈ Finset.range (N + 1), genCoeff ν S0 g j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

/-- **Source leaf 1: Duhamel representation of the mean stream** (SP 397-404 `S_s - nu S_etaeta = g`,
SP 410-412 and 541: "In the source Duhamel integral"; bounded solution of the heat equation with
the mean stress as source, `S(0)` and `g` having the moments of SP 543-545). -/
def MeanStreamDuhamel : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → ∀ η : ℝ,
        meanStream tr s η = genDuhamel ν (meanStream tr 0) (meanStress tr) s η

/-- **Source leaf 2: the mean stress is smooth, even, and its weighted mixed jets decay
exponentially in the age** (SP 399, 543-545, 548-549: `g = hmean (v_1 v_2)` is quadratic in the
fluctuations since `\\bar v_2 = 0`; `g = S_s - nu S_etaeta` is even because `S` is even; the weighted
fluctuation bounds of `sct:fluctuation` give `(1+|eta|)^k |partial_eta^b partial_t^l g| <= C e^{-kappa t}`
for `t > 0`). -/
def MeanStressWeightedDecay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) ∧
      (∀ t : ℝ, 0 < t → ∀ η : ℝ, meanStress tr t (-η) = meanStress tr t η) ∧
      ∀ k b ℓ : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
        (1 + |η|) ^ k *
            ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) t) η‖ ≤
          C * Real.exp (-(κ * t))

/-- **Source leaf 3: the weighted heat-Taylor remainder of a Duhamel solution** (SP 455-458 and
proof 527-551, generic in the data): for `nu > 0`, an even datum `S0` with all even moments finite
and a smooth even source `g` whose weighted mixed jets decay like `e^{-kappa t}`, the remainder
`R_N` of `genDuhamel ν S0 g` satisfies
`(1+|eta|)^m |partial_eta^b partial_s^l R_N| <= C s^{(m-b-2N-3)/2-l}` for `s >= 1`. -/
def HeatDuhamelWeightedRemainder : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (S0 : ℝ → ℝ) (g : ℝ → ℝ → ℝ),
    (∀ η : ℝ, S0 (-η) = S0 η) →
    (∀ j : ℕ, Integrable (fun η : ℝ => η ^ (2 * j) * S0 η) volume) →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ) →
    (∀ t : ℝ, 0 < t → ∀ η : ℝ, g t (-η) = g t η) →
    (∀ k b ℓ : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
        (1 + |η|) ^ k * ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => g r e) t) η‖ ≤
          C * Real.exp (-(κ * t))) →
    ∀ N m b ℓ : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      (1 + |η|) ^ m *
          ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => genRemainder ν S0 g N r e) s) η‖ ≤
        C * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ)

theorem weightedTrainMeanRemMixedFixed_of (hD : MeanStreamDuhamel) (hG : MeanStressWeightedDecay)
    (hB0 : TrainMeanMomentsFixed) (hR : HeatDuhamelWeightedRemainder) :
    WeightedTrainMeanRemMixedFixed := by
  intro ρ hρ
  obtain ⟨ν1, h1, hD'⟩ := hD ρ hρ
  obtain ⟨ν2, h2, hG'⟩ := hG ρ hρ
  obtain ⟨ν3, h3, hB'⟩ := hB0 ρ hρ
  refine ⟨min ν1 (min ν2 ν3), lt_min h1 (lt_min h2 h3), fun ν hν hle tr htr N m b ℓ => ?_⟩
  have l1 : ν ≤ ν1 := hle.trans (min_le_left _ _)
  have l2 : ν ≤ ν2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have l3 : ν ≤ ν3 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsm, hge, hdec⟩ := hG' ν hν l2 tr htr
  have hB := hB' ν hν l3 tr htr
  obtain ⟨C, hC⟩ := hR ν hν (meanStream tr 0) (meanStress tr) (hB.1 0 le_rfl)
    (fun j => (hB.2 j).1) hsm hge hdec N m b ℓ
  refine ⟨C, fun s hs η => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hrem : ∀ r e : ℝ, 0 < r → meanRemainder tr N r e = genRemainder ν (meanStream tr 0)
      (meanStress tr) N r e := by
    intro r e hr
    simp only [meanRemainder, genRemainder, meanCoeff, genCoeff]
    rw [hD' ν hν l1 tr htr r hr e]
  have hin : ∀ e : ℝ, iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s =
      iteratedDeriv ℓ (fun r => genRemainder ν (meanStream tr 0) (meanStress tr) N r e) s := by
    intro e
    refine Filter.EventuallyEq.iteratedDeriv_eq ℓ ?_
    filter_upwards [Ioi_mem_nhds hs0] with r hr using hrem r e hr
  have : (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) =
      fun e => iteratedDeriv ℓ (fun r => genRemainder ν (meanStream tr 0) (meanStress tr) N r e) s :=
    funext hin
  rw [this]
  exact hC s hs η

end UnforcedLeray.Short.PartIIIb.Concrete
