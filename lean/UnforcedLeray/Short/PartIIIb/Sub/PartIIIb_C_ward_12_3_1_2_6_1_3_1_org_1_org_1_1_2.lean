import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

/-!
# `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/1/2`: `TrainMeanRemWtdFixed`, decomposed

Source `the November 2 reference manuscript`
455-458 (`sct:expansion` remainder, weights `eta^m`, `p = infinity`), proof 527-551, fixed
parameters 429-435.

The single source leaf is the weighted mixed remainder bound `WeightedTrainMeanRemMixedFixed`.
`trainMeanRemWtdFixed_of` is the calculus reduction through `JointFromMixed1D` (pointwise at `y`, so
the weight is a constant), using `s^{(m-b-2N-3)/2-l} <= s^{m/2-N-3/2}` for `s >= 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI UnforcedLeray.Short.IIb

/-- **Source leaf: weighted mixed mean remainder at fixed parameters** (SP 455-458 with weights
`eta^m` and `p = infinity`: `|eta^m d_eta^b d_s^l R_N| <= P s^{(m-b-2N-3)/2-l}`, `s >= 1`; proof
SP 527-551; fixed parameters SP 429-435). Weighted form of `PartI.TrainMeanRemMixedFixed`. -/
def WeightedTrainMeanRemMixedFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ N m b ℓ : ℕ, ∃ C : ℝ,
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        (1 + |η|) ^ m *
            ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η‖ ≤
          C * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ)

/-- The weighted joint-derivative form from the weighted mixed bounds. -/
theorem trainMeanRemWtdFixed_of (hM : TrainMeanEquations) (hH : HeatTermSmooth)
    (hJ : JointFromMixed1D) (hL : WeightedTrainMeanRemMixedFixed) : TrainMeanRemWtdFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, hL'⟩ := hL ρ hρ
  refine ⟨ν₀, hν₀, fun ν hν hle tr htr N m i => ?_⟩
  have hc0 : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
  have hex : ∀ ℓ : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      (1 + |η|) ^ m *
          ‖iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η‖ ≤
        C * s ^ ((((m : ℝ) - ((i - ℓ : ℕ) : ℝ)) - 2 * N - 3) / 2 - ℓ) :=
    fun ℓ => hL' ν hν hle tr htr N m (i - ℓ) ℓ
  choose Cf hbd using hex
  obtain ⟨K, hK0, hKj⟩ := hJ i
  set R := Finset.range (i + 1) with hR
  refine ⟨K * ∑ ℓ ∈ R, |Cf ℓ|, fun y hy => ?_⟩
  -- smoothness
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  let ι : ℝ × ℝ →L[ℝ] ℝ × (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hι : ∀ x, ι x = (x.1, (0, x.2)) := fun x => rfl
  have hιmaps : MapsTo ι U2 (Ioi 0 ×ˢ univ) := fun x hx => by
    simp only [hι, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hmn : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (hM ν _ hν hc0 tr htr).1
  have hheat : ∀ j : ℕ, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => heatTerm ν j (ι x)) U2 := fun j =>
    (hH ν hν j).comp ι.contDiff.contDiffOn hιmaps
  have hΦ1eq : (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) =
      fun x => meanStream tr x.1 x.2 -
        ∑ j ∈ Finset.range (N + 1), meanCoeff tr j * heatTerm ν j (ι x) := by
    funext x
    simp [meanRemainder, heatTerm, hι]
  have hΦ1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) U2 := by
    rw [hΦ1eq]
    exact hmn.sub (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hheat j))
  have hy0 : 0 < y.1 := by linarith
  have h1 := hKj (fun r e => meanRemainder tr N r e) hΦ1 y hy0
  have hw0 : 0 ≤ (1 + |y.2|) ^ m := by positivity
  have hexp : ∀ ℓ ∈ R, (1 + |y.2|) ^ m *
      ‖iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖
      ≤ |Cf ℓ| * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    intro ℓ _
    have a := hbd ℓ y.1 hy y.2
    have hp : y.1 ^ ((((m : ℝ) - ((i - ℓ : ℕ) : ℝ)) - 2 * N - 3) / 2 - ℓ) ≤
        y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le hy ?_
      have : (0:ℝ) ≤ ((i - ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have : (0:ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      linarith
    have hpos : 0 ≤ y.1 ^ ((((m : ℝ) - ((i - ℓ : ℕ) : ℝ)) - 2 * N - 3) / 2 - ℓ) :=
      Real.rpow_nonneg (by linarith) _
    calc _ ≤ Cf ℓ * y.1 ^ ((((m : ℝ) - ((i - ℓ : ℕ) : ℝ)) - 2 * N - 3) / 2 - ℓ) := a
      _ ≤ |Cf ℓ| * y.1 ^ ((((m : ℝ) - ((i - ℓ : ℕ) : ℝ)) - 2 * N - 3) / 2 - ℓ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  calc (1 + |y.2|) ^ m * ‖iteratedFDeriv ℝ i
          (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖
      ≤ (1 + |y.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖) :=
        mul_le_mul_of_nonneg_left h1 hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2|) ^ m *
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, |Cf ℓ| * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hexp) hK0
    _ = _ := by rw [← Finset.sum_mul]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
