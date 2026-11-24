import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs.JetUnif
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.MeanStreamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemainderSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemPointwise
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Order-by-order `(ν, c)`-polynomial weighted joint-derivative bounds for train stream and remainder

In `RingBoundedDerivs` (`Short/PartII-a/StatementsRing.lean`), the threshold `ν₀` and polynomial
constants `(C, d)` are chosen after fixing the Cartesian derivative order `k : ℕ`. Consequently,
the already-proved Part I theorems `TrainFluctuationDecay` and `TrainMeanExpansion` (together with
`jointFromAgeJets` and `jointFromMixed1D`) directly supply:

1. `early_stream_wtd_jet_poly`: on `0 < y.1 ≤ 1`,
   `(1 + |y.2.2|) ^ m * ‖D^i Ψ(y)‖ ≤ polyConst C d ν (ν ^ (-ρ))`;
2. `late_heatRem_wtd_jet_poly`: on `1 ≤ y.1`,
   `(1 + |y.2.2|) ^ m * ‖D^i (heatRemainder ν (meanCoeff tr) N Ψ)(y)‖ ≤
     polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff ageJet)

/-! ### 1. Elementary weight and polynomial-majorant helpers -/

theorem one_add_abs_pow_le_two_mul_sq (m : ℕ) (η : ℝ) :
    (1 + |η|) ^ m ≤ 2 ^ m * (1 + η ^ 2) ^ m := by
  have h1 : 1 + |η| ≤ 2 * (1 + η ^ 2) := by
    nlinarith [sq_nonneg (|η| - 1), sq_abs η]
  calc (1 + |η|) ^ m ≤ (2 * (1 + η ^ 2)) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    _ = 2 ^ m * (1 + η ^ 2) ^ m := mul_pow _ _ _

theorem polyConst_nonneg_of {C : ℝ} (hC : 0 ≤ C) (d : ℕ) {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ polyConst C d ν c := by
  unfold polyConst
  have : 0 < ν⁻¹ := inv_pos.2 hν
  exact mul_nonneg hC (pow_nonneg (by linarith) d)

theorem polyConst_add_le {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (d1 d2 : ℕ)
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    polyConst C1 d1 ν c + polyConst C2 d2 ν c ≤
      polyConst (C1 + C2) (max d1 d2) ν c := by
  have h1 : polyConst C1 d1 ν c ≤ polyConst C1 (max d1 d2) ν c :=
    polyConst_mono hν hc le_rfl hC1 (le_max_left _ _)
  have h2 : polyConst C2 d2 ν c ≤ polyConst C2 (max d1 d2) ν c :=
    polyConst_mono hν hc le_rfl hC2 (le_max_right _ _)
  have h3 : polyConst C1 (max d1 d2) ν c + polyConst C2 (max d1 d2) ν c =
      polyConst (C1 + C2) (max d1 d2) ν c := by
    unfold polyConst; ring
  linarith

theorem polyConst_mul_eq (C1 C2 : ℝ) (d1 d2 : ℕ) (ν c : ℝ) :
    polyConst C1 d1 ν c * polyConst C2 d2 ν c =
      polyConst (C1 * C2) (d1 + d2) ν c := by
  unfold polyConst
  rw [pow_add]
  ring

/-! ### 2. Weighted age-jet and joint-jet bounds for the fluctuation `ψ - meanStream` -/

/-- Weighted age-jet bound for the stream fluctuation from `TrainFluctuationDecay`:
`(1 + |z.2|) ^ m * ‖ageJet ℓ j ψ̃ s z‖ ≤ polyConst C M ν (ν ^ (-ρ)) * exp(-κ ν s / c²)`. -/
theorem fluct_ageJet_wtd_poly (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (m ℓ j : ℕ) :
    ∃ (ν₀ C : ℝ) (M : ℕ) (κ : ℝ), 0 < ν₀ ∧ 0 ≤ C ∧ 0 < κ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : ℝ × ℝ,
            (1 + |z.2|) ^ m *
              ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤
                polyConst C M ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) := by
  obtain ⟨C0, M, κ, ν₀, hC0, hκ, hν₀, hbd⟩ := hFD ρ hρ (2 * m) ℓ j
  refine ⟨ν₀, 2 ^ m * C0, M, κ, hν₀, by positivity, hκ,
    fun ν hν hνle tr htr s hs z => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hw := ((hbd ν hν hνle tr htr s hs).1).2
  have hB0 : 0 ≤ polyConst C0 M ν (ν ^ (-ρ)) *
      Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) :=
    mul_nonneg (polyConst_nonneg_of hC0.le M hν hc) (Real.exp_pos _).le
  have hpt := pointwise_of_wSupNorm hB0 hw z
  rw [sqrt_jap_even] at hpt
  have hwt := one_add_abs_pow_le_two_mul_sq m z.2
  calc (1 + |z.2|) ^ m * ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖
      ≤ (2 ^ m * (1 + z.2 ^ 2) ^ m) *
          ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ :=
        mul_le_mul_of_nonneg_right hwt (norm_nonneg _)
    _ = 2 ^ m * ((1 + z.2 ^ 2) ^ m *
          ‖ageJet ℓ j (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖) := by ring
    _ ≤ 2 ^ m * (polyConst C0 M ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2))) :=
        mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = polyConst (2 ^ m * C0) M ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) := by
        unfold polyConst; ring

/-- At all positive ages `s > 0`, the weighted joint derivative `D^i(ψ - meanStream)` is bounded by
`polyConst C d ν (ν ^ (-ρ))`. -/
theorem early_fluct_wtd_jet_poly (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
            (1 + |y.2.2|) ^ m *
              ‖iteratedFDeriv ℝ i
                (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨K, hK0, hKj⟩ := UnforcedLeray.Short.PartI.jointFromAgeJets i
  have hex : ∀ ℓ : ℕ, ∃ (ν₀ C : ℝ) (M : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : ℝ × ℝ,
            (1 + |z.2|) ^ m *
              ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤
                polyConst C M ν (ν ^ (-ρ)) := by
    intro ℓ
    obtain ⟨ν₀, C, M, κ, hν₀, hC0, hκ, hbd⟩ := fluct_ageJet_wtd_poly hFD hρ m ℓ (i - ℓ)
    refine ⟨ν₀, C, M, hν₀, hC0, fun ν hν hνle tr htr s hs z => ?_⟩
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
    have hexp_le : Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κ * ν * s / (ν ^ (-ρ)) ^ 2 := by positivity
      linarith
    calc (1 + |z.2|) ^ m * ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖
        ≤ polyConst C M ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) :=
          hbd ν hν hνle tr htr s hs z
      _ ≤ polyConst C M ν (ν ^ (-ρ)) * 1 :=
          mul_le_mul_of_nonneg_left hexp_le (polyConst_nonneg_of hC0 M hν hc)
      _ = polyConst C M ν (ν ^ (-ρ)) := mul_one _
  choose νf Cf Mf hνf hCf hbd using hex
  set R := Finset.range (i + 1)
  have hSν : 0 ≤ ∑ ℓ ∈ R, 1 / νf ℓ :=
    Finset.sum_nonneg fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le
  set ν₀ := 1 / (1 + ∑ ℓ ∈ R, 1 / νf ℓ)
  set d := ∑ ℓ ∈ R, Mf ℓ
  set C := K * ∑ ℓ ∈ R, Cf ℓ
  refine ⟨ν₀, C, d, inv_one_add_pos hSν,
    mul_nonneg hK0 (Finset.sum_nonneg fun ℓ _ => hCf ℓ), fun ν hν hνle tr htr y hy0 => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc tr htr
  have hmn : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (UnforcedLeray.Short.PartI.trainMeanEquations_proof ν _ hν hc tr htr).1
  have hF : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) U :=
    hψ.sub (hmn.comp L.contDiff.contDiffOn hLmaps)
  have hmain := hKj (fun r w => tr.ψ r w - meanStream tr r w.2) hF y hy0
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hterm : ∀ ℓ ∈ R,
      (1 + |y.2.2|) ^ m *
        ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖ ≤
        polyConst (Cf ℓ) d ν (ν ^ (-ρ)) := by
    intro ℓ hℓ
    have hν_ℓ : ν ≤ νf ℓ :=
      hνle.trans (inv_one_add_le (hνf ℓ)
        (Finset.single_le_sum (f := fun ℓ => 1 / νf ℓ)
          (fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le) hℓ))
    have hM_ℓ : Mf ℓ ≤ d :=
      Finset.single_le_sum (f := Mf) (fun _ _ => Nat.zero_le _) hℓ
    exact (hbd ℓ ν hν hν_ℓ tr htr y.1 hy0 y.2).trans
      (polyConst_mono hν hc le_rfl (hCf ℓ) hM_ℓ)
  calc (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖) :=
        mul_le_mul_of_nonneg_left hmain hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2.2|) ^ m *
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, polyConst (Cf ℓ) d ν (ν ^ (-ρ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hK0
    _ = polyConst C d ν (ν ^ (-ρ)) := by
        dsimp [C]
        unfold polyConst
        rw [← Finset.sum_mul]
        ring

/-- For `1 ≤ y.1`, the weighted joint derivative `D^i(ψ - meanStream)` is bounded by
`polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)`. -/
theorem late_fluct_wtd_jet_poly (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (N m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
            (1 + |y.2.2|) ^ m *
              ‖iteratedFDeriv ℝ i
                (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
  obtain ⟨K, hK0, hKj⟩ := UnforcedLeray.Short.PartI.jointFromAgeJets i
  have hex : ∀ ℓ : ℕ, ∃ (ν₀ C : ℝ) (M : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 1 ≤ s → ∀ z : ℝ × ℝ,
            (1 + |z.2|) ^ m *
              ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖ ≤
                polyConst C M ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    intro ℓ
    obtain ⟨ν₀, C1, M1, κ, hν₀, hC1, hκ, hbd⟩ := fluct_ageJet_wtd_poly hFD hρ m ℓ (i - ℓ)
    obtain ⟨C2, M2, hC2, habs⟩ := expPowAbsorb κ (N + 2) hκ
    refine ⟨ν₀, C1 * C2, M1 + M2, hν₀, mul_nonneg hC1 hC2, fun ν hν hνle tr htr s hs z => ?_⟩
    have hs0 : 0 < s := by linarith
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
    have h1 := hbd ν hν hνle tr htr s hs0 z
    have h2 := habs ν (ν ^ (-ρ)) s hν hc hs0.le
    have hexp_le : Real.exp (-(κ / 2 * ν * s / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κ / 2 * ν * s / (ν ^ (-ρ)) ^ 2 := by positivity
      linarith
    have h2' : s ^ (N + 2) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) ≤
        polyConst C2 M2 ν (ν ^ (-ρ)) := by
      calc s ^ (N + 2) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2))
          ≤ polyConst C2 M2 ν (ν ^ (-ρ)) * Real.exp (-(κ / 2 * ν * s / (ν ^ (-ρ)) ^ 2)) := h2
        _ ≤ polyConst C2 M2 ν (ν ^ (-ρ)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le (polyConst_nonneg_of hC2 M2 hν hc)
        _ = polyConst C2 M2 ν (ν ^ (-ρ)) := mul_one _
    have hpow_le : (s ^ (N + 2))⁻¹ ≤ s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
      have heq : (s ^ (N + 2))⁻¹ = s ^ (-((N + 2 : ℕ) : ℝ)) := by
        rw [Real.rpow_neg hs0.le, Real.rpow_natCast]
      rw [heq]
      refine Real.rpow_le_rpow_of_exponent_le hs ?_
      have : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
      push_cast
      linarith
    have hexp_pow : Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) ≤
        polyConst C2 M2 ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
      have hpos : 0 < s ^ (N + 2) := pow_pos hs0 _
      have hdiv : Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) ≤
          polyConst C2 M2 ν (ν ^ (-ρ)) * (s ^ (N + 2))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hpos]
        exact h2'
      exact hdiv.trans
        (mul_le_mul_of_nonneg_left hpow_le (polyConst_nonneg_of hC2 M2 hν hc))
    calc (1 + |z.2|) ^ m * ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) s z‖
        ≤ polyConst C1 M1 ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) := h1
      _ ≤ polyConst C1 M1 ν (ν ^ (-ρ)) *
            (polyConst C2 M2 ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2)) :=
          mul_le_mul_of_nonneg_left hexp_pow (polyConst_nonneg_of hC1 M1 hν hc)
      _ = (polyConst C1 M1 ν (ν ^ (-ρ)) * polyConst C2 M2 ν (ν ^ (-ρ))) *
            s ^ ((m : ℝ) / 2 - N - 3 / 2) := by ring
      _ = polyConst (C1 * C2) (M1 + M2) ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
          rw [polyConst_mul_eq]
  choose νf Cf Mf hνf hCf hbd using hex
  set R := Finset.range (i + 1)
  have hSν : 0 ≤ ∑ ℓ ∈ R, 1 / νf ℓ :=
    Finset.sum_nonneg fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le
  set ν₀ := 1 / (1 + ∑ ℓ ∈ R, 1 / νf ℓ)
  set d := ∑ ℓ ∈ R, Mf ℓ
  set C := K * ∑ ℓ ∈ R, Cf ℓ
  refine ⟨ν₀, C, d, inv_one_add_pos hSν,
    mul_nonneg hK0 (Finset.sum_nonneg fun ℓ _ => hCf ℓ), fun ν hν hνle tr htr y hy => ?_⟩
  have hy0 : 0 < y.1 := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc tr htr
  have hmn : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (UnforcedLeray.Short.PartI.trainMeanEquations_proof ν _ hν hc tr htr).1
  have hF : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) U :=
    hψ.sub (hmn.comp L.contDiff.contDiffOn hLmaps)
  have hmain := hKj (fun r w => tr.ψ r w - meanStream tr r w.2) hF y hy0
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hrpow0 : 0 ≤ y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := Real.rpow_nonneg hy0.le _
  have hterm : ∀ ℓ ∈ R,
      (1 + |y.2.2|) ^ m *
        ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖ ≤
        polyConst (Cf ℓ) d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    intro ℓ hℓ
    have hν_ℓ : ν ≤ νf ℓ :=
      hνle.trans (inv_one_add_le (hνf ℓ)
        (Finset.single_le_sum (f := fun ℓ => 1 / νf ℓ)
          (fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le) hℓ))
    have hM_ℓ : Mf ℓ ≤ d :=
      Finset.single_le_sum (f := Mf) (fun _ _ => Nat.zero_le _) hℓ
    exact (hbd ℓ ν hν hν_ℓ tr htr y.1 hy y.2).trans
      (mul_le_mul_of_nonneg_right (polyConst_mono hν hc le_rfl (hCf ℓ) hM_ℓ) hrpow0)
  calc (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖) :=
        mul_le_mul_of_nonneg_left hmain hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2.2|) ^ m *
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - meanStream tr r w.2) y.1 y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, polyConst (Cf ℓ) d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hK0
    _ = polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
        dsimp [C]
        unfold polyConst
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-! ### 3. Early-age (`0 < y.1 ≤ 1`) weighted joint-jet bounds for `meanStream` and `tr.ψ` -/

/-- On `0 < y.1 ≤ 1`, the weighted joint derivative `D^i (meanStream tr)` is bounded by
`polyConst C d ν (ν ^ (-ρ))`. -/
theorem early_mean_wtd_jet_poly (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × ℝ, 0 < y.1 → y.1 ≤ 1 →
            (1 + |y.2|) ^ m *
              ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanStream tr x.1 x.2) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) := by
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPt : MeanStreamPointwise :=
    meanStreamPointwise_of hME (meanStreamSmooth_of hS)
      (sliceDerivContinuous_of ageDerivSmooth) essSupPointwise
  obtain ⟨K, hK0, hKj⟩ := UnforcedLeray.Short.PartI.jointFromMixed1D i
  have hex : ∀ ℓ : ℕ, ∃ (ν₀ C : ℝ) (M : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ η : ℝ,
            (1 + |η|) ^ m *
              ‖iteratedDeriv (i - ℓ)
                (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η‖ ≤
                polyConst C M ν (ν ^ (-ρ)) := by
    intro ℓ
    obtain ⟨C0, M0, ν₀, hC0, hν₀, hbd⟩ := earlyMeanSlice_of hPt ρ m (i - ℓ) ℓ hρ
    refine ⟨ν₀, 2 ^ m * C0, M0, hν₀, by positivity, fun ν hν hνle tr htr s hs0 hs1 η => ?_⟩
    rw [Real.norm_eq_abs]
    have h1 := hbd ν hν hνle tr htr s hs0 hs1 η
    have hwt := one_add_abs_pow_le_two_mul_sq m η
    calc (1 + |η|) ^ m *
            |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η|
        ≤ (2 ^ m * (1 + η ^ 2) ^ m) *
            |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| :=
          mul_le_mul_of_nonneg_right hwt (abs_nonneg _)
      _ = 2 ^ m * ((1 + η ^ 2) ^ m *
            |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η|) := by
          ring
      _ ≤ 2 ^ m * polyConst C0 M0 ν (ν ^ (-ρ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = polyConst (2 ^ m * C0) M0 ν (ν ^ (-ρ)) := by
          unfold polyConst; ring
  choose νf Cf Mf hνf hCf hbd using hex
  set R := Finset.range (i + 1)
  have hSν : 0 ≤ ∑ ℓ ∈ R, 1 / νf ℓ :=
    Finset.sum_nonneg fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le
  set ν₀ := 1 / (1 + ∑ ℓ ∈ R, 1 / νf ℓ)
  set d := ∑ ℓ ∈ R, Mf ℓ
  set C := K * ∑ ℓ ∈ R, Cf ℓ
  refine ⟨ν₀, C, d, inv_one_add_pos hSν,
    mul_nonneg hK0 (Finset.sum_nonneg fun ℓ _ => hCf ℓ), fun ν hν hνle tr htr y hy0 hy1 => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hmn : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (UnforcedLeray.Short.PartI.trainMeanEquations_proof ν _ hν hc tr htr).1
  have hmain := hKj (fun r e => meanStream tr r e) hmn y hy0
  have hw0 : 0 ≤ (1 + |y.2|) ^ m := by positivity
  have hterm : ∀ ℓ ∈ R,
      (1 + |y.2|) ^ m *
        ‖iteratedDeriv (i - ℓ)
          (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) y.1) y.2‖ ≤
        polyConst (Cf ℓ) d ν (ν ^ (-ρ)) := by
    intro ℓ hℓ
    have hν_ℓ : ν ≤ νf ℓ :=
      hνle.trans (inv_one_add_le (hνf ℓ)
        (Finset.single_le_sum (f := fun ℓ => 1 / νf ℓ)
          (fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le) hℓ))
    have hM_ℓ : Mf ℓ ≤ d :=
      Finset.single_le_sum (f := Mf) (fun _ _ => Nat.zero_le _) hℓ
    exact (hbd ℓ ν hν hν_ℓ tr htr y.1 hy0 hy1 y.2).trans
      (polyConst_mono hν hc le_rfl (hCf ℓ) hM_ℓ)
  calc (1 + |y.2|) ^ m * ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanStream tr x.1 x.2) y‖
      ≤ (1 + |y.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) y.1) y.2‖) :=
        mul_le_mul_of_nonneg_left hmain hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2|) ^ m *
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) y.1) y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, polyConst (Cf ℓ) d ν (ν ^ (-ρ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hK0
    _ = polyConst C d ν (ν ^ (-ρ)) := by
        dsimp [C]
        unfold polyConst
        rw [← Finset.sum_mul]
        ring

/-- **Early-age (`0 < y.1 ≤ 1`) weighted joint-derivative polynomial bound for `tr.ψ`**. -/
theorem early_stream_wtd_jet_poly (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ 1 →
            (1 + |y.2.2|) ^ m *
              ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨ν1, C1, d1, hν1, hC1, h1⟩ := early_fluct_wtd_jet_poly hFD hρ m i
  obtain ⟨ν2, C2, d2, hν2, hC2, h2⟩ := early_mean_wtd_jet_poly hME hρ m i
  refine ⟨min ν1 ν2, C1 + C2, max d1 d2, lt_min hν1 hν2, add_nonneg hC1 hC2,
    fun ν hν hνle tr htr y hy0 hy1 => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [hL, one_mul, Prod.norm_def, Prod.norm_def]
    simp only [Prod.norm_def]
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans' (le_max_right _ _))
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hpre : L ⁻¹' U2 = U := by
    ext x
    simp only [hL, hUdef, hU2def, mem_preimage, mem_prod, mem_Ioi, mem_univ, and_true]
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc tr htr
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (UnforcedLeray.Short.PartI.trainMeanEquations_proof ν _ hν hc tr htr).1
  have hf1 : ContDiffOn ℝ ∞ ((fun x : ℝ × ℝ => meanStream tr x.1 x.2) ∘ L) U :=
    hmean.comp L.contDiff.contDiffOn (hpre ▸ subset_rfl : U ⊆ L ⁻¹' U2)
  have hf2 : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) U :=
    hψ.sub hf1
  have hsplit : (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) =
      ((fun x : ℝ × ℝ => meanStream tr x.1 x.2) ∘ L) +
        (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) := by
    funext x
    simp only [Pi.add_apply, Function.comp_apply, hL]
    ring
  have hyU : y ∈ U := by
    simp only [hUdef, mem_prod, mem_Ioi, mem_univ, and_true]; exact hy0
  have hyU2 : L y ∈ U2 := hLmaps hyU
  rw [hsplit, ← iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_add_apply
      ((hf1.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top))
      ((hf2.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)) hUo.uniqueDiffOn hyU]
  have hcomp := L.iteratedFDerivWithin_comp_right hmean hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2]
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hA : ‖(iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)).compContinuousLinearMap
        fun _ => L‖ ≤ ‖iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLnorm
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (le_of_eq (mul_one _))
  have hbd2 := h2 ν hν (hνle.trans (min_le_right _ _)) tr htr (L y) hy0 hy1
  simp only [hL] at hbd2
  have hbd1 := h1 ν hν (hνle.trans (min_le_left _ _)) tr htr y hy0
  have hsum := norm_add_le
    ((iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)).compContinuousLinearMap
      fun _ => L)
    (iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y)
  calc (1 + |y.2.2|) ^ m * ‖(iteratedFDeriv ℝ i
          (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)).compContinuousLinearMap (fun _ => L) +
        iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (‖iteratedFDeriv ℝ i
          (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)‖ +
        ‖iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖) :=
        mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hA le_rfl)) hw0
    _ = (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (L y)‖ +
        (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ :=
        mul_add _ _ _
    _ ≤ polyConst C2 d2 ν (ν ^ (-ρ)) + polyConst C1 d1 ν (ν ^ (-ρ)) :=
        add_le_add (by simpa [hL] using hbd2) hbd1
    _ = polyConst C1 d1 ν (ν ^ (-ρ)) + polyConst C2 d2 ν (ν ^ (-ρ)) := add_comm _ _
    _ ≤ polyConst (C1 + C2) (max d1 d2) ν (ν ^ (-ρ)) :=
        polyConst_add_le hC1 hC2 d1 d2 hν hc

/-! ### 4. Late-age (`1 ≤ y.1`) weighted joint-jet bounds for `meanRemainder` and `heatRemainder` -/

/-- On `1 ≤ y.1`, the weighted joint derivative `D^i (meanRemainder tr N)` is bounded by
`polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)`. -/
theorem late_meanRem_wtd_jet_poly (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (N m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × ℝ, 1 ≤ y.1 →
            (1 + |y.2|) ^ m *
              ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
  have hSm : MeanRemainderSmooth :=
    meanRemainderSmooth_of UnforcedLeray.Short.PartI.trainMeanEquations_proof heatKernelIterSmooth
  have hPt : MeanRemPointwise :=
    meanRemPointwise_of hME hSm (sliceDerivContinuous_of ageDerivSmooth) essSupPointwise
  obtain ⟨K, hK0, hKj⟩ := UnforcedLeray.Short.PartI.jointFromMixed1D i
  have hex : ∀ ℓ : ℕ, ∃ (ν₀ C : ℝ) (M : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
            (1 + |η|) ^ m *
              ‖iteratedDeriv (i - ℓ)
                (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η‖ ≤
                polyConst C M ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    intro ℓ
    obtain ⟨CA, MA, νA, hνA, HA⟩ := hPt ρ N 0 (i - ℓ) ℓ hρ
    obtain ⟨CB, MB, νB, hνB, HB⟩ := hPt ρ N m (i - ℓ) ℓ hρ
    refine ⟨min νA νB, 2 ^ m * (max CA 0 + max CB 0), max MA MB, lt_min hνA hνB,
      by positivity, fun ν hν hνle tr htr s hs η => ?_⟩
    have hs0 : 0 < s := by linarith
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
    rw [Real.norm_eq_abs]
    set D := |iteratedDeriv (i - ℓ) (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η|
    have hD0 : 0 ≤ D := abs_nonneg _
    have hA := HA ν hν (hνle.trans (min_le_left _ _)) tr htr s hs η
    have hB := HB ν hν (hνle.trans (min_le_right _ _)) tr htr s hs η
    have hpA : s ^ ((((0 : ℕ) : ℝ) - ((i - ℓ : ℕ) : ℝ) - 2 * N - 3) / 2 - ℓ) ≤
        s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le hs ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((i - ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      push_cast; linarith
    have hpB : s ^ ((((m : ℕ) : ℝ) - ((i - ℓ : ℕ) : ℝ) - 2 * N - 3) / 2 - ℓ) ≤
        s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le hs ?_
      have : (0 : ℝ) ≤ ((i - ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      linarith
    have hPA_le : polyConst CA MA ν (ν ^ (-ρ)) ≤ polyConst (max CA 0) (max MA MB) ν (ν ^ (-ρ)) :=
      polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
    have hPB_le : polyConst CB MB ν (ν ^ (-ρ)) ≤ polyConst (max CB 0) (max MA MB) ν (ν ^ (-ρ)) :=
      polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
    have tA : |η| ^ 0 * D ≤
        polyConst (max CA 0) (max MA MB) ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) :=
      hA.trans (mul_le_mul hPA_le hpA (Real.rpow_nonneg hs0.le _)
        (polyConst_nonneg_of (le_max_right _ _) _ hν hc))
    have tB : |η| ^ m * D ≤
        polyConst (max CB 0) (max MA MB) ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) :=
      hB.trans (mul_le_mul hPB_le hpB (Real.rpow_nonneg hs0.le _)
        (polyConst_nonneg_of (le_max_right _ _) _ hν hc))
    have hpow := pow_one_add_le m (abs_nonneg η)
    calc (1 + |η|) ^ m * D
        ≤ (2 ^ m * (1 + |η| ^ m)) * D := mul_le_mul_of_nonneg_right hpow hD0
      _ = 2 ^ m * (|η| ^ 0 * D + |η| ^ m * D) := by ring
      _ ≤ 2 ^ m * (polyConst (max CA 0) (max MA MB) ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2) +
            polyConst (max CB 0) (max MA MB) ν (ν ^ (-ρ)) * s ^ ((m : ℝ) / 2 - N - 3 / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add tA tB) (by positivity)
      _ = polyConst (2 ^ m * (max CA 0 + max CB 0)) (max MA MB) ν (ν ^ (-ρ)) *
            s ^ ((m : ℝ) / 2 - N - 3 / 2) := by
          unfold polyConst; ring
  choose νf Cf Mf hνf hCf hbd using hex
  set R := Finset.range (i + 1)
  have hSν : 0 ≤ ∑ ℓ ∈ R, 1 / νf ℓ :=
    Finset.sum_nonneg fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le
  set ν₀ := 1 / (1 + ∑ ℓ ∈ R, 1 / νf ℓ)
  set d := ∑ ℓ ∈ R, Mf ℓ
  set C := K * ∑ ℓ ∈ R, Cf ℓ
  refine ⟨ν₀, C, d, inv_one_add_pos hSν,
    mul_nonneg hK0 (Finset.sum_nonneg fun ℓ _ => hCf ℓ), fun ν hν hνle tr htr y hy => ?_⟩
  have hy0 : 0 < y.1 := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hΦ1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hSm ν (ν ^ (-ρ)) hν hc tr htr N
  have hmain := hKj (fun r e => meanRemainder tr N r e) hΦ1 y hy0
  have hw0 : 0 ≤ (1 + |y.2|) ^ m := by positivity
  have hrpow0 : 0 ≤ y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := Real.rpow_nonneg hy0.le _
  have hterm : ∀ ℓ ∈ R,
      (1 + |y.2|) ^ m *
        ‖iteratedDeriv (i - ℓ)
          (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖ ≤
        polyConst (Cf ℓ) d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
    intro ℓ hℓ
    have hν_ℓ : ν ≤ νf ℓ :=
      hνle.trans (inv_one_add_le (hνf ℓ)
        (Finset.single_le_sum (f := fun ℓ => 1 / νf ℓ)
          (fun ℓ _ => (one_div_pos.2 (hνf ℓ)).le) hℓ))
    have hM_ℓ : Mf ℓ ≤ d :=
      Finset.single_le_sum (f := Mf) (fun _ _ => Nat.zero_le _) hℓ
    exact (hbd ℓ ν hν hν_ℓ tr htr y.1 hy y.2).trans
      (mul_le_mul_of_nonneg_right (polyConst_mono hν hc le_rfl (hCf ℓ) hM_ℓ) hrpow0)
  calc (1 + |y.2|) ^ m * ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) y‖
      ≤ (1 + |y.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖) :=
        mul_le_mul_of_nonneg_left hmain hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2|) ^ m *
          ‖iteratedDeriv (i - ℓ)
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) y.1) y.2‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, polyConst (Cf ℓ) d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hK0
    _ = polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
        dsimp [C]
        unfold polyConst
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- **Late-age (`1 ≤ y.1`) weighted joint-derivative polynomial bound for `heatRemainder`**. -/
theorem late_heatRem_wtd_jet_poly (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (N m i : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
            (1 + |y.2.2|) ^ m *
              ‖iteratedFDeriv ℝ i
                (UnforcedLeray.Short.IIb.heatRemainder ν (meanCoeff tr) N
                  (fun x => tr.ψ x.1 x.2)) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by
  obtain ⟨ν1, C1, d1, hν1, hC1, h1⟩ := late_fluct_wtd_jet_poly hFD hρ N m i
  obtain ⟨ν2, C2, d2, hν2, hC2, h2⟩ := late_meanRem_wtd_jet_poly hME hρ N m i
  have hSm : MeanRemainderSmooth :=
    meanRemainderSmooth_of UnforcedLeray.Short.PartI.trainMeanEquations_proof heatKernelIterSmooth
  refine ⟨min ν1 ν2, C1 + C2, max d1 d2, lt_min hν1 hν2, add_nonneg hC1 hC2,
    fun ν hν hνle tr htr y hy => ?_⟩
  have hy0 : 0 < y.1 := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [hL, one_mul, Prod.norm_def, Prod.norm_def]
    simp only [Prod.norm_def]
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans' (le_max_right _ _))
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hpre : L ⁻¹' U2 = U := by
    ext x
    simp only [hL, hUdef, hU2def, mem_preimage, mem_prod, mem_Ioi, mem_univ, and_true]
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc tr htr
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (UnforcedLeray.Short.PartI.trainMeanEquations_proof ν _ hν hc tr htr).1
  have hmeanL : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => meanStream tr x.1 x.2.2) U :=
    hmean.comp L.contDiff.contDiffOn hLmaps
  have hΦ1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) U2 :=
    hSm ν (ν ^ (-ρ)) hν hc tr htr N
  have hf1 : ContDiffOn ℝ ∞ ((fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) ∘ L) U :=
    hΦ1.comp L.contDiff.contDiffOn (hpre ▸ subset_rfl : U ⊆ L ⁻¹' U2)
  have hf2 : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) U :=
    hψ.sub hmeanL
  have hsplit : UnforcedLeray.Short.IIb.heatRemainder ν (meanCoeff tr) N (fun x => tr.ψ x.1 x.2) =
      ((fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) ∘ L) +
        (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) := by
    funext x
    simp only [UnforcedLeray.Short.IIb.heatRemainder, meanRemainder,
      UnforcedLeray.Short.IIb.heatTerm, Pi.add_apply, Function.comp_apply, hL]
    ring
  have hyU : y ∈ U := by
    simp only [hUdef, mem_prod, mem_Ioi, mem_univ, and_true]; exact hy0
  have hyU2 : L y ∈ U2 := hLmaps hyU
  rw [hsplit, ← iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_add_apply
      ((hf1.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top))
      ((hf2.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)) hUo.uniqueDiffOn hyU]
  have hcomp := L.iteratedFDerivWithin_comp_right hΦ1 hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2]
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hrpow0 : 0 ≤ y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := Real.rpow_nonneg hy0.le _
  have hA : ‖(iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap
        fun _ => L‖ ≤ ‖iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLnorm
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (le_of_eq (mul_one _))
  have hbd2 := h2 ν hν (hνle.trans (min_le_right _ _)) tr htr (L y) hy
  simp only [hL] at hbd2
  have hbd1 := h1 ν hν (hνle.trans (min_le_left _ _)) tr htr y hy
  have hsum := norm_add_le
    ((iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap
      fun _ => L)
    (iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y)
  calc (1 + |y.2.2|) ^ m * ‖(iteratedFDeriv ℝ i
          (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)).compContinuousLinearMap (fun _ => L) +
        iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (‖iteratedFDeriv ℝ i
          (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ +
        ‖iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖) :=
        mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hA le_rfl)) hw0
    _ = (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (L y)‖ +
        (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖ :=
        mul_add _ _ _
    _ ≤ polyConst C2 d2 ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) +
          polyConst C1 d1 ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
        add_le_add (by simpa [hL] using hbd2) hbd1
    _ = (polyConst C1 d1 ν (ν ^ (-ρ)) + polyConst C2 d2 ν (ν ^ (-ρ))) *
          y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) := by ring
    _ ≤ polyConst (C1 + C2) (max d1 d2) ν (ν ^ (-ρ)) * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2) :=
        mul_le_mul_of_nonneg_right (polyConst_add_le hC1 hC2 d1 d2 hν hc) hrpow0

end UnforcedLeray.Short.PartIIa
