import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem fluct_polyP_bound (C : ℝ) (N : ℕ) (ν : ℝ) (hC : 0 ≤ C) (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-2 : ℝ)) ≤ C * 3 ^ N * ν⁻¹ ^ (2 * N) := by
  have ht : 1 ≤ ν⁻¹ := by nlinarith [inv_pos.2 hν0, mul_inv_cancel₀ hν0.ne']
  have hc : ν ^ (-2 : ℝ) = ν⁻¹ ^ 2 := by
    rw [Real.rpow_neg hν0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      inv_pow]
  unfold UnforcedLeray.Short.PartI.polyP
  rw [hc]
  have h3 : 1 + ν⁻¹ ^ 2 + ν⁻¹ ≤ 3 * (ν⁻¹ ^ 2) := by nlinarith
  have h4 : (1 + ν⁻¹ ^ 2 + ν⁻¹) ^ N ≤ (3 * (ν⁻¹ ^ 2)) ^ N :=
    pow_le_pow_left₀ (by positivity) h3 N
  have h5 : (3 * (ν⁻¹ ^ 2)) ^ N = 3 ^ N * ν⁻¹ ^ (2 * N) := by
    rw [mul_pow, ← pow_mul]
  calc C * (1 + ν⁻¹ ^ 2 + ν⁻¹) ^ N ≤ C * (3 * (ν⁻¹ ^ 2)) ^ N :=
        mul_le_mul_of_nonneg_left h4 hC
    _ = C * 3 ^ N * ν⁻¹ ^ (2 * N) := by rw [h5]; ring

theorem fluctJetWeighted_of (hfl : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    FluctJetWeighted := by
  intro k j
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, hbd⟩ := hfl 2 (by norm_num) (2 * k) 0 j
  refine ⟨C * 3 ^ N, 2 * N, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν tr htr s hs x
  have hν0 : 0 < ν := hν.1
  have hνν₀ : ν ≤ ν₀ := le_trans hν.2 (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  obtain ⟨-, ⟨-, hsup⟩, -⟩ := hbd ν hν0 hνν₀ tr htr s hs
  have hpoly0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
    unfold UnforcedLeray.Short.PartI.polyP
    have hinv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
    have : 0 ≤ 1 + UnforcedLeray.Short.PartI.trainPeriod 2 ν + ν⁻¹ := by
      have : 0 ≤ UnforcedLeray.Short.PartI.trainPeriod 2 ν := Real.rpow_nonneg hν0.le _
      linarith
    exact mul_nonneg hC.le (pow_nonneg this N)
  have hKnn : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg hpoly0 (Real.exp_pos _).le
  have hexp1 : Real.exp (-(κ * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hκ.le hν0.le) hs.le) (sq_nonneg _)
    linarith
  have hage : ∀ z : UnforcedLeray.Cyl.Plane,
      UnforcedLeray.Short.PartI.ageJet 0 j (fun r => UnforcedLeray.Short.PartI.hfluct
        (ν ^ (-2 : ℝ)) (tr.v r)) s z =
        iteratedFDeriv ℝ j (UnforcedLeray.Short.PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s)) z := by
    intro z
    simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero]
  have hle := le_trans (le_iSup (fun z : UnforcedLeray.Cyl.Plane =>
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap (2 * k) z)) *
        ‖UnforcedLeray.Short.PartI.ageJet 0 j (fun r => UnforcedLeray.Short.PartI.hfluct
          (ν ^ (-2 : ℝ)) (tr.v r)) s z‖ₑ) x) hsup
  rw [hage x, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hKnn] at hle
  have hsq : Real.sqrt (UnforcedLeray.Train.jap (2 * k) x) = (1 + x.2 ^ 2) ^ k := by
    unfold UnforcedLeray.Train.jap
    rw [pow_mul', Real.sqrt_sq (by positivity)]
  rw [hsq] at hle
  have hfinal := le_trans hle (mul_le_of_le_one_right hpoly0 hexp1)
  have hpoly := fluct_polyP_bound C N ν hC.le hν0 hν1
  exact le_trans hfinal hpoly

end UnforcedLeray.Short.IIIa
