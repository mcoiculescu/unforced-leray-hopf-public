import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-b, task `PartII-b:G4/3/6/1/6`: fixed-band jets of `v - V_c`

Source of record: `the November 2 reference manuscript` 468-478 (`sct:fixed-band`),
255-258 (polynomial convention).  `TrainFixedBand` with `ρ = 2`, `m = 0`, `L = ℓ`, `k = j`, the
pointwise bound from the weighted sup norm, the exact rescaling `∂_s^ℓ = ν^ℓ ∂_σ^ℓ` (no smoothness
needed: `deriv_comp_mul_left`, `ContinuousLinearEquiv.iteratedFDeriv_comp_left`), and
`exp(C_Σ/ν - b_Σ c²) ≤ 1` for small `ν`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI

theorem iteratedDeriv_scale_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : ℝ}
    (g : ℝ → E) (n : ℕ) :
    iteratedDeriv n (fun σ => g (σ / ν)) = fun σ => (ν⁻¹) ^ n • iteratedDeriv n g (σ / ν) := by
  induction n with
  | zero => funext σ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext σ
    rw [deriv_fun_const_smul_field, iteratedDeriv_succ]
    have : (fun σ => iteratedDeriv n g (σ / ν)) = fun σ => iteratedDeriv n g (ν⁻¹ * σ) := by
      funext σ; rw [div_eq_inv_mul]
    rw [this, deriv_comp_mul_left (c := ν⁻¹) (f := iteratedDeriv n g) (x := σ)]
    rw [pow_succ, mul_smul, ← div_eq_inv_mul]

theorem iteratedFDeriv_smul_of_ne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℝ} (ha : a ≠ 0) (f : E → F) (j : ℕ) (z : E) :
    iteratedFDeriv ℝ j (fun w => a • f w) z = a • iteratedFDeriv ℝ j f z := by
  have h := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := f) (x := z) (i := j)
    (ContinuousLinearEquiv.smulLeft (M₁ := F) (R₁ := ℝ) (Units.mk0 a ha))
  ext m
  have := congrArg (fun T => T m) h
  exact this

theorem ageJet_eq_smul_sigmaJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : ℝ}
    (hν : 0 < ν) (ℓ j : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ageJet ℓ j F s z = ν ^ ℓ • sigmaJet ν ℓ j F s z := by
  unfold ageJet sigmaJet UnforcedLeray.Train.jet
  have hs : ∀ w : UnforcedLeray.Cyl.Plane, iteratedDeriv ℓ (fun σ => F (σ / ν) w) (ν * s) =
      (ν⁻¹) ^ ℓ • iteratedDeriv ℓ (fun r => F r w) s := by
    intro w
    rw [iteratedDeriv_scale_div (fun r => F r w) ℓ]
    simp [mul_div_cancel_left₀ _ hν.ne']
  have hf : (fun w => iteratedDeriv ℓ (fun r => F r w) s) =
      fun w => ν ^ ℓ • iteratedDeriv ℓ (fun σ => F (σ / ν) w) (ν * s) := by
    funext w
    rw [hs w, smul_smul, ← mul_pow, mul_inv_cancel₀ hν.ne']; simp
  rw [hf, iteratedFDeriv_smul_of_ne (pow_ne_zero _ hν.ne')]

theorem fixedBandJets_of (hF : UnforcedLeray.Short.PartI.TrainFixedBand) :
    UnforcedLeray.Short.IIb.FixedBandJets := by
  intro Sig hSig ℓ j
  obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, H⟩ := hF 2 (by norm_num) Sig hSig 0 ℓ j
  refine ⟨C * 3 ^ N, 2 * N, min ν₀ (min 1 (bS / (|CS| + 1))), by positivity,
    lt_min hν₀ (lt_min one_pos (by positivity)), ?_⟩
  intro ν hν hνle tr htr s hs hsS z
  have hν0 : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνb : ν ≤ bS / (|CS| + 1) := hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcdef : trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
    unfold trainPeriod
    rw [Real.rpow_neg hν.le]; norm_num
  have h1 := H ν hν hν0 tr htr s hs hsS
  simp only at h1
  -- exponential factor
  have hexp : CS / ν - bS * (trainPeriod 2 ν) ^ 2 ≤ 0 := by
    rw [hcdef, inv_pow, sub_nonpos]
    have hA : 0 < |CS| + 1 := by positivity
    have h3 : ν ^ 3 ≤ ν := by
      have : ν ^ 3 = ν * ν ^ 2 := by ring
      rw [this]
      nlinarith [pow_pos hν 2, mul_pos hν hν]
    have : CS * ν ^ 3 ≤ bS := by
      have h4 : |CS| * ν ≤ bS := by
        have := mul_le_mul_of_nonneg_left hνb (abs_nonneg CS)
        have h5 : |CS| * (bS / (|CS| + 1)) ≤ bS := by
          rw [mul_div_assoc', div_le_iff₀ hA]; nlinarith [abs_nonneg CS]
        linarith
      calc CS * ν ^ 3 ≤ |CS| * ν ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |CS| * ν := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ ≤ bS := h4
    rw [div_le_iff₀ hν]
    have hν4 : 0 < (ν ^ 2) ^ 2 := by positivity
    have : bS * ((ν ^ 2) ^ 2)⁻¹ * ν = bS / ν ^ 3 := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hexp1 : Real.exp (CS / ν - bS * (trainPeriod 2 ν) ^ 2) ≤ 1 := Real.exp_le_one_iff.2 hexp
  have hP : 0 ≤ polyP C N ν (trainPeriod 2 ν) := by
    unfold polyP; rw [hcdef]; have : 0 < ν := hν; positivity
  have hsup : wSupNorm 0 (sigmaJet ν ℓ j (fun r w => tr.v r w - UnforcedLeray.Train.Vc ν (trainPeriod 2 ν) r w) s)
      ≤ ENNReal.ofReal (polyP C N ν (trainPeriod 2 ν)) := by
    have hl : wSupNorm 0 (sigmaJet ν ℓ j
        (fun r w => tr.v r w - UnforcedLeray.Train.Vc ν (trainPeriod 2 ν) r w) s) ≤
        ENNReal.ofReal (polyP C N ν (trainPeriod 2 ν) * Real.exp (CS / ν - bS * (trainPeriod 2 ν) ^ 2)) := by
      refine le_trans ?_ h1
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_range.2 (Nat.lt_succ_self ℓ)))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_range.2 (Nat.lt_succ_self j)))
      exact le_add_right (le_add_right (le_add_right (le_add_right le_add_self)))
    exact hl.trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hP hexp1))
  have hpt := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hP hsup z
  have hjap : UnforcedLeray.Train.jap 0 z = 1 := by simp [UnforcedLeray.Train.jap]
  rw [hjap] at hpt
  simp only [Real.sqrt_one, one_mul] at hpt
  rw [ageJet_eq_smul_sigmaJet hν, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hν]
  have hνl : ν ^ ℓ ≤ 1 := pow_le_one₀ hν.le hν1
  have hinv : (1 : ℝ) ≤ (ν ^ 2)⁻¹ := (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hν.le hν1)
  have hinv1 : ν⁻¹ ≤ (ν ^ 2)⁻¹ := by
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hbase : 1 + (trainPeriod 2 ν) + ν⁻¹ ≤ 3 * (ν ^ 2)⁻¹ := by rw [hcdef]; linarith
  have hb0 : 0 ≤ 1 + (trainPeriod 2 ν) + ν⁻¹ := by rw [hcdef]; have : 0 < ν := hν; positivity
  have hpoly : polyP C N ν (trainPeriod 2 ν) ≤ C * 3 ^ N * (ν ^ (2 * N))⁻¹ := by
    unfold polyP
    calc C * (1 + (trainPeriod 2 ν) + ν⁻¹) ^ N ≤ C * (3 * (ν ^ 2)⁻¹) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbase N) hC.le
      _ = C * 3 ^ N * (ν ^ (2 * N))⁻¹ := by
          rw [mul_pow, pow_mul, inv_pow]; ring
  have hn := norm_nonneg (sigmaJet ν ℓ j (fun r w => tr.v r w - UnforcedLeray.Train.Vc ν (trainPeriod 2 ν) r w) s z)
  calc ν ^ ℓ * ‖sigmaJet ν ℓ j (fun r w => tr.v r w - UnforcedLeray.Train.Vc ν (trainPeriod 2 ν) r w) s z‖
      ≤ 1 * polyP C N ν (trainPeriod 2 ν) := mul_le_mul hνl hpt hn zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hpoly

end UnforcedLeray.Short.IIb
