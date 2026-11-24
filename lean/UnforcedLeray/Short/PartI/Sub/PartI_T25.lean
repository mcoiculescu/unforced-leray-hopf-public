import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof

/-!
# `PartI:T25` Sub-module: fixed-band comparison (`sct:fixed-band`)

Source of record: `the November 2 reference manuscript`, lines 468-478, 541-551.

This module provides:
1. Exact rescaling `sigmaJet ν ℓ j F s z = (ν⁻¹)^ℓ • ageJet ℓ j F s z` and the resulting scaling
   of `wCellL2` and `wSupNorm`.
2. Weight interpolation `wCellL2_interp_fixedBand` between doubled polynomial weight `2m` and
   unweighted `0`, together with `trainFixedBand_sigmaJet_of_ageJet` converting a `(2m)`-polynomial
   / `(0)`-exponential pair on `ageJet ℓ j` over `0 < s ≤ Sg / ν` into the `sigmaJet ν ℓ j`
   fixed-band estimate.
3. Conversion `polyPS_le_polyP_of_le_div_nu` from `polyPS C N ν c s` to `polyP` on `0 ≤ s ≤ Sg / ν`,
   and pointwise domination lemmas `wCellL2_le_of_pointwise`, `wSupNorm_le_of_pointwise`.
4. The base (`ℓ = 0`, `m = 0`) velocity fixed-band comparison `trainFixedBand_vel_zero_unweighted`
   derived directly from `trainComparison_proof` (`PartI:T10`) and `trainPeriodAsymptotics_proof`.
5. Single-order `ageJet` leaf propositions `TrainFixedBandVelAgeJet`, `TrainFixedBandVortAgeJet`,
   and `TrainFixedBandPressAgeJet`, and the full double-sum assembly `trainFixedBand_of` proving
   `TrainFixedBand` across `ℓ ≤ L` and `j ≤ k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)

namespace PartI_T25

/-! ### 1. Slow-time jet rescaling `sigmaJet` vs `ageJet` -/

theorem iteratedDeriv_scale_div_fixedBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : ℝ} (g : ℝ → E) (n : ℕ) :
    iteratedDeriv n (fun σ => g (σ / ν)) = fun σ => (ν⁻¹) ^ n • iteratedDeriv n g (σ / ν) := by
  induction n with
  | zero => funext σ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext σ
    rw [deriv_fun_const_smul_field, iteratedDeriv_succ]
    have hfun : (fun σ => iteratedDeriv n g (σ / ν)) = fun σ => iteratedDeriv n g (ν⁻¹ * σ) := by
      funext τ; rw [div_eq_inv_mul]
    rw [hfun, deriv_comp_mul_left (c := ν⁻¹) (f := iteratedDeriv n g) (x := σ)]
    rw [pow_succ, mul_smul, ← div_eq_inv_mul]

theorem iteratedFDeriv_smul_of_ne_fixedBand {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℝ} (ha : a ≠ 0) (f : E → F) (j : ℕ) (z : E) :
    iteratedFDeriv ℝ j (fun w => a • f w) z = a • iteratedFDeriv ℝ j f z := by
  have h := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := f) (x := z) (i := j)
    (ContinuousLinearEquiv.smulLeft (M₁ := F) (R₁ := ℝ) (Units.mk0 a ha))
  ext m
  exact congrArg (fun T => T m) h

theorem sigmaJet_eq_inv_pow_smul_ageJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : ℝ} (hν : 0 < ν) (ℓ j : ℕ) (F : ℝ → Plane → E) (s : ℝ) (z : Plane) :
    sigmaJet ν ℓ j F s z = (ν⁻¹) ^ ℓ • ageJet ℓ j F s z := by
  unfold sigmaJet ageJet jet
  have hs : (fun w : Plane => iteratedDeriv ℓ (fun σ => F (σ / ν) w) (ν * s)) =
      fun w : Plane => (ν⁻¹) ^ ℓ • iteratedDeriv ℓ (fun r => F r w) s := by
    funext w
    rw [iteratedDeriv_scale_div_fixedBand (fun r => F r w) ℓ]
    simp [mul_div_cancel_left₀ _ hν.ne']
  rw [hs, iteratedFDeriv_smul_of_ne_fixedBand (pow_ne_zero _ (inv_ne_zero hν.ne'))]

theorem wCellL2_const_smul_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (f : Plane → E) :
    wCellL2 c m (fun z => a • f z) = ENNReal.ofReal a * wCellL2 c m f := by
  unfold wCellL2
  have hfun : (fun z : Plane => Real.sqrt (jap m z) • a • f z) =
      a • fun z : Plane => Real.sqrt (jap m z) • f z := by
    funext z
    rw [Pi.smul_apply, smul_comm]
  rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal ha]

theorem wSupNorm_const_smul_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (f : Plane → E) :
    wSupNorm m (fun z => a • f z) = ENNReal.ofReal a * wSupNorm m f := by
  unfold wSupNorm
  rw [ENNReal.mul_iSup]
  congr 1
  funext z
  rw [enorm_smul, Real.enorm_eq_ofReal ha]
  ring

theorem wCellL2_sigmaJet_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : ℝ} (hν : 0 < ν) (c : ℝ) (m ℓ j : ℕ) (F : ℝ → Plane → E) (s : ℝ) :
    wCellL2 c m (sigmaJet ν ℓ j F s) =
      ENNReal.ofReal ((ν⁻¹) ^ ℓ) * wCellL2 c m (ageJet ℓ j F s) := by
  have hfun : sigmaJet ν ℓ j F s = fun z => (ν⁻¹) ^ ℓ • ageJet ℓ j F s z :=
    funext (sigmaJet_eq_inv_pow_smul_ageJet hν ℓ j F s)
  rw [hfun, wCellL2_const_smul_nonneg c m (by positivity)]

theorem wSupNorm_sigmaJet_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : ℝ} (hν : 0 < ν) (m ℓ j : ℕ) (F : ℝ → Plane → E) (s : ℝ) :
    wSupNorm m (sigmaJet ν ℓ j F s) =
      ENNReal.ofReal ((ν⁻¹) ^ ℓ) * wSupNorm m (ageJet ℓ j F s) := by
  have hfun : sigmaJet ν ℓ j F s = fun z => (ν⁻¹) ^ ℓ • ageJet ℓ j F s z :=
    funext (sigmaJet_eq_inv_pow_smul_ageJet hν ℓ j F s)
  rw [hfun, wSupNorm_const_smul_nonneg m (by positivity)]

/-! ### 2. Polynomial conversion on `0 ≤ s ≤ Sg / ν` and pointwise domination -/

/-- On `0 ≤ s ≤ Sg / ν` (`Sg ≥ 0`, `ν > 0`, `c ≥ 0`), `polyPS C N ν c s` is bounded by
`polyP (C * (1 + Sg) ^ N) (2 * N) ν c` since `1 + s ≤ (1 + Sg) (1 + c + ν⁻¹)`. -/
theorem polyPS_le_polyP_of_le_div_nu {C Sg ν c s : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hSg : 0 ≤ Sg) (hν : 0 < ν) (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hs : s ≤ Sg / ν) :
    polyPS C N ν c s ≤ polyP (C * (1 + Sg) ^ N) (2 * N) ν c := by
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have h1s : 1 + s ≤ (1 + Sg) * X := by
    have hs' : s ≤ Sg * ν⁻¹ := by rwa [div_eq_mul_inv] at hs
    dsimp [X]
    nlinarith [mul_nonneg hSg hc, mul_nonneg hSg hν_inv]
  have hprod : X * (1 + s) ≤ (1 + Sg) * X ^ 2 := by
    calc X * (1 + s)
        ≤ X * ((1 + Sg) * X) := mul_le_mul_of_nonneg_left h1s hX0
      _ = (1 + Sg) * X ^ 2 := by ring
  have hbase_nn : 0 ≤ X * (1 + s) := by
    have : 0 ≤ 1 + s := by linarith
    exact mul_nonneg hX0 this
  unfold polyPS polyP
  change C * (X * (1 + s)) ^ N ≤ C * (1 + Sg) ^ N * X ^ (2 * N)
  calc C * (X * (1 + s)) ^ N
      ≤ C * ((1 + Sg) * X ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hprod N) hC
    _ = C * (1 + Sg) ^ N * X ^ (2 * N) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- Pointwise norm domination lifts to `wCellL2 c m`. -/
theorem wCellL2_le_of_pointwise {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (f : Plane → E) (g : Plane → F)
    (hfg : ∀ z : Plane, ‖f z‖ ≤ K * ‖g z‖) :
    wCellL2 c m f ≤ ENNReal.ofReal K * wCellL2 c m g := by
  unfold wCellL2
  rw [← Real.enorm_eq_ofReal hK, ← eLpNorm_const_smul]
  refine eLpNorm_mono_enorm fun z => ?_
  rw [Pi.smul_apply, ← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hK,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (jap m z) * ‖f z‖
      ≤ Real.sqrt (jap m z) * (K * ‖g z‖) :=
        mul_le_mul_of_nonneg_left (hfg z) (Real.sqrt_nonneg _)
    _ = K * (Real.sqrt (jap m z) * ‖g z‖) := by ring

/-- Pointwise norm domination lifts to `wSupNorm m`. -/
theorem wSupNorm_le_of_pointwise {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (f : Plane → E) (g : Plane → F)
    (hfg : ∀ z : Plane, ‖f z‖ ≤ K * ‖g z‖) :
    wSupNorm m f ≤ ENNReal.ofReal K * wSupNorm m g := by
  unfold wSupNorm
  rw [ENNReal.mul_iSup]
  refine iSup_le fun z => ?_
  refine le_iSup_of_le z ?_
  rw [← mul_assoc, mul_comm (ENNReal.ofReal K), mul_assoc]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (hfg z)

/-! ### 3. Weight interpolation for `wCellL2` -/

@[simp]
private theorem jap_zero_eq_one (z : Plane) : jap 0 z = 1 := by
  simp [jap]

@[simp]
private theorem sqrt_jap_zero_eq_one (z : Plane) : Real.sqrt (jap 0 z) = 1 := by
  simp [jap]

private theorem jap_nonneg_fixedBand (m : ℕ) (z : Plane) : 0 ≤ jap m z := by
  unfold jap
  positivity

private theorem sqrt_jap_two_mul_fixedBand (m : ℕ) (z : Plane) :
    Real.sqrt (jap (2 * m) z) = (Real.sqrt (jap m z)) ^ 2 := by
  have h : jap (2 * m) z = (jap m z) ^ 2 := by
    unfold jap
    rw [mul_comm 2 m, pow_mul]
  rw [h, Real.sqrt_sq (jap_nonneg_fixedBand m z), Real.sq_sqrt (jap_nonneg_fixedBand m z)]

theorem wCellL2_zero_eq_cellL2_fixedBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : Plane → E) : wCellL2 c 0 f = cellL2 c f := by
  unfold wCellL2 cellL2
  simp

theorem wSupNorm_zero_jet_eq_supNormD_fixedBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (f : Plane → E) : wSupNorm 0 (jet j f) = B0277.supNormD j f := by
  unfold wSupNorm B0277.supNormD jet
  simp

private theorem wCellL2_rpow_two_fixedBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (k : ℕ) (f : Plane → E) :
    wCellL2 c k f ^ (2 : ℝ) =
      ∫⁻ z : Plane, ‖Real.sqrt (jap k z) • f z‖ₑ ^ (2 : ℝ) ∂(Cyl.cellμ c) := by
  unfold wCellL2
  exact eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero

/-- Weight interpolation for `wCellL2` between `2m` and `0` via level-set splitting. -/
theorem wCellL2_interp_fixedBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) (f : Plane → E) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h2m : wCellL2 c (2 * m) f ≤ ENNReal.ofReal A)
    (h0 : wCellL2 c 0 f ≤ ENNReal.ofReal B) :
    wCellL2 c m f ≤ ENNReal.ofReal (Real.sqrt (2 * A * B)) := by
  set R : ℝ := Real.sqrt (A / B)
  have hR : 0 < R := Real.sqrt_pos.2 (div_pos hA hB)
  set S : Set Plane := {z : Plane | Real.sqrt (jap m z) ≤ R}
  have hS : MeasurableSet S := by
    have hc : Continuous (fun z : Plane => Real.sqrt (jap m z)) := by
      unfold jap
      fun_prop
    exact (isClosed_Iic.preimage hc).measurableSet
  let μ := Cyl.cellμ c
  let gm : Plane → ℝ≥0∞ := fun z => ‖Real.sqrt (jap m z) • f z‖ₑ ^ (2 : ℝ)
  let g0 : Plane → ℝ≥0∞ := fun z => ‖Real.sqrt (jap 0 z) • f z‖ₑ ^ (2 : ℝ)
  let g2m : Plane → ℝ≥0∞ := fun z => ‖Real.sqrt (jap (2 * m) z) • f z‖ₑ ^ (2 : ℝ)
  have hsplit : ∫⁻ z, gm z ∂μ = (∫⁻ z in S, gm z ∂μ) + (∫⁻ z in Sᶜ, gm z ∂μ) :=
    (lintegral_add_compl gm hS).symm
  have hS_le : ∫⁻ z in S, gm z ∂μ ≤ ENNReal.ofReal (R ^ 2) * ∫⁻ z, g0 z ∂μ := by
    calc ∫⁻ z in S, gm z ∂μ
        ≤ ∫⁻ z in S, ENNReal.ofReal (R ^ 2) * g0 z ∂μ := by
          refine setLIntegral_mono' hS fun z hz => ?_
          have hz_le : Real.sqrt (jap m z) ≤ R := hz
          dsimp [gm, g0]
          rw [enorm_smul, enorm_smul, sqrt_jap_zero_eq_one,
            Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
            Real.enorm_eq_ofReal zero_le_one, ENNReal.ofReal_one, one_mul,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
            Real.rpow_two]
          gcongr
      _ ≤ ∫⁻ z, ENNReal.ofReal (R ^ 2) * g0 z ∂μ := setLIntegral_le_lintegral S _
      _ = ENNReal.ofReal (R ^ 2) * ∫⁻ z, g0 z ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hSc_le : ∫⁻ z in Sᶜ, gm z ∂μ ≤ ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ z, g2m z ∂μ := by
    calc ∫⁻ z in Sᶜ, gm z ∂μ
        ≤ ∫⁻ z in Sᶜ, ENNReal.ofReal (R⁻¹ ^ 2) * g2m z ∂μ := by
          refine setLIntegral_mono' hS.compl fun z hz => ?_
          have hz' : R < Real.sqrt (jap m z) := not_le.mp hz
          have hw : Real.sqrt (jap m z) ≤ R⁻¹ * Real.sqrt (jap (2 * m) z) := by
            rw [sqrt_jap_two_mul_fixedBand, sq]
            calc Real.sqrt (jap m z)
                = R⁻¹ * (R * Real.sqrt (jap m z)) := by field_simp
              _ ≤ R⁻¹ * (Real.sqrt (jap m z) * Real.sqrt (jap m z)) := by gcongr
          dsimp [gm, g2m]
          rw [enorm_smul, enorm_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
            Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
            Real.rpow_two, Real.rpow_two, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          gcongr
      _ ≤ ∫⁻ z, ENNReal.ofReal (R⁻¹ ^ 2) * g2m z ∂μ := setLIntegral_le_lintegral Sᶜ _
      _ = ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ z, g2m z ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h0_sq : ∫⁻ z, g0 z ∂μ ≤ ENNReal.ofReal (B ^ 2) := by
    rw [← wCellL2_rpow_two_fixedBand c 0 f]
    calc wCellL2 c 0 f ^ (2 : ℝ)
        ≤ ENNReal.ofReal B ^ (2 : ℝ) := ENNReal.rpow_le_rpow h0 (by norm_num)
      _ = ENNReal.ofReal (B ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num), Real.rpow_two]
  have h2m_sq : ∫⁻ z, g2m z ∂μ ≤ ENNReal.ofReal (A ^ 2) := by
    rw [← wCellL2_rpow_two_fixedBand c (2 * m) f]
    calc wCellL2 c (2 * m) f ^ (2 : ℝ)
        ≤ ENNReal.ofReal A ^ (2 : ℝ) := ENNReal.rpow_le_rpow h2m (by norm_num)
      _ = ENNReal.ofReal (A ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA.le (by norm_num), Real.rpow_two]
  have hsq : wCellL2 c m f ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * A * B) := by
    rw [wCellL2_rpow_two_fixedBand, hsplit]
    calc (∫⁻ z in S, gm z ∂μ) + (∫⁻ z in Sᶜ, gm z ∂μ)
        ≤ ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (B ^ 2) +
            ENNReal.ofReal (R⁻¹ ^ 2) * ENNReal.ofReal (A ^ 2) := by
          gcongr
          · exact hS_le.trans (by gcongr)
          · exact hSc_le.trans (by gcongr)
      _ = ENNReal.ofReal (R ^ 2 * B ^ 2 + R⁻¹ ^ 2 * A ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (2 * A * B) := by
          congr 1
          have hR2 : R ^ 2 = A / B := Real.sq_sqrt (div_nonneg hA.le hB.le)
          rw [inv_pow, hR2]
          field_simp
          ring
  calc wCellL2 c m f
      = (wCellL2 c m f ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel (by norm_num), ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal (2 * A * B) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (2 * A * B)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          Real.sqrt_eq_rpow]

/-! ### 4. Base (`ℓ = 0`, `m = 0`) velocity fixed-band comparison from `trainComparison_proof` -/

/-- On `0 < s ≤ Sg / ν`, `trainComparison_proof` directly yields the unweighted (`m = 0`, `ℓ = 0`)
fixed-band estimate for `dv = tr.v - Vc` with Gaussian factor `exp(-(b / (1 + Sg)) c²)`. -/
theorem trainFixedBand_vel_zero_unweighted (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg)
    (j : ℕ) :
    ∃ C bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            wCellL2 c 0 (ageJet 0 j dv s) ≤
                ENNReal.ofReal (polyP C 1 ν c * Real.exp (-(bS * c ^ 2))) ∧
            wSupNorm 0 (ageJet 0 j dv s) ≤
                ENNReal.ofReal (polyP C 1 ν c * Real.exp (-(bS * c ^ 2))) := by
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ j
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  refine ⟨Ce, be / (1 + Sg), min νe νp, hCe, div_pos hbe (by positivity), lt_min hνe hνp, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_p : ν ≤ νp := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hν_p.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_p
  have hw_ge1 : 1 ≤ width ν s := by
    unfold width
    linarith [mul_pos hν hs]
  have hw_le_Sg : width ν s ≤ 1 + Sg := by
    unfold width
    have hνs : ν * s ≤ Sg := by
      have := mul_le_mul_of_nonneg_left hs_le hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    linarith
  have hSg_le_c2 : 1 + Sg ≤ (trainPeriod ρ ν) ^ 2 := by
    calc 1 + Sg ≤ ν * (trainPeriod ρ ν) ^ 2 := hνc2
      _ ≤ 1 * (trainPeriod ρ ν) ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg _)
      _ = (trainPeriod ρ ν) ^ 2 := one_mul _
  have hw_le_c2 : width ν s ≤ (trainPeriod ρ ν) ^ 2 := hw_le_Sg.trans hSg_le_c2
  obtain ⟨hL2, hSup⟩ := hcomp ν hν hν_e tr htr s hs.le hw_le_c2
  have hj_nn : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrpow1 : width ν s ^ (-(2 + (j : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw_ge1 (by linarith)
  have hrpow2 : width ν s ^ (-((5 + (j : ℝ)) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw_ge1 (by linarith)
  have hexp : Real.exp (-(be * (trainPeriod ρ ν) ^ 2 / width ν s)) ≤
      Real.exp (-(be / (1 + Sg) * (trainPeriod ρ ν) ^ 2)) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hw_le_Sg
  have hpoly : Ce * ν⁻¹ ≤ polyP Ce 1 ν (trainPeriod ρ ν) := by
    unfold polyP
    rw [pow_one]
    have hc0 : 0 ≤ trainPeriod ρ ν := zero_le_one.trans hc1
    nlinarith [hCe.le]
  have hpoly_nn : 0 ≤ polyP Ce 1 ν (trainPeriod ρ ν) := by
    have hc0 : 0 ≤ trainPeriod ρ ν := zero_le_one.trans hc1
    unfold polyP
    positivity
  have hbound1 : Ce * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
        Real.exp (-(be * (trainPeriod ρ ν) ^ 2 / width ν s)) ≤
      polyP Ce 1 ν (trainPeriod ρ ν) * Real.exp (-(be / (1 + Sg) * (trainPeriod ρ ν) ^ 2)) := by
    have h1 : Ce * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) ≤ polyP Ce 1 ν (trainPeriod ρ ν) := by
      calc Ce * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2))
          ≤ Ce * ν⁻¹ * 1 := mul_le_mul_of_nonneg_left hrpow1 (by positivity)
        _ = Ce * ν⁻¹ := mul_one _
        _ ≤ polyP Ce 1 ν (trainPeriod ρ ν) := hpoly
    exact mul_le_mul h1 hexp (Real.exp_nonneg _) hpoly_nn
  have hbound2 : Ce * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
        Real.exp (-(be * (trainPeriod ρ ν) ^ 2 / width ν s)) ≤
      polyP Ce 1 ν (trainPeriod ρ ν) * Real.exp (-(be / (1 + Sg) * (trainPeriod ρ ν) ^ 2)) := by
    have h1 : Ce * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) ≤ polyP Ce 1 ν (trainPeriod ρ ν) := by
      calc Ce * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2))
          ≤ Ce * ν⁻¹ * 1 := mul_le_mul_of_nonneg_left hrpow2 (by positivity)
        _ = Ce * ν⁻¹ := mul_one _
        _ ≤ polyP Ce 1 ν (trainPeriod ρ ν) := hpoly
    exact mul_le_mul h1 hexp (Real.exp_nonneg _) hpoly_nn
  have hage : ageJet 0 j (fun r z => tr.v r z - Vc ν (trainPeriod ρ ν) r z) s =
      jet j (fun z => tr.v s z - Vc ν (trainPeriod ρ ν) s z) := rfl
  dsimp only
  rw [hage, wCellL2_zero_eq_cellL2_fixedBand, wSupNorm_zero_jet_eq_supNormD_fixedBand]
  exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hbound1),
    hSup.trans (ENNReal.ofReal_le_ofReal hbound2)⟩

/-- Interpolates the weight-`2m` polynomial bound and the weight-`0` exponential bound on
`ageJet ℓ j F s`, and rescales by `(ν⁻¹)^ℓ` to bound `sigmaJet ν ℓ j F s` in `wCellL2 c m + wSupNorm 0`. -/
theorem trainFixedBand_sigmaJet_of_ageJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ℝ} {N m ℓ j : ℕ} {CS bS ν c s : ℝ}
    (hC : 0 < C) (hbS : 0 < bS) (hν : 0 < ν) (hc : 0 ≤ c) (F : ℝ → Plane → E)
    (h2m : wCellL2 c (2 * m) (ageJet ℓ j F s) ≤ ENNReal.ofReal (polyP C N ν c))
    (h0 : wCellL2 c 0 (ageJet ℓ j F s) ≤
      ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)))
    (hsup : wSupNorm 0 (ageJet ℓ j F s) ≤
      ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))) :
    wCellL2 c m (sigmaJet ν ℓ j F s) + wSupNorm 0 (sigmaJet ν ℓ j F s) ≤
      ENNReal.ofReal (polyP (3 * C) (N + ℓ) ν c *
        Real.exp (max CS 0 / ν - (bS / 2) * c ^ 2)) := by
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv_nn : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX1 : 1 ≤ X := by
    dsimp [X]
    linarith
  have hνX : ν⁻¹ ≤ X := by
    dsimp [X]
    linarith
  have hν_pow_le : (ν⁻¹) ^ ℓ ≤ X ^ ℓ := pow_le_pow_left₀ hν_inv_nn hνX ℓ
  have hA_pos : 0 < polyP C N ν c := by
    unfold polyP
    positivity
  set E₀ : ℝ := Real.exp (CS / ν - bS * c ^ 2)
  have hE₀_pos : 0 < E₀ := Real.exp_pos _
  have hB_pos : 0 < polyP C N ν c * E₀ := mul_pos hA_pos hE₀_pos
  have hinterp : wCellL2 c m (ageJet ℓ j F s) ≤
      ENNReal.ofReal (Real.sqrt (2 * polyP C N ν c * (polyP C N ν c * E₀))) :=
    wCellL2_interp_fixedBand c m (ageJet ℓ j F s) hA_pos hB_pos h2m h0
  set E_out : ℝ := Real.exp (max CS 0 / ν - (bS / 2) * c ^ 2)
  have hE_out_pos : 0 < E_out := Real.exp_pos _
  have hE₀_le_sq : E₀ ≤ E_out ^ 2 := by
    dsimp [E₀, E_out]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hCS : CS ≤ max CS 0 := le_max_left _ _
    have hCS0 : 0 ≤ max CS 0 := le_max_right _ _
    have hdiv1 : CS / ν ≤ max CS 0 / ν := div_le_div_of_nonneg_right hCS hν.le
    have hdiv2 : 0 ≤ max CS 0 / ν := div_nonneg hCS0 hν.le
    linarith
  have hE₀_le_out : E₀ ≤ E_out := by
    dsimp [E₀, E_out]
    apply Real.exp_le_exp.2
    have hCS : CS ≤ max CS 0 := le_max_left _ _
    have hdiv : CS / ν ≤ max CS 0 / ν := div_le_div_of_nonneg_right hCS hν.le
    have hb : (bS / 2) * c ^ 2 ≤ bS * c ^ 2 := by
      nlinarith [sq_nonneg c, hbS.le]
    linarith
  have hsqrt_le : Real.sqrt (2 * polyP C N ν c * (polyP C N ν c * E₀)) ≤
      2 * C * X ^ N * E_out := by
    have hsq : 2 * polyP C N ν c * (polyP C N ν c * E₀) ≤ (2 * C * X ^ N * E_out) ^ 2 := by
      unfold polyP
      change 2 * (C * X ^ N) * (C * X ^ N * E₀) ≤ (2 * C * X ^ N * E_out) ^ 2
      calc 2 * (C * X ^ N) * (C * X ^ N * E₀)
          ≤ 4 * (C * X ^ N) ^ 2 * E₀ := by nlinarith [sq_nonneg (C * X ^ N), hE₀_pos.le]
        _ ≤ 4 * (C * X ^ N) ^ 2 * E_out ^ 2 := by gcongr
        _ = (2 * C * X ^ N * E_out) ^ 2 := by ring
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩
  have hL2_sigma : wCellL2 c m (sigmaJet ν ℓ j F s) ≤
      ENNReal.ofReal (2 * C * X ^ (N + ℓ) * E_out) := by
    rw [wCellL2_sigmaJet_eq hν]
    calc ENNReal.ofReal ((ν⁻¹) ^ ℓ) * wCellL2 c m (ageJet ℓ j F s)
        ≤ ENNReal.ofReal ((ν⁻¹) ^ ℓ) *
            ENNReal.ofReal (Real.sqrt (2 * polyP C N ν c * (polyP C N ν c * E₀))) := by gcongr
      _ = ENNReal.ofReal ((ν⁻¹) ^ ℓ *
            Real.sqrt (2 * polyP C N ν c * (polyP C N ν c * E₀))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (2 * C * X ^ (N + ℓ) * E_out) := by
          apply ENNReal.ofReal_le_ofReal
          calc (ν⁻¹) ^ ℓ * Real.sqrt (2 * polyP C N ν c * (polyP C N ν c * E₀))
              ≤ X ^ ℓ * (2 * C * X ^ N * E_out) :=
                mul_le_mul hν_pow_le hsqrt_le (Real.sqrt_nonneg _) (by positivity)
            _ = 2 * C * X ^ (N + ℓ) * E_out := by rw [pow_add]; ring
  have hSup_sigma : wSupNorm 0 (sigmaJet ν ℓ j F s) ≤
      ENNReal.ofReal (C * X ^ (N + ℓ) * E_out) := by
    rw [wSupNorm_sigmaJet_eq hν]
    calc ENNReal.ofReal ((ν⁻¹) ^ ℓ) * wSupNorm 0 (ageJet ℓ j F s)
        ≤ ENNReal.ofReal ((ν⁻¹) ^ ℓ) * ENNReal.ofReal (polyP C N ν c * E₀) := by gcongr
      _ = ENNReal.ofReal ((ν⁻¹) ^ ℓ * (polyP C N ν c * E₀)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C * X ^ (N + ℓ) * E_out) := by
          apply ENNReal.ofReal_le_ofReal
          unfold polyP
          change (ν⁻¹) ^ ℓ * (C * X ^ N * E₀) ≤ C * X ^ (N + ℓ) * E_out
          calc (ν⁻¹) ^ ℓ * (C * X ^ N * E₀)
              ≤ X ^ ℓ * (C * X ^ N * E_out) := by
                apply mul_le_mul hν_pow_le _ (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_left hE₀_le_out (by positivity)
            _ = C * X ^ (N + ℓ) * E_out := by rw [pow_add]; ring
  calc wCellL2 c m (sigmaJet ν ℓ j F s) + wSupNorm 0 (sigmaJet ν ℓ j F s)
      ≤ ENNReal.ofReal (2 * C * X ^ (N + ℓ) * E_out) +
          ENNReal.ofReal (C * X ^ (N + ℓ) * E_out) := add_le_add hL2_sigma hSup_sigma
    _ = ENNReal.ofReal (polyP (3 * C) (N + ℓ) ν c * E_out) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        unfold polyP
        change 2 * C * X ^ (N + ℓ) * E_out + C * X ^ (N + ℓ) * E_out =
          3 * C * X ^ (N + ℓ) * E_out
        ring

end PartI_T25

/-! ### 5. Single-order `ageJet` leaf propositions and conditional assembly `trainFixedBand_of` -/

/-- **Single-order fixed-band `ageJet` bounds for the velocity difference `dv = tr.v - Vc`
(`PartI:T25/1`):**
source lines 468-478, 541-551 of `the November 2 reference manuscript`.
For every `ρ > 1/2`, `Sg > 0`, and `m ℓ j : ℕ`, on `0 < s ≤ Sg / ν`, `ageJet ℓ j dv s` satisfies a
weight-`2m` polynomial bound and an unweighted (`m = 0`) exponential fixed-band bound. -/
def TrainFixedBandVelAgeJet : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ m ℓ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            wCellL2 c (2 * m) (ageJet ℓ j dv s) ≤ ENNReal.ofReal (polyP C N ν c) ∧
            wCellL2 c 0 (ageJet ℓ j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet ℓ j dv s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- **Single-order fixed-band `ageJet` bounds for the vorticity difference `dω = curl tr.v - curl Vc`
(`PartI:T25/2`):**
source lines 468-478, 541-551 of `the November 2 reference manuscript`.
For every `ρ > 1/2`, `Sg > 0`, and `m ℓ j : ℕ`, on `0 < s ≤ Sg / ν`, `ageJet ℓ j dω s` satisfies a
weight-`2m` polynomial bound and an unweighted (`m = 0`) exponential fixed-band bound. -/
def TrainFixedBandVortAgeJet : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ m ℓ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
            wCellL2 c (2 * m) (ageJet ℓ j dω s) ≤ ENNReal.ofReal (polyP C N ν c) ∧
            wCellL2 c 0 (ageJet ℓ j dω s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet ℓ j dω s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

/-- **Single-order fixed-band `ageJet` bounds for the pressure-gradient difference `dp = ∇(tr.p - pc)`
(`PartI:T25/3`):**
source lines 468-478, 541-551 of `the November 2 reference manuscript`.
For every `ρ > 1/2`, `Sg > 0`, and `m ℓ j : ℕ`, on `0 < s ≤ Sg / ν`, `ageJet ℓ j dp s` satisfies a
weight-`2m` polynomial bound and an unweighted (`m = 0`) exponential fixed-band bound. -/
def TrainFixedBandPressAgeJet : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ Sg : ℝ, 0 < Sg → ∀ m ℓ j : ℕ,
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dp : ℝ → Plane → Vec := fun r z =>
              Train.gradS (fun w => tr.p r w - pc ν c r w) z
            wCellL2 c (2 * m) (ageJet ℓ j dp s) ≤ ENNReal.ofReal (polyP C N ν c) ∧
            wCellL2 c 0 (ageJet ℓ j dp s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
            wSupNorm 0 (ageJet ℓ j dp s) ≤
              ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))

namespace PartI_T25

private theorem add_six_le_fixedBand {a1 b1 a2 b2 a3 b3 k : ℝ≥0∞}
    (h1 : a1 + b1 ≤ k) (h2 : a2 + b2 ≤ k) (h3 : a3 + b3 ≤ k) :
    a1 + b1 + a2 + b2 + a3 + b3 ≤ k + k + k := by
  have hassoc : a1 + b1 + a2 + b2 + a3 + b3 = (a1 + b1) + (a2 + b2) + (a3 + b3) := by
    simp only [add_assoc]
  rw [hassoc]
  exact add_le_add (add_le_add h1 h2) h3

/-- Single-(ℓ, j) combined `sigmaJet` bound for `(dv, dω, dp)` from the three `ageJet` leaf Props. -/
theorem trainFixedBand_single_order
    (hVel : TrainFixedBandVelAgeJet)
    (hVort : TrainFixedBandVortAgeJet)
    (hPress : TrainFixedBandPressAgeJet)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (m ℓ j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
            let dp : ℝ → Plane → Vec := fun r z =>
              Train.gradS (fun w => tr.p r w - pc ν c r w) z
            (wCellL2 c m (sigmaJet ν ℓ j dv s) + wSupNorm 0 (sigmaJet ν ℓ j dv s) +
             wCellL2 c m (sigmaJet ν ℓ j dω s) + wSupNorm 0 (sigmaJet ν ℓ j dω s) +
             wCellL2 c m (sigmaJet ν ℓ j dp s) + wSupNorm 0 (sigmaJet ν ℓ j dp s)) ≤
            ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
  obtain ⟨C₁, N₁, CS₁, b₁, ν₁, hC₁, hb₁, hν₁, h₁⟩ := hVel ρ hρ Sg hSg m ℓ j
  obtain ⟨C₂, N₂, CS₂, b₂, ν₂, hC₂, hb₂, hν₂, h₂⟩ := hVort ρ hρ Sg hSg m ℓ j
  obtain ⟨C₃, N₃, CS₃, b₃, ν₃, hC₃, hb₃, hν₃, h₃⟩ := hPress ρ hρ Sg hSg m ℓ j
  let C_max := max C₁ (max C₂ C₃)
  let N_max := max N₁ (max N₂ N₃) + ℓ
  let CS_max := max (max CS₁ 0) (max (max CS₂ 0) (max CS₃ 0))
  let b_min := min (b₁ / 2) (min (b₂ / 2) (b₃ / 2))
  have hC_max : 0 < C_max := lt_max_of_lt_left hC₁
  have hb_min : 0 < b_min := lt_min (half_pos hb₁) (lt_min (half_pos hb₂) (half_pos hb₃))
  refine ⟨9 * C_max, N_max, CS_max, b_min, min ν₁ (min ν₂ ν₃),
    by positivity, hb_min, lt_min hν₁ (lt_min hν₂ hν₃), ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₃_le : ν ≤ ν₃ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc0 : 0 ≤ trainPeriod ρ ν := by
    unfold trainPeriod
    exact Real.rpow_nonneg hν.le _
  have hX1 : 1 ≤ 1 + trainPeriod ρ ν + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  obtain ⟨h1_2m, h1_0, h1_sup⟩ := h₁ ν hν hν₁_le tr htr s hs hs_le
  obtain ⟨h2_2m, h2_0, h2_sup⟩ := h₂ ν hν hν₂_le tr htr s hs hs_le
  obtain ⟨h3_2m, h3_0, h3_sup⟩ := h₃ ν hν hν₃_le tr htr s hs hs_le
  let c := trainPeriod ρ ν
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
  let dp : ℝ → Plane → Vec := fun r z => Train.gradS (fun w => tr.p r w - pc ν c r w) z
  have hterm₁ := trainFixedBand_sigmaJet_of_ageJet hC₁ hb₁ hν hc0 dv h1_2m h1_0 h1_sup
  have hterm₂ := trainFixedBand_sigmaJet_of_ageJet hC₂ hb₂ hν hc0 dω h2_2m h2_0 h2_sup
  have hterm₃ := trainFixedBand_sigmaJet_of_ageJet hC₃ hb₃ hν hc0 dp h3_2m h3_0 h3_sup
  let E_out := Real.exp (CS_max / ν - b_min * c ^ 2)
  have hE_out_nn : 0 ≤ E_out := (Real.exp_pos _).le
  have hpoly₁ : polyP (3 * C₁) (N₁ + ℓ) ν c * Real.exp (max CS₁ 0 / ν - (b₁ / 2) * c ^ 2) ≤
      polyP (3 * C_max) N_max ν c * E_out := by
    apply mul_le_mul
    · unfold polyP
      have hC_le : 3 * C₁ ≤ 3 * C_max := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      have hN_le : N₁ + ℓ ≤ N_max := by omega
      exact mul_le_mul hC_le (pow_le_pow_right₀ hX1 hN_le) (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      have hCS_le : max CS₁ 0 / ν ≤ CS_max / ν :=
        div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      have hb_le : b_min * c ^ 2 ≤ (b₁ / 2) * c ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg c)
      linarith
    · exact (Real.exp_pos _).le
    · unfold polyP; positivity
  have hpoly₂ : polyP (3 * C₂) (N₂ + ℓ) ν c * Real.exp (max CS₂ 0 / ν - (b₂ / 2) * c ^ 2) ≤
      polyP (3 * C_max) N_max ν c * E_out := by
    apply mul_le_mul
    · unfold polyP
      have hC_le : 3 * C₂ ≤ 3 * C_max :=
        mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) (by norm_num)
      have hN_le : N₂ + ℓ ≤ N_max := by omega
      exact mul_le_mul hC_le (pow_le_pow_right₀ hX1 hN_le) (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      have hCS_le : max CS₂ 0 / ν ≤ CS_max / ν :=
        div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hν.le
      have hb_le : b_min * c ^ 2 ≤ (b₂ / 2) * c ^ 2 :=
        mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (sq_nonneg c)
      linarith
    · exact (Real.exp_pos _).le
    · unfold polyP; positivity
  have hpoly₃ : polyP (3 * C₃) (N₃ + ℓ) ν c * Real.exp (max CS₃ 0 / ν - (b₃ / 2) * c ^ 2) ≤
      polyP (3 * C_max) N_max ν c * E_out := by
    apply mul_le_mul
    · unfold polyP
      have hC_le : 3 * C₃ ≤ 3 * C_max :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) (by norm_num)
      have hN_le : N₃ + ℓ ≤ N_max := by omega
      exact mul_le_mul hC_le (pow_le_pow_right₀ hX1 hN_le) (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      have hCS_le : max CS₃ 0 / ν ≤ CS_max / ν :=
        div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hν.le
      have hb_le : b_min * c ^ 2 ≤ (b₃ / 2) * c ^ 2 :=
        mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (sq_nonneg c)
      linarith
    · exact (Real.exp_pos _).le
    · unfold polyP; positivity
  have h₁' := hterm₁.trans (ENNReal.ofReal_le_ofReal hpoly₁)
  have h₂' := hterm₂.trans (ENNReal.ofReal_le_ofReal hpoly₂)
  have h₃' := hterm₃.trans (ENNReal.ofReal_le_ofReal hpoly₃)
  let K3 := polyP (3 * C_max) N_max ν c * E_out
  have hK3_nn : 0 ≤ K3 := by
    dsimp [K3]
    unfold polyP
    positivity
  have hsum := add_six_le_fixedBand h₁' h₂' h₃'
  have hK3_eq : ENNReal.ofReal K3 + ENNReal.ofReal K3 + ENNReal.ofReal K3 =
      ENNReal.ofReal (polyP (9 * C_max) N_max ν c * E_out) := by
    rw [← ENNReal.ofReal_add hK3_nn hK3_nn, ← ENNReal.ofReal_add (by positivity) hK3_nn]
    congr 1
    dsimp [K3]
    unfold polyP
    ring
  exact hsum.trans_eq hK3_eq

/-- Inner `j`-sum assembly for fixed `ℓ`. -/
theorem trainFixedBand_sum_j
    (hVel : TrainFixedBandVelAgeJet)
    (hVort : TrainFixedBandVortAgeJet)
    (hPress : TrainFixedBandPressAgeJet)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (m ℓ k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
            let c := trainPeriod ρ ν
            let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
            let dω : ℝ → Plane → ℝ := fun r z => Cyl.curl (tr.v r) z - Cyl.curl (Vc ν c r) z
            let dp : ℝ → Plane → Vec := fun r z =>
              Train.gradS (fun w => tr.p r w - pc ν c r w) z
            ∑ j ∈ Finset.range (k + 1),
              (wCellL2 c m (sigmaJet ν ℓ j dv s) + wSupNorm 0 (sigmaJet ν ℓ j dv s) +
               wCellL2 c m (sigmaJet ν ℓ j dω s) + wSupNorm 0 (sigmaJet ν ℓ j dω s) +
               wCellL2 c m (sigmaJet ν ℓ j dp s) + wSupNorm 0 (sigmaJet ν ℓ j dp s)) ≤
            ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) := by
  induction k with
  | zero =>
    obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, h0⟩ :=
      trainFixedBand_single_order hVel hVort hPress ρ hρ Sg hSg m ℓ 0
    refine ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, fun ν hν hν_le tr htr s hs hs_le => ?_⟩
    dsimp only
    rw [Finset.range_one, Finset.sum_singleton]
    exact h0 ν hν hν_le tr htr s hs hs_le
  | succ k ih =>
    obtain ⟨C₁, N₁, CS₁, b₁, ν₁, hC₁, hb₁, hν₁, h₁⟩ := ih
    obtain ⟨C₂, N₂, CS₂, b₂, ν₂, hC₂, hb₂, hν₂, h₂⟩ :=
      trainFixedBand_single_order hVel hVort hPress ρ hρ Sg hSg m ℓ (k + 1)
    refine ⟨C₁ + C₂, max N₁ N₂, max CS₁ CS₂, min b₁ b₂, min ν₁ ν₂,
      add_pos hC₁ hC₂, lt_min hb₁ hb₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hs_le
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    have hc0 : 0 ≤ trainPeriod ρ ν := by
      unfold trainPeriod
      exact Real.rpow_nonneg hν.le _
    have hX1 : 1 ≤ 1 + trainPeriod ρ ν + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have h_ih := h₁ ν hν hν₁_le tr htr s hs hs_le
    have h_top := h₂ ν hν hν₂_le tr htr s hs hs_le
    dsimp only at h_ih h_top ⊢
    rw [Finset.sum_range_succ]
    set c := trainPeriod ρ ν
    set E_out := Real.exp (max CS₁ CS₂ / ν - min b₁ b₂ * c ^ 2)
    have hE₁ : Real.exp (CS₁ / ν - b₁ * c ^ 2) ≤ E_out := by
      apply Real.exp_le_exp.2
      have hCS : CS₁ / ν ≤ max CS₁ CS₂ / ν :=
        div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      have hb : min b₁ b₂ * c ^ 2 ≤ b₁ * c ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg c)
      linarith
    have hE₂ : Real.exp (CS₂ / ν - b₂ * c ^ 2) ≤ E_out := by
      apply Real.exp_le_exp.2
      have hCS : CS₂ / ν ≤ max CS₁ CS₂ / ν :=
        div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      have hb : min b₁ b₂ * c ^ 2 ≤ b₂ * c ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg c)
      linarith
    have hP₁ : polyP C₁ N₁ ν c * Real.exp (CS₁ / ν - b₁ * c ^ 2) ≤
        polyP C₁ (max N₁ N₂) ν c * E_out := by
      apply mul_le_mul _ hE₁ (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
    have hP₂ : polyP C₂ N₂ ν c * Real.exp (CS₂ / ν - b₂ * c ^ 2) ≤
        polyP C₂ (max N₁ N₂) ν c * E_out := by
      apply mul_le_mul _ hE₂ (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
    calc _ ≤ ENNReal.ofReal (polyP C₁ (max N₁ N₂) ν c * E_out) +
            ENNReal.ofReal (polyP C₂ (max N₁ N₂) ν c * E_out) :=
          add_le_add (h_ih.trans (ENNReal.ofReal_le_ofReal hP₁))
            (h_top.trans (ENNReal.ofReal_le_ofReal hP₂))
      _ = ENNReal.ofReal (polyP (C₁ + C₂) (max N₁ N₂) ν c * E_out) := by
          rw [← ENNReal.ofReal_add (by unfold polyP; positivity) (by unfold polyP; positivity)]
          congr 1
          unfold polyP
          ring

end PartI_T25

/-- **Conditional assembly of `TrainFixedBand` (`PartI:T25`)** across the double sum over
`ℓ ≤ L` and `j ≤ k` from the three single-order `ageJet` leaf propositions. -/
theorem trainFixedBand_of
    (_hTails : TrainStreamVelocityPressureTails)
    (_hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet)
    (hVort : TrainFixedBandVortAgeJet)
    (hPress : TrainFixedBandPressAgeJet) :
    TrainFixedBand := by
  intro ρ hρ Sg hSg m L k
  induction L with
  | zero =>
    obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, h0⟩ :=
      PartI_T25.trainFixedBand_sum_j hVel hVort hPress ρ hρ Sg hSg m 0 k
    refine ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, fun ν hν hν_le tr htr s hs hs_le => ?_⟩
    dsimp only
    rw [Finset.range_one, Finset.sum_singleton]
    exact h0 ν hν hν_le tr htr s hs hs_le
  | succ L ih =>
    obtain ⟨C₁, N₁, CS₁, b₁, ν₁, hC₁, hb₁, hν₁, h₁⟩ := ih
    obtain ⟨C₂, N₂, CS₂, b₂, ν₂, hC₂, hb₂, hν₂, h₂⟩ :=
      PartI_T25.trainFixedBand_sum_j hVel hVort hPress ρ hρ Sg hSg m (L + 1) k
    refine ⟨C₁ + C₂, max N₁ N₂, max CS₁ CS₂, min b₁ b₂, min ν₁ ν₂,
      add_pos hC₁ hC₂, lt_min hb₁ hb₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hs_le
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    have hc0 : 0 ≤ trainPeriod ρ ν := by
      unfold trainPeriod
      exact Real.rpow_nonneg hν.le _
    have hX1 : 1 ≤ 1 + trainPeriod ρ ν + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have h_ih := h₁ ν hν hν₁_le tr htr s hs hs_le
    have h_top := h₂ ν hν hν₂_le tr htr s hs hs_le
    dsimp only at h_ih h_top ⊢
    rw [Finset.sum_range_succ]
    set c := trainPeriod ρ ν
    set E_out := Real.exp (max CS₁ CS₂ / ν - min b₁ b₂ * c ^ 2)
    have hE₁ : Real.exp (CS₁ / ν - b₁ * c ^ 2) ≤ E_out := by
      apply Real.exp_le_exp.2
      have hCS : CS₁ / ν ≤ max CS₁ CS₂ / ν :=
        div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      have hb : min b₁ b₂ * c ^ 2 ≤ b₁ * c ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg c)
      linarith
    have hE₂ : Real.exp (CS₂ / ν - b₂ * c ^ 2) ≤ E_out := by
      apply Real.exp_le_exp.2
      have hCS : CS₂ / ν ≤ max CS₁ CS₂ / ν :=
        div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      have hb : min b₁ b₂ * c ^ 2 ≤ b₂ * c ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg c)
      linarith
    have hP₁ : polyP C₁ N₁ ν c * Real.exp (CS₁ / ν - b₁ * c ^ 2) ≤
        polyP C₁ (max N₁ N₂) ν c * E_out := by
      apply mul_le_mul _ hE₁ (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
    have hP₂ : polyP C₂ N₂ ν c * Real.exp (CS₂ / ν - b₂ * c ^ 2) ≤
        polyP C₂ (max N₁ N₂) ν c * E_out := by
      apply mul_le_mul _ hE₂ (Real.exp_pos _).le (by unfold polyP; positivity)
      unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
    calc _ ≤ ENNReal.ofReal (polyP C₁ (max N₁ N₂) ν c * E_out) +
            ENNReal.ofReal (polyP C₂ (max N₁ N₂) ν c * E_out) :=
          add_le_add (h_ih.trans (ENNReal.ofReal_le_ofReal hP₁))
            (h_top.trans (ENNReal.ofReal_le_ofReal hP₂))
      _ = ENNReal.ofReal (polyP (C₁ + C₂) (max N₁ N₂) ν c * E_out) := by
          rw [← ENNReal.ofReal_add (by unfold polyP; positivity) (by unfold polyP; positivity)]
          congr 1
          unfold polyP
          ring

end UnforcedLeray.Short.PartI
