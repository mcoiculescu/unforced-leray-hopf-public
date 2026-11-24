import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# `PartI:T22` (`Sub/PartI_T22.lean`): exponential fluctuation decay in all polynomial weights (`sct:fluctuation`)

Source of record: `the November 2 reference manuscript`, lines 439-446, 515-526.

This module proves:
1. Weight interpolation between doubled polynomial weight `2m` and unweighted `0` for both
   `wSupNorm` (`PartI_T22.wSupNorm_interp`) and `wCellL2` (`PartI_T22.wCellL2_interp`).
2. Pre-overlap (`0 < s ≤ s_c`) unweighted (`m = 0`) exponential decay for all `(ψ̃, ṽ, p)` and all
   mixed age/spatial jets `∂_s^ℓ D^j` from `TrainStreamVelocityPressureTails` (`hTails.2.2` at
   `m = 0`, using `ν s / c² ≤ 1` and `1 + s ≤ (1 + c + ν⁻¹)³`).
3. Polynomial-in-`(1 + s)` absorption into a quartered exponential decay rate `κ = lam / 4` with
   polynomial cost in `c, ν⁻¹` (`PartI_T22.polyPS_mul_exp_absorb`).
4. **Unconditional proof of the `ℓ = 0` velocity post-overlap unweighted fluctuation decay**
   (`trainPostOverlapVelZero_of : OverlapFluctuationDecay → TrainPostOverlapVelZero`), rescaling
   `U(T) = overlapField ν c tr.v T` from the unit cylinder to the period-`c` cell via
   `cellL2_jet_scaleField` and `jet_scaleField`.
5. Conditional assembly `trainFluctuationDecay_of` proving `TrainFluctuationDecay` from
   `TrainStreamVelocityPressureTails`, `OverlapFluctuationDecay`, and the two remaining post-overlap
   unweighted leaves:
   * `TrainPostOverlapStreamPressureZero` (`PartI:T22/1`, source lines 499-503, 515-522):
     post-overlap unweighted (`m = 0`, `ℓ = 0`) exponential decay for the stream fluctuation `ψ̃`
     and pressure `p` via horizontal mode stream inversion and the cylinder pressure kernel.
   * `TrainPostOverlapAgeDerivFromZero` (`PartI:T22/2`, source lines 523-526):
     post-overlap unweighted (`m = 0`) exponential decay for higher age derivatives `∂_s^ℓ D^j`
     of `(ψ̃, ṽ, p)` from the `ℓ = 0` bounds by finite induction on the differentiated equations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)

namespace PartI_T22

/-! ### 1. Algebraic identities for `jap` weights -/

@[simp]
theorem jap_zero (z : Plane) : jap 0 z = 1 := by
  simp [jap]

@[simp]
theorem sqrt_jap_zero (z : Plane) : Real.sqrt (jap 0 z) = 1 := by
  simp [jap]

theorem jap_nonneg (m : ℕ) (z : Plane) : 0 ≤ jap m z := by
  unfold jap
  positivity

theorem jap_two_mul (m : ℕ) (z : Plane) : jap (2 * m) z = (jap m z) ^ 2 := by
  unfold jap
  rw [mul_comm 2 m, pow_mul]

theorem sqrt_jap_two_mul (m : ℕ) (z : Plane) :
    Real.sqrt (jap (2 * m) z) = (Real.sqrt (jap m z)) ^ 2 := by
  rw [jap_two_mul, Real.sqrt_sq (jap_nonneg m z), Real.sq_sqrt (jap_nonneg m z)]

theorem wCellL2_zero_eq_cellL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : Plane → E) : wCellL2 c 0 f = cellL2 c f := by
  unfold wCellL2 cellL2
  simp

theorem wSupNorm_zero_jet_eq_supNormD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (f : Plane → E) : wSupNorm 0 (jet j f) = B0277.supNormD j f := by
  unfold wSupNorm B0277.supNormD jet
  simp

/-! ### 2. Weight interpolation for `wSupNorm` and `wCellL2` -/

/-- Weight interpolation for `wSupNorm`: the weight-`m` sup norm is bounded by `√(2 A B)` from
the weight-`2m` bound `A` and the weight-`0` bound `B`. -/
theorem wSupNorm_interp {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : Plane → E)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h2m : wSupNorm (2 * m) f ≤ ENNReal.ofReal A)
    (h0 : wSupNorm 0 f ≤ ENNReal.ofReal B) :
    wSupNorm m f ≤ ENNReal.ofReal (Real.sqrt (2 * A * B)) := by
  unfold wSupNorm
  apply iSup_le
  intro z
  set R : ℝ := Real.sqrt (A / B)
  have hR : 0 < R := Real.sqrt_pos.2 (div_pos hA hB)
  by_cases hz : Real.sqrt (jap m z) ≤ R
  · have h0z : ENNReal.ofReal (Real.sqrt (jap 0 z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
      (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 0 w)) * ‖f w‖ₑ) z).trans h0
    rw [sqrt_jap_zero, ENNReal.ofReal_one, one_mul] at h0z
    have hRle : ENNReal.ofReal (Real.sqrt (jap m z)) ≤ ENNReal.ofReal R :=
      ENNReal.ofReal_le_ofReal hz
    calc ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ
        ≤ ENNReal.ofReal R * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (R * B) := (ENNReal.ofReal_mul hR.le).symm
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * A * B)) := by
          apply ENNReal.ofReal_le_ofReal
          have hRB : (R * B) ^ 2 = A * B := by
            rw [mul_pow, Real.sq_sqrt (div_nonneg hA.le hB.le)]
            field_simp
          have hle : (R * B) ^ 2 ≤ (Real.sqrt (2 * A * B)) ^ 2 := by
            rw [hRB, Real.sq_sqrt (by positivity)]
            linarith [mul_pos hA hB]
          exact (abs_le_of_sq_le_sq' hle (Real.sqrt_nonneg _)).2
  · have hz' : R < Real.sqrt (jap m z) := not_le.mp hz
    have h2mz : ENNReal.ofReal (Real.sqrt (jap (2 * m) z)) * ‖f z‖ₑ ≤ ENNReal.ofReal A :=
      (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap (2 * m) w)) * ‖f w‖ₑ) z).trans h2m
    have hw : Real.sqrt (jap m z) ≤ R⁻¹ * Real.sqrt (jap (2 * m) z) := by
      rw [sqrt_jap_two_mul, sq]
      calc Real.sqrt (jap m z)
          = R⁻¹ * (R * Real.sqrt (jap m z)) := by field_simp
        _ ≤ R⁻¹ * (Real.sqrt (jap m z) * Real.sqrt (jap m z)) := by gcongr
    calc ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ
        ≤ ENNReal.ofReal (R⁻¹ * Real.sqrt (jap (2 * m) z)) * ‖f z‖ₑ := by gcongr
      _ = ENNReal.ofReal R⁻¹ * (ENNReal.ofReal (Real.sqrt (jap (2 * m) z)) * ‖f z‖ₑ) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hR.le), mul_assoc]
      _ ≤ ENNReal.ofReal R⁻¹ * ENNReal.ofReal A := by gcongr
      _ = ENNReal.ofReal (R⁻¹ * A) := (ENNReal.ofReal_mul (inv_nonneg.2 hR.le)).symm
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * A * B)) := by
          apply ENNReal.ofReal_le_ofReal
          have hRA : (R⁻¹ * A) ^ 2 = A * B := by
            rw [mul_pow, inv_pow, Real.sq_sqrt (div_nonneg hA.le hB.le)]
            field_simp
          have hle : (R⁻¹ * A) ^ 2 ≤ (Real.sqrt (2 * A * B)) ^ 2 := by
            rw [hRA, Real.sq_sqrt (by positivity)]
            linarith [mul_pos hA hB]
          exact (abs_le_of_sq_le_sq' hle (Real.sqrt_nonneg _)).2

private theorem wCellL2_rpow_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (k : ℕ) (f : Plane → E) :
    wCellL2 c k f ^ (2 : ℝ) =
      ∫⁻ z : Plane, ‖Real.sqrt (jap k z) • f z‖ₑ ^ (2 : ℝ) ∂(Cyl.cellμ c) := by
  unfold wCellL2
  exact eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero

/-- Weight interpolation for `wCellL2` via level-set splitting of the Lebesgue integral (requires
no measurability hypothesis on `f`). -/
theorem wCellL2_interp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
          have hz' : Real.sqrt (jap m z) ≤ R := hz
          dsimp [gm, g0]
          rw [enorm_smul, enorm_smul, sqrt_jap_zero, Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
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
            rw [sqrt_jap_two_mul, sq]
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
    rw [← wCellL2_rpow_two c 0 f]
    calc wCellL2 c 0 f ^ (2 : ℝ)
        ≤ ENNReal.ofReal B ^ (2 : ℝ) := ENNReal.rpow_le_rpow h0 (by norm_num)
      _ = ENNReal.ofReal (B ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num), Real.rpow_two]
  have h2m_sq : ∫⁻ z, g2m z ∂μ ≤ ENNReal.ofReal (A ^ 2) := by
    rw [← wCellL2_rpow_two c (2 * m) f]
    calc wCellL2 c (2 * m) f ^ (2 : ℝ)
        ≤ ENNReal.ofReal A ^ (2 : ℝ) := ENNReal.rpow_le_rpow h2m (by norm_num)
      _ = ENNReal.ofReal (A ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA.le (by norm_num), Real.rpow_two]
  have hsq : wCellL2 c m f ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * A * B) := by
    rw [wCellL2_rpow_two, hsplit]
    have h1 : ∫⁻ z in S, gm z ∂μ ≤ ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (B ^ 2) := by
      calc ∫⁻ z in S, gm z ∂μ
          ≤ ENNReal.ofReal (R ^ 2) * ∫⁻ z, g0 z ∂μ := hS_le
        _ ≤ ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (B ^ 2) := by gcongr
    have h2 : ∫⁻ z in Sᶜ, gm z ∂μ ≤ ENNReal.ofReal (R⁻¹ ^ 2) * ENNReal.ofReal (A ^ 2) := by
      calc ∫⁻ z in Sᶜ, gm z ∂μ
          ≤ ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ z, g2m z ∂μ := hSc_le
        _ ≤ ENNReal.ofReal (R⁻¹ ^ 2) * ENNReal.ofReal (A ^ 2) := by gcongr
    calc (∫⁻ z in S, gm z ∂μ) + (∫⁻ z in Sᶜ, gm z ∂μ)
        ≤ ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (B ^ 2) +
            ENNReal.ofReal (R⁻¹ ^ 2) * ENNReal.ofReal (A ^ 2) := add_le_add h1 h2
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
          ← Real.sqrt_eq_rpow]

/-! ### 3. Pre-overlap exponential bound and polynomial-in-age absorption -/

/-- For `0 ≤ s ≤ B0146.overlapAge ν c`, `polyPS C₀ N₀ ν c s` is bounded by
`polyP (C₀ * exp lam) (4 * N₀) ν c * exp (-(lam * ν * s / c²))` since `ν s / c² ≤ 1` and
`1 + s ≤ (1 + c + ν⁻¹)³`. -/
theorem polyPS_le_polyP_mul_exp_of_le_overlapAge {C₀ lam ν c s : ℝ} (N₀ : ℕ)
    (hC₀ : 0 ≤ C₀) (hlam : 0 ≤ lam) (hν : 0 < ν) (hc : 1 ≤ c) (hs0 : 0 ≤ s)
    (hs : s ≤ B0146.overlapAge ν c) :
    polyPS C₀ N₀ ν c s ≤
      polyP (C₀ * Real.exp lam) (4 * N₀) ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ X := by linarith
  have hνX : ν⁻¹ ≤ X := by linarith
  have hs_le : s ≤ c ^ 2 * ν⁻¹ := by
    unfold B0146.overlapAge at hs
    calc s ≤ (c ^ 2 - 1) / ν := hs
      _ ≤ c ^ 2 / ν := div_le_div_of_nonneg_right (by linarith) hν.le
      _ = c ^ 2 * ν⁻¹ := div_eq_mul_inv _ _
  have h1s : 1 + s ≤ X ^ 3 := by
    have hX_def : X = 1 + c + ν⁻¹ := rfl
    have hc2_pos : 0 ≤ c ^ 2 := sq_nonneg c
    have hc_mul : 0 ≤ c * ν⁻¹ := mul_nonneg hc0.le hν_inv
    have hν2_pos : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have hX3 : 1 + c ^ 2 * ν⁻¹ ≤ X ^ 3 := by
      rw [hX_def]
      nlinarith [sq_nonneg c, sq_nonneg (ν⁻¹), mul_nonneg hc2_pos hν_inv,
        mul_nonneg hc0.le hν2_pos]
    linarith
  have hX1s : X * (1 + s) ≤ X ^ 4 := by
    calc X * (1 + s) ≤ X * X ^ 3 := mul_le_mul_of_nonneg_left h1s (by positivity)
      _ = X ^ 4 := by ring
  have hpow : (X * (1 + s)) ^ N₀ ≤ X ^ (4 * N₀) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hX1s N₀
  have hu_le : lam * ν * s / c ^ 2 ≤ lam := by
    have hνs : ν * s ≤ c ^ 2 := by
      unfold B0146.overlapAge at hs
      have := (le_div_iff₀ hν).mp hs
      linarith
    calc lam * ν * s / c ^ 2
        = lam * ((ν * s) / c ^ 2) := by ring
      _ ≤ lam * (c ^ 2 / c ^ 2) := by
          gcongr
      _ = lam := by
          rw [div_self (pow_ne_zero 2 hc0.ne'), mul_one]
  have hexp : 1 ≤ Real.exp lam * Real.exp (-(lam * ν * s / c ^ 2)) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith
  unfold polyPS polyP
  calc C₀ * (X * (1 + s)) ^ N₀
      ≤ C₀ * X ^ (4 * N₀) := mul_le_mul_of_nonneg_left hpow hC₀
    _ ≤ C₀ * X ^ (4 * N₀) * (Real.exp lam * Real.exp (-(lam * ν * s / c ^ 2))) :=
        le_mul_of_one_le_right (by positivity) hexp
    _ = C₀ * Real.exp lam * X ^ (4 * N₀) * Real.exp (-(lam * ν * s / c ^ 2)) := by ring

/-- Absorbing the polynomial factor `(1 + s) ^ N₁` of `polyPS C₁ N₁ ν c s` into the exponential
`exp (-(lam * ν * s / c²))`: the geometric mean `√(2 A B)` is bounded by
`polyP C_out (2 * N₁ + N₂) ν c * exp (-((lam / 4) * ν * s / c²))`. -/
theorem polyPS_mul_exp_absorb {C₁ C₂ lam ν c s : ℝ} (N₁ N₂ : ℕ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hlam : 0 < lam) (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 ≤ s) :
    let A := polyPS C₁ N₁ ν c s
    let B := polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2))
    let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2)
    let C_out : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
    Real.sqrt (2 * A * B) ≤
      polyP C_out (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2)) := by
  intro A B K_abs C_out
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ X := by linarith
  have hνX : ν⁻¹ ≤ X := by linarith
  set u : ℝ := ν * s / c ^ 2
  have hu : 0 ≤ u := by positivity
  have hs_u : s = c ^ 2 * ν⁻¹ * u := by
    dsimp [u]
    field_simp
  have h1s : 1 + s ≤ X ^ 3 * (1 + u) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hmul : c ^ 2 * ν⁻¹ ≤ X ^ 3 := by
      calc c ^ 2 * ν⁻¹ ≤ X ^ 2 * X := mul_le_mul hc2 hνX hν_inv (by positivity)
        _ = X ^ 3 := by ring
    have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    calc 1 + s = 1 + (c ^ 2 * ν⁻¹) * u := by rw [hs_u]
      _ ≤ X ^ 3 + X ^ 3 * u := add_le_add hX3 (mul_le_mul_of_nonneg_right hmul hu)
      _ = X ^ 3 * (1 + u) := by ring
  have hX1s : (X * (1 + s)) ^ N₁ ≤ X ^ (4 * N₁) * (1 + u) ^ N₁ := by
    calc (X * (1 + s)) ^ N₁
        ≤ (X * (X ^ 3 * (1 + u))) ^ N₁ := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left h1s (by positivity)
      _ = (X ^ 4 * (1 + u)) ^ N₁ := by ring_nf
      _ = X ^ (4 * N₁) * (1 + u) ^ N₁ := by rw [mul_pow, ← pow_mul]
  have habs : (1 + u) ^ N₁ ≤ K_abs * Real.exp (lam / 2 * u) := by
    have h := Real.pow_div_factorial_le_exp (lam / 2 * (1 + u)) (by positivity) N₁
    have hf : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
    have hlp : 0 < (lam / 2) ^ N₁ := by positivity
    rw [div_le_iff₀ hf, mul_pow] at h
    have hexp_add : Real.exp (lam / 2 * (1 + u)) = Real.exp (lam / 2) * Real.exp (lam / 2 * u) := by
      rw [mul_add, mul_one, Real.exp_add]
    rw [hexp_add] at h
    dsimp [K_abs]
    calc (1 + u) ^ N₁
        = ((lam / 2) ^ N₁)⁻¹ * ((lam / 2) ^ N₁ * (1 + u) ^ N₁) := by field_simp
      _ ≤ ((lam / 2) ^ N₁)⁻¹ * (Real.exp (lam / 2) * Real.exp (lam / 2 * u) * N₁.factorial) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hlp.le)
      _ = (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2) *
            Real.exp (lam / 2 * u) := by ring
  have hX_pow : X ^ (4 * N₁) * X ^ N₂ ≤ X ^ (2 * (2 * N₁ + N₂)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hX1 (by omega)
  have hK_pos : 0 < K_abs := by
    dsimp [K_abs]
    positivity
  have hsq : 2 * A * B ≤
      (polyP C_out (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * u))) ^ 2 := by
    have hA_le : A ≤ C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u)) := by
      dsimp [A, polyPS]
      calc C₁ * (X * (1 + s)) ^ N₁
          ≤ C₁ * (X ^ (4 * N₁) * (1 + u) ^ N₁) :=
            mul_le_mul_of_nonneg_left hX1s hC₁.le
        _ = C₁ * X ^ (4 * N₁) * (1 + u) ^ N₁ := by ring
        _ ≤ C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u)) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
    have hB_pos : 0 ≤ B := by
      dsimp [B, polyP]
      positivity
    have hexp_comb : Real.exp (lam / 2 * u) * Real.exp (-(lam * u)) =
        (Real.exp (-((lam / 4) * u))) ^ 2 := by
      rw [← Real.exp_add, sq, ← Real.exp_add]
      congr 1
      ring
    have hB_eq : B = C₂ * X ^ N₂ * Real.exp (-(lam * u)) := by
      dsimp [B, polyP, X, u]
      ring
    calc 2 * A * B
        ≤ 2 * (C₁ * X ^ (4 * N₁) * (K_abs * Real.exp (lam / 2 * u))) * B := by
          gcongr
      _ = 2 * C₁ * C₂ * K_abs * (X ^ (4 * N₁) * X ^ N₂) *
            (Real.exp (lam / 2 * u) * Real.exp (-(lam * u))) := by
          rw [hB_eq]
          ring
      _ ≤ 2 * C₁ * C₂ * K_abs * X ^ (2 * (2 * N₁ + N₂)) *
            (Real.exp (lam / 2 * u) * Real.exp (-(lam * u))) := by
          gcongr
      _ = (polyP C_out (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * u))) ^ 2 := by
          rw [hexp_comb]
          dsimp [polyP, C_out, X]
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul,
            mul_comm (2 * N₁ + N₂) 2]
  have h_rhs_nonneg : 0 ≤ polyP C_out (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * u)) := by
    dsimp [polyP, C_out]
    positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq h_rhs_nonneg] at hsqrt
  have hu_eq : -(lam / 4 * u) = -(lam / 4 * ν * s / c ^ 2) := by
    dsimp [u]
    ring
  rwa [hu_eq] at hsqrt

/-! ### 4. Smoothness and rescaling of the `ℓ = 0` velocity fluctuation after overlap -/

private theorem hmean_const_smul_vec (c a : ℝ) (F : Plane → Vec) (Y : ℝ) :
    hmean c (fun y : Plane => a • F y) Y = a • hmean c F Y := by
  unfold hmean
  rw [integral_smul, smul_comm]

private theorem hmean_scale_unit_vec {c : ℝ} (hc : 0 < c) (F : Plane → Vec) (Y : ℝ) :
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

theorem hfluct_scaleField {c : ℝ} (hc : 0 < c) (f : Plane → Vec) :
    hfluct 1 (scaleField c f) = scaleField c (hfluct c f) := by
  funext y
  unfold hfluct scaleField
  have h1 : hmean 1 (fun w : Plane => c ^ 3 • f (c • w)) y.2 =
      c ^ 3 • hmean c f (c * y.2) := by
    rw [hmean_const_smul_vec, hmean_scale_unit_vec hc f y.2]
  rw [h1]
  simp [Prod.smul_snd, smul_eq_mul, smul_sub]

theorem ageJet_zero (j : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → Plane → E) (s : ℝ) :
    ageJet 0 j F s = jet j (F s) := by
  rfl

private theorem hmean_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (k : Fin 2) :
    (hmean c a η) k = hmean c (fun z => a z k) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- For `c > 0` and `s > 0`, the horizontal velocity fluctuation `hfluct c (tr.v s)` is `C^∞`. -/
theorem contDiff_hfluct_v_slice {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 < s) : ContDiff ℝ ∞ (hfluct c (tr.v s)) := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv_slice : ContDiff ℝ ∞ (tr.v s) := by
    have hmap : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1
      (hv_joint.comp hmap.contDiffOn (fun z _ => ⟨hs, mem_univ _⟩))
  have hmean_k : ∀ k : Fin 2, ContDiff ℝ ∞ (fun η : ℝ => hmean c (tr.v s) η k) := by
    intro k
    have hvk : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
    have hmk : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (fun z => tr.v x.1 z k) x.2)
        (Ioi 0 ×ˢ univ) :=
      hmeanContDiff c hc (fun r z => tr.v r z k) hvk
    have hslice := t01_contDiff_slice hmk hs
    have heq : (fun η : ℝ => hmean c (tr.v s) η k) =
        fun η : ℝ => hmean c (fun z => tr.v s z k) η := by
      funext η
      exact hmean_apply_vec hv_slice.continuous η k
    rwa [heq]
  have hmean_vec : ContDiff ℝ ∞ (fun η : ℝ => hmean c (tr.v s) η) := by
    have hpi : ContDiff ℝ ∞ (fun η : ℝ => fun k : Fin 2 => hmean c (tr.v s) η k) :=
      contDiff_pi.2 hmean_k
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp hpi
  exact hv_slice.sub (hmean_vec.comp contDiff_snd)

/-- For `c ≥ 1`, `B0277.supNormD j f ≤ B0277.supNormD j (scaleField c f)`. -/
theorem supNormD_le_supNormD_scaleField {c : ℝ} (hc : 1 ≤ c) (j : ℕ) (f : Plane → Vec) :
    B0277.supNormD j f ≤ B0277.supNormD j (scaleField c f) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h1 : 1 ≤ c ^ 3 * c ^ j := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 3 * c ^ j := mul_le_mul (one_le_pow₀ hc) (one_le_pow₀ hc) zero_le_one (by positivity)
  unfold B0277.supNormD
  apply iSup_le
  intro z
  have hsmul : c • (c⁻¹ • z) = z := smul_inv_smul₀ hc0.ne' z
  have hpt : jet j (scaleField c f) (c⁻¹ • z) = (c ^ 3 * c ^ j) • jet j f z := by
    rw [jet_scaleField j c f (c⁻¹ • z), hsmul]
  calc ‖iteratedFDeriv ℝ j f z‖ₑ
      = 1 * ‖jet j f z‖ₑ := (one_mul _).symm
    _ ≤ ENNReal.ofReal (c ^ 3 * c ^ j) * ‖jet j f z‖ₑ := by
        rw [← ENNReal.ofReal_one]
        gcongr
    _ = ‖jet j (scaleField c f) (c⁻¹ • z)‖ₑ := by
        rw [hpt, enorm_smul, Real.enorm_eq_ofReal (by positivity)]
    _ ≤ ⨆ y : Plane, ‖iteratedFDeriv ℝ j (scaleField c f) y‖ₑ :=
        le_iSup (fun y : Plane => ‖iteratedFDeriv ℝ j (scaleField c f) y‖ₑ) (c⁻¹ • z)

/-- For `c ≥ 1` and smooth `f`, `cellL2 c (jet j f) ≤ cellL2 1 (jet j (scaleField c f))`. -/
theorem cellL2_jet_le_cellL2_jet_scaleField {c : ℝ} (hc : 1 ≤ c) (j : ℕ) {f : Plane → Vec}
    (hf : ContDiff ℝ ∞ f) :
    cellL2 c (jet j f) ≤ cellL2 1 (jet j (scaleField c f)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h1 : 1 ≤ c ^ 2 * c ^ j := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 2 * c ^ j := mul_le_mul (one_le_pow₀ hc) (one_le_pow₀ hc) zero_le_one (by positivity)
  rw [cellL2_jet_scaleField hc0 j hf]
  calc cellL2 c (jet j f)
      = ENNReal.ofReal 1 * cellL2 c (jet j f) := by rw [ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (c ^ 2 * c ^ j) * cellL2 c (jet j f) := by gcongr

end PartI_T22

/-! ### 5. Post-overlap unweighted fluctuation decay leaves and conditional assembly -/

/-- **Post-overlap (`s ≥ s_c`) unweighted (`m = 0`) exponential decay of the `ℓ = 0` velocity
fluctuation jets `D^j ṽ`** (source lines 439-446, 515-517): proved unconditionally below
(`trainPostOverlapVelZero_of`) from `OverlapFluctuationDecay` (`PartI:T13`). -/
def TrainPostOverlapVelZero : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
    0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
          let c := trainPeriod ρ ν
          let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
          wCellL2 c 0 (ageJet 0 j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
          wSupNorm 0 (ageJet 0 j (fun r => hfluct c (tr.v r)) s) ≤ K

/-- **Unconditional proof of `TrainPostOverlapVelZero` from `OverlapFluctuationDecay`**:
for `s ≥ s_c = B0146.overlapAge ν c`, rescaling `U(T) = overlapField ν c tr.v T` at
`T = ν (s - s_c) / c² ≥ 0` from the unit cylinder to the period-`c` cell gives
`wCellL2 c 0 (D^j ṽ(s)) ≤ C e^{lam} e^{-lam ν s / c²}` and
`wSupNorm 0 (D^j ṽ(s)) ≤ C e^{lam} e^{-lam ν s / c²}`. -/
theorem trainPostOverlapVelZero_of (hFD : OverlapFluctuationDecay) :
    TrainPostOverlapVelZero := by
  intro ρ hρ j
  obtain ⟨C_ov, lam, ν_ov, hC_ov, hlam, hν_ov, hOv⟩ := hFD ρ hρ j
  refine ⟨C_ov * Real.exp lam, 0, lam, min ν_ov 1, mul_pos hC_ov (Real.exp_pos _), hlam,
    lt_min hν_ov one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν_ov' : ν ≤ ν_ov := hν_le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  set s_c := B0146.overlapAge ν c
  set T := ν * (s - s_c) / c ^ 2
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hν.le (sub_nonneg.2 hsc)) (sq_nonneg c)
  have hs_eq : s_c + c ^ 2 * T / ν = s := by
    have hν0 : ν ≠ 0 := hν.ne'
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
    dsimp [T]
    field_simp
    ring
  have hU_eq : overlapField ν c tr.v T = scaleField c (tr.v s) := by
    funext y
    simp [overlapField, scaleField, s_c, hs_eq]
  have hW_eq : hfluct 1 (overlapField ν c tr.v T) = scaleField c (hfluct c (tr.v s)) := by
    rw [hU_eq, PartI_T22.hfluct_scaleField hc0]
  obtain ⟨hl2_ov, hsup_ov⟩ := hOv ν hν hν_ov' tr htr T hT
  rw [hW_eq] at hl2_ov hsup_ov
  have hexp : C_ov * Real.exp (-(lam * T)) ≤
      polyP (C_ov * Real.exp lam) 0 ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
    unfold polyP
    rw [pow_zero, mul_one, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC_ov.le
    have hsc_le : ν * s_c ≤ c ^ 2 := by
      dsimp [s_c, B0146.overlapAge]
      rw [mul_div_cancel₀ _ hν.ne']
      linarith
    have hsc_div : ν * s_c / c ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hc0)).2 hsc_le
    have hT_id : -(lam * T) = lam * (ν * s_c / c ^ 2) - lam * ν * s / c ^ 2 := by
      dsimp [T]
      ring
    rw [hT_id]
    nlinarith [mul_le_mul_of_nonneg_left hsc_div hlam.le]
  have hK_le : ENNReal.ofReal (C_ov * Real.exp (-(lam * T))) ≤
      ENNReal.ofReal (polyP (C_ov * Real.exp lam) 0 ν c * Real.exp (-(lam * ν * s / c ^ 2))) :=
    ENNReal.ofReal_le_ofReal hexp
  have hsm : ContDiff ℝ ∞ (hfluct c (tr.v s)) := PartI_T22.contDiff_hfluct_v_slice hc0 tr hs
  dsimp only
  rw [PartI_T22.ageJet_zero, PartI_T22.wCellL2_zero_eq_cellL2, PartI_T22.wSupNorm_zero_jet_eq_supNormD]
  exact ⟨(PartI_T22.cellL2_jet_le_cellL2_jet_scaleField hc1 j hsm).trans (hl2_ov.trans hK_le),
    (PartI_T22.supNormD_le_supNormD_scaleField hc1 j (hfluct c (tr.v s))).trans
      (hsup_ov.trans hK_le)⟩

/-- **Leaf 1 (`PartI:T22/1`): post-overlap (`s ≥ s_c`) unweighted (`m = 0`, `ℓ = 0`) exponential
decay of the spatial jets `D^j` of the stream fluctuation `ψ̃` and pressure `p`** (source lines
439-446, 499-503, 515-522): from `TrainPostOverlapVelZero` (`ṽ` at `ℓ = 0`) and `TrainOverlap`,
the horizontal mode stream inverse `-e^{-|k_n||η|}/(2|k_n|)` on `k_n = 2πn/c ≠ 0` bounds `D^j ψ̃`,
and the cylinder pressure kernel for `-Δ p = ∂_i ∂_j (v_i v_j)` with `\bar p = -\overline{v₂²}`
(where the pure mean tensor `\bar v₁² e₁ ⊗ e₁` has zero double divergence and every other term
contains `ṽ`) bounds `D^j p`. -/
def TrainPostOverlapStreamPressureZero : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
    0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
          let c := trainPeriod ρ ν
          let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
          (wCellL2 c 0 (ageJet 0 j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
            wSupNorm 0 (ageJet 0 j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
          (wCellL2 c 0 (ageJet 0 j tr.p s) ≤ K ∧
            wSupNorm 0 (ageJet 0 j tr.p s) ≤ K)

/-- **Leaf 2 (`PartI:T22/2`): post-overlap (`s ≥ s_c`) unweighted (`m = 0`) exponential decay of
all age/spatial jets `∂_s^ℓ D^j` of `(ψ̃, ṽ, p)` from the `ℓ = 0` bounds** (source lines 523-526:
"The equations now give the age derivatives by finite induction: each fluctuation equation retains
a fluctuation factor"). -/
def TrainPostOverlapAgeDerivFromZero : Prop :=
  TrainPostOverlapVelZero → TrainPostOverlapStreamPressureZero → TrainOverlap →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
      0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
            (wCellL2 c 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
              wSupNorm 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
            (wCellL2 c 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
              wSupNorm 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
            (wCellL2 c 0 (ageJet ℓ j tr.p s) ≤ K ∧
              wSupNorm 0 (ageJet ℓ j tr.p s) ≤ K)

/-- **Unweighted (`m = 0`) post-overlap (`s ≥ s_c`) exponential decay of the mixed age/spatial jets
`∂_s^ℓ D^j` of `(ψ̃, ṽ, p)`** (source lines 515-526). -/
def TrainPostOverlapUnweightedFluctDecay : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ,
    0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
          let c := trainPeriod ρ ν
          let K : ℝ≥0∞ := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
          (wCellL2 c 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
            wSupNorm 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
          (wCellL2 c 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
            wSupNorm 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
          (wCellL2 c 0 (ageJet ℓ j tr.p s) ≤ K ∧
            wSupNorm 0 (ageJet ℓ j tr.p s) ≤ K)

/-- Assembles `TrainPostOverlapUnweightedFluctDecay` from `OverlapFluctuationDecay`, `TrainOverlap`,
and the two leaves `TrainPostOverlapStreamPressureZero` and `TrainPostOverlapAgeDerivFromZero`. -/
theorem trainPostOverlapUnweightedFluctDecay_of
    (hFD : OverlapFluctuationDecay) (hOv : TrainOverlap)
    (hSP0 : TrainPostOverlapStreamPressureZero)
    (hAge : TrainPostOverlapAgeDerivFromZero) :
    TrainPostOverlapUnweightedFluctDecay :=
  hAge (trainPostOverlapVelZero_of hFD) hSP0 hOv

/-- **Conditional assembly of `TrainFluctuationDecay` from `TrainPostOverlapUnweightedFluctDecay`**:
combines the doubled polynomial weight `2m` bound and pre-overlap (`0 < s ≤ s_c`) unweighted bound
from `TrainStreamVelocityPressureTails` with `TrainPostOverlapUnweightedFluctDecay`, interpolating
weights via `wCellL2_interp` and `wSupNorm_interp` and absorbing the polynomial factor
`(1 + s)^{N₁}` via `polyPS_mul_exp_absorb`. -/
theorem trainFluctuationDecay_of_post (hTails : TrainStreamVelocityPressureTails)
    (hPost : TrainPostOverlapUnweightedFluctDecay) :
    TrainFluctuationDecay := by
  intro ρ hρ m ℓ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT2m⟩ := hTails.2.2 ρ hρ (2 * m) ℓ j
  obtain ⟨C₀, N₀, ν₀', hC₀, hν₀', hT0⟩ := hTails.2.2 ρ hρ 0 ℓ j
  obtain ⟨CP, NP, lam, νP, hCP, hlam, hνP, hP⟩ := hPost ρ hρ ℓ j
  let C₂ : ℝ := max (C₀ * Real.exp lam) CP
  let N₂ : ℕ := max (4 * N₀) NP
  have hC₂ : 0 < C₂ := lt_of_lt_of_le (mul_pos hC₀ (Real.exp_pos _)) (le_max_left _ _)
  let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2)
  let C_out : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  have hC_out : 0 < C_out := Real.sqrt_pos.2 (by positivity)
  refine ⟨C_out, 2 * N₁ + N₂, lam / 4, min (min ν₁ ν₀') (min νP 1), hC_out, by positivity,
    lt_min (lt_min hν₁ hν₀') (lt_min hνP one_pos), ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₀'_le : ν ≤ ν₀' := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνP_le : ν ≤ νP := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  let A : ℝ := polyPS C₁ N₁ ν c s
  let B : ℝ := polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2))
  have hA_pos : 0 < A := by
    dsimp [A, polyPS]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B, polyP]
    positivity
  have h2m_all := hT2m ν hν hν₁_le tr htr s hs
  have h0_all :
      (wCellL2 c 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ ENNReal.ofReal B ∧
        wSupNorm 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ ENNReal.ofReal B) ∧
      (wCellL2 c 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ ENNReal.ofReal B ∧
        wSupNorm 0 (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ ENNReal.ofReal B) ∧
      (wCellL2 c 0 (ageJet ℓ j tr.p s) ≤ ENNReal.ofReal B ∧
        wSupNorm 0 (ageJet ℓ j tr.p s) ≤ ENNReal.ofReal B) := by
    by_cases hsc : s ≤ B0146.overlapAge ν c
    · have h0_pre := hT0 ν hν hν₀'_le tr htr s hs
      have hB_pre : polyPS C₀ N₀ ν c s ≤ B := by
        have h1 := PartI_T22.polyPS_le_polyP_mul_exp_of_le_overlapAge N₀ hC₀.le hlam.le hν hc1 hs.le hsc
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        unfold polyP
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
          (by positivity) hC₂.le
      have hK_le : ENNReal.ofReal (polyPS C₀ N₀ ν c s) ≤ ENNReal.ofReal B :=
        ENNReal.ofReal_le_ofReal hB_pre
      exact ⟨⟨h0_pre.1.1.trans hK_le, h0_pre.1.2.trans hK_le⟩,
        ⟨h0_pre.2.1.1.trans hK_le, h0_pre.2.1.2.trans hK_le⟩,
        ⟨h0_pre.2.2.2.2.1.trans hK_le, h0_pre.2.2.2.2.2.trans hK_le⟩⟩
    · have hsc' : B0146.overlapAge ν c ≤ s := (not_le.mp hsc).le
      have h0_post := hP ν hν hνP_le tr htr s hs hsc'
      have hB_post : polyP CP NP ν c * Real.exp (-(lam * ν * s / c ^ 2)) ≤ B := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        unfold polyP
        exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
          (by positivity) hC₂.le
      have hK_le : ENNReal.ofReal (polyP CP NP ν c * Real.exp (-(lam * ν * s / c ^ 2))) ≤
          ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hB_post
      exact ⟨⟨h0_post.1.1.trans hK_le, h0_post.1.2.trans hK_le⟩,
        ⟨h0_post.2.1.1.trans hK_le, h0_post.2.1.2.trans hK_le⟩,
        ⟨h0_post.2.2.1.trans hK_le, h0_post.2.2.2.trans hK_le⟩⟩
  have habs : ENNReal.ofReal (Real.sqrt (2 * A * B)) ≤
      ENNReal.ofReal (polyP C_out (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2))) :=
    ENNReal.ofReal_le_ofReal (PartI_T22.polyPS_mul_exp_absorb N₁ N₂ hC₁ hC₂ hlam hν hc1 hs.le)
  refine ⟨⟨(PartI_T22.wCellL2_interp c m _ hA_pos hB_pos h2m_all.1.1 h0_all.1.1).trans habs,
      (PartI_T22.wSupNorm_interp m _ hA_pos hB_pos h2m_all.1.2 h0_all.1.2).trans habs⟩,
    ⟨(PartI_T22.wCellL2_interp c m _ hA_pos hB_pos h2m_all.2.1.1 h0_all.2.1.1).trans habs,
      (PartI_T22.wSupNorm_interp m _ hA_pos hB_pos h2m_all.2.1.2 h0_all.2.1.2).trans habs⟩,
    ⟨(PartI_T22.wCellL2_interp c m _ hA_pos hB_pos h2m_all.2.2.2.2.1 h0_all.2.2.1).trans habs,
      (PartI_T22.wSupNorm_interp m _ hA_pos hB_pos h2m_all.2.2.2.2.2 h0_all.2.2.2).trans habs⟩⟩

/-- **Conditional assembly of `TrainFluctuationDecay` (`PartI:T22`)**: proves `TrainFluctuationDecay`
from `hTails : TrainStreamVelocityPressureTails`, `hFD : OverlapFluctuationDecay`, `hOv : TrainOverlap`,
and the two post-overlap leaves `TrainPostOverlapStreamPressureZero` (`PartI:T22/1`) and
`TrainPostOverlapAgeDerivFromZero` (`PartI:T22/2`). -/
theorem trainFluctuationDecay_of (hTails : TrainStreamVelocityPressureTails)
    (hFD : OverlapFluctuationDecay) (hOv : TrainOverlap)
    (hSP0 : TrainPostOverlapStreamPressureZero)
    (hAge : TrainPostOverlapAgeDerivFromZero) :
    TrainFluctuationDecay :=
  trainFluctuationDecay_of_post hTails (trainPostOverlapUnweightedFluctDecay_of hFD hOv hSP0 hAge)

end UnforcedLeray.Short.PartI
