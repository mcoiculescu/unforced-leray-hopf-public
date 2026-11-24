import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityBounds.Linf
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Sub.PartI_T22
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound
import UnforcedLeray.Units.B0169
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `PartI:T20` (`Sub/PartI_T20.lean`): Gaussian transverse tail of the train vorticity

Source of record: `the November 2 reference manuscript`, lines 483-497, 523-526
(old 484-492), in the proof of Lemma `sct:heat`.

## Structure of this module

1. **Global vertical velocity decay and drift primitive (`train_v2_uniform_decay`,
   `driftPrimitive`)** (source lines 483-486):
   * Pre-overlap (`0 ≤ s ≤ s_c`): combine `Train.Vc_bounds 0 0` and `trainComparison_proof` (`j = 0`)
     to bound `|tr.v s z 1| ≤ K_pre * (width ν s) ^ (-(3 / 2 : ℝ))`.
   * Post-overlap (`s ≥ s_c`, `T = ν (s - s_c) / c² ≥ 0`): since `hmean 1 U Y 1 = 0` (`hOv` at
     `j = 0`), `U y 1 = hfluct 1 U y 1`, so `|tr.v s z 1| ≤ C_ov * c⁻³ * exp(-lam * T) ≤
     K_post * (width ν s) ^ (-(3 / 2 : ℝ))`.
   * Explicit smooth primitive `driftPrimitive K_v ν s = (2 * K_v / ν) * (1 - (1 + ν * s)^{-1/2})`
     satisfying `0 ≤ driftPrimitive K_v ν s ≤ 2 * K_v / ν` and
     `HasDerivAt (driftPrimitive K_v ν) (K_v * (width ν s) ^ (-(3 / 2 : ℝ))) s`.
2. **Gaussian supersolution and parabolic comparison at `(ℓ, j) = (0, 0)`
   (`train_vorticity_gaussian_tail_zero_pointwise`, `train_vorticity_gaussian_tail_zero`)**
   (source lines 486-494):
   * For any `lam ≥ 0` and `τ ∈ {-1, 1}`,
     `gaussSupersol M₀ K_v ν lam τ r w = 40 * exp(lam * A(r) + (2 + ν r) lam²) * exp(-lam τ w.2)`
     dominates `|Cyl.curl (tr.v 0) w|` at `r = 0` (`B0169.curl_train_initial`,
     `B0169.abs_initialVorticity_le_tilt`) and satisfies `0 ≤ vorticityOp ν tr.v gaussSupersol r w`.
   * Phragmén-Lindelöf barrier comparison (`parabolicMinPrinciple`, `sechSupersolution`,
     `linf_limit`) and optimization of `τ = ±1` and `lam = max (|z.2| - C'/ν) 0 / (2 * (2 + ν * s))`
     prove the `(0, 0)` Gaussian vorticity tail unconditionally.
3. **All spatial derivatives at `ℓ = 0` (`TrainVorticitySpatialJetTail`,
   `train_vorticity_spatial_jet_tail`)** (source lines 495-497):
   * Global `L^∞` polynomial bounds on all spatial jets `jet m (tr.v s)` (`train_v_jet_sup_bound`)
     and coordinate word derivatives `B0151.derivWord w (Cyl.curl (tr.v s))`
     (`train_curl_derivWord_sup_bound`) for all `s > 0`, combining `Train.Vc_bounds` +
     `trainComparison_proof` before `s_c` with `overlap_highnorm_bound_j` after `s_c`.
   * 1D Landau-Kolmogorov interpolation along horizontal and outward vertical rays
     (`PartI_T20.deriv_abs_le_three_sqrt_of_ray`) inductively transfers the Gaussian transverse tail
     to every spatial word derivative `B0151.derivWord w (Cyl.curl (tr.v s))`
     (`train_curl_derivWord_gaussian_tail`) and hence to `ageJet 0 j (fun r w => Cyl.curl (tr.v r) w)`
     for every `j : ℕ` (`train_vorticity_spatial_jet_tail`).
4. **Age-derivative induction leaf (`TrainVorticityAgeDerivFromZero`, `PartI:T20/1`) and conditional
   assembly (`train_vorticity_gaussian_tail_of`)** (source lines 523-526):
   * Isolates the finite induction in the age derivative order `ℓ` along the differentiated
     vorticity equation `∂_s ω = ν Δω - v · ∇ω` (`TrainVorticityAgeDerivFromZero`) and assembles
     `TrainVorticityGaussianTail`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. Pointwise vertical velocity decay and explicit drift primitive -/

/-- Pointwise bound from `B0277.supNormD j f ≤ ENNReal.ofReal B`. -/
theorem norm_jet_le_of_supNormD_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) {f : Plane → E} {B : ℝ} (hB : 0 ≤ B) (h : B0277.supNormD j f ≤ ENNReal.ofReal B)
    (z : Plane) : ‖jet j f z‖ ≤ B := by
  have hz : ‖iteratedFDeriv ℝ j f z‖ₑ ≤ B0277.supNormD j f :=
    le_iSup (fun w : Plane => ‖iteratedFDeriv ℝ j f w‖ₑ) z
  have hnorm : ‖iteratedFDeriv ℝ j f z‖ₑ = ENNReal.ofReal ‖jet j f z‖ := by
    rw [← ofReal_norm]
    rfl
  rw [hnorm] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 (hz.trans h)

/-- Pointwise bound from `B0277.supNormD 0 f ≤ ENNReal.ofReal B`. -/
theorem norm_le_of_supNormD_zero_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} {B : ℝ} (hB : 0 ≤ B) (h : B0277.supNormD 0 f ≤ ENNReal.ofReal B)
    (z : Plane) : ‖f z‖ ≤ B := by
  have h0 := norm_jet_le_of_supNormD_le 0 hB h z
  unfold jet at h0
  rwa [norm_iteratedFDeriv_zero] at h0

/-- For `x ≥ 0`, `x * exp(-x) ≤ 1`. -/
private theorem mul_exp_neg_le_one_vort {x : ℝ} (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 := by
  have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc x * Real.exp (-x)
      ≤ Real.exp x * Real.exp (-x) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Pre-overlap error factor absorption: for `1 ≤ ν * c²`, `0 < a`, and `0 < b`,
`ν⁻¹ * a ^ (-((5 + 0) / 2)) * exp(-(b * c² / a)) ≤ b⁻¹ * a ^ (-(3 / 2 : ℝ))`. -/
private theorem preOverlap_v2_err_factor_le {ν c a b : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hνc2 : 1 ≤ ν * c ^ 2) :
    ν⁻¹ * a ^ (-((5 + (0 : ℝ)) / 2)) * Real.exp (-(b * c ^ 2 / a)) ≤
      b⁻¹ * a ^ (-(3 / 2 : ℝ)) := by
  have hν_inv_le : ν⁻¹ ≤ c ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hν]
    linarith
  have hrpow : a ^ (-((5 + (0 : ℝ)) / 2)) = a⁻¹ * a ^ (-(3 / 2 : ℝ)) := by
    have h5 : -((5 + (0 : ℝ)) / 2) = (-1 : ℝ) + -(3 / 2 : ℝ) := by norm_num
    rw [h5, Real.rpow_add ha, Real.rpow_neg_one]
  have hx_nn : 0 ≤ b * c ^ 2 / a := by positivity
  have h_exp := mul_exp_neg_le_one_vort hx_nn
  have h_ca : c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a)) ≤ b⁻¹ := by
    calc c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))
        = b⁻¹ * ((b * c ^ 2 / a) * Real.exp (-(b * c ^ 2 / a))) := by
          have hb_ne : b ≠ 0 := hb.ne'
          field_simp
      _ ≤ b⁻¹ * 1 := mul_le_mul_of_nonneg_left h_exp (inv_nonneg.2 hb.le)
      _ = b⁻¹ := mul_one _
  calc ν⁻¹ * a ^ (-((5 + (0 : ℝ)) / 2)) * Real.exp (-(b * c ^ 2 / a))
      = ν⁻¹ * (a⁻¹ * a ^ (-(3 / 2 : ℝ))) * Real.exp (-(b * c ^ 2 / a)) := by rw [hrpow]
    _ ≤ c ^ 2 * (a⁻¹ * a ^ (-(3 / 2 : ℝ))) * Real.exp (-(b * c ^ 2 / a)) := by gcongr
    _ = (c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))) * a ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ b⁻¹ * a ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h_ca (Real.rpow_nonneg ha.le _)

/-- For `T ≥ 0` and `lam > 0`,
`exp(-(lam * T)) ≤ (1 + (lam / 2)⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ))`. -/
private theorem exp_neg_le_rpow_neg_three_halves {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    Real.exp (-(lam * T)) ≤ (1 + (lam / 2)⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ)) := by
  set μ : ℝ := lam / 2
  have hμ : 0 < μ := half_pos hlam
  have h1T_pos : 0 < 1 + T := by linarith
  have h1T_ge1 : 1 ≤ 1 + T := by linarith
  have hexp_le1 : Real.exp (-(μ * T)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hT_exp : T * Real.exp (-(μ * T)) ≤ μ⁻¹ := by
    have hx := mul_exp_neg_le_one_vort (mul_nonneg hμ.le hT)
    calc T * Real.exp (-(μ * T))
        = μ⁻¹ * ((μ * T) * Real.exp (-(μ * T))) := by
          have hμ_ne : μ ≠ 0 := hμ.ne'
          field_simp
      _ ≤ μ⁻¹ * 1 := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hμ.le)
      _ = μ⁻¹ := mul_one _
  have hprod : (1 + T) * Real.exp (-(μ * T)) ≤ 1 + μ⁻¹ := by
    calc (1 + T) * Real.exp (-(μ * T))
        = Real.exp (-(μ * T)) + T * Real.exp (-(μ * T)) := by ring
      _ ≤ 1 + μ⁻¹ := add_le_add hexp_le1 hT_exp
  have hsq : (1 + T) ^ 2 * Real.exp (-(lam * T)) ≤ (1 + μ⁻¹) ^ 2 := by
    have hnn : 0 ≤ (1 + T) * Real.exp (-(μ * T)) := by positivity
    have hmul := mul_le_mul hprod hprod hnn (by positivity)
    have hexp2 : Real.exp (-(μ * T)) * Real.exp (-(μ * T)) = Real.exp (-(lam * T)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [μ]
      ring
    calc (1 + T) ^ 2 * Real.exp (-(lam * T))
        = ((1 + T) * Real.exp (-(μ * T))) * ((1 + T) * Real.exp (-(μ * T))) := by
          rw [ ← hexp2 ]; ring
      _ ≤ (1 + μ⁻¹) * (1 + μ⁻¹) := hmul
      _ = (1 + μ⁻¹) ^ 2 := (sq _).symm
  have hinv_le : ((1 + T) ^ 2)⁻¹ ≤ (1 + T) ^ (-(3 / 2 : ℝ)) := by
    have hr2 : ((1 + T) ^ 2)⁻¹ = (1 + T) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg h1T_pos.le, Real.rpow_two]
    rw [hr2]
    exact Real.rpow_le_rpow_of_exponent_le h1T_ge1 (by norm_num)
  calc Real.exp (-(lam * T))
      = ((1 + T) ^ 2 * Real.exp (-(lam * T))) * ((1 + T) ^ 2)⁻¹ := by
        rw [mul_comm ((1 + T) ^ 2), mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h1T_pos.ne'), mul_one]
    _ ≤ (1 + μ⁻¹) ^ 2 * ((1 + T) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ (1 + μ⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv_le (by positivity)

/-- Pre-overlap pointwise bound on `|Vc ν c s z 1|`. -/
theorem preOverlap_Vc_v2_abs_le :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s → width ν s ≤ c ^ 2 → ∀ z : Plane,
        |Vc ν c s z 1| ≤ CV * (width ν s) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, _, hC, _, hVc⟩ := Train.Vc_bounds 0 0
  refine ⟨C + 1, by linarith, fun ν c s hc ha1 hac z => ?_⟩
  have ha0 : 0 < width ν s := zero_lt_one.trans_le ha1
  have h0 := (hVc ν c s hc ha1 hac).1 [] rfl 1 z
  simp only [pow_zero, one_mul, B0151.derivWord, Nat.cast_zero, add_zero] at h0
  have hexp : -(3 : ℝ) / 2 = -(3 / 2 : ℝ) := by norm_num
  rw [hexp] at h0
  exact h0.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ha0.le _))

/-- **Uniform global vertical velocity decay (`train_v2_uniform_decay`)** (source lines 483-486):
from `Train.Vc_bounds`, `trainComparison_proof` (`j = 0`), and `hOv : TrainOverlap` (`j = 0`),
for every `ρ > 1/2` there exist `K_v > 0` and `ν₀ > 0` such that for all `0 < ν ≤ ν₀`, every
`BUC` train `tr` at period `c = trainPeriod ρ ν`, every age `s ≥ 0`, and every `z : Plane`,
`1 ≤ c`, `2 ≤ c²`, and `|tr.v s z 1| ≤ K_v * (width ν s) ^ (-(3 / 2 : ℝ))`. -/
theorem train_v2_uniform_decay (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ K_v ν₀ : ℝ, 0 < K_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          1 ≤ trainPeriod ρ ν ∧ 2 ≤ (trainPeriod ρ ν) ^ 2 ∧
          ∀ s : ℝ, 0 ≤ s → ∀ z : Plane,
            |tr.v s z 1| ≤ K_v * (width ν s) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ 0
  obtain ⟨CV, hCV, hVc⟩ := preOverlap_Vc_v2_abs_le
  obtain ⟨C_ov, lam, ν_ov, hC_ov, hlam, hν_ov, hov⟩ := hOv ρ hρ 0
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  let K_pre : ℝ := Ce * be⁻¹ + CV
  let K_post : ℝ := C_ov * (1 + (lam / 2)⁻¹) ^ 2
  have hK_pre : 0 < K_pre := by positivity
  have hK_post : 0 < K_post := by positivity
  refine ⟨max K_pre K_post, min νe (min ν_ov νp), lt_max_of_lt_left hK_pre,
    lt_min hνe (lt_min hν_ov hνp), ?_⟩
  intro ν hν hν_le tr htr
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_ov_le : ν ≤ ν_ov := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_p.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_p
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc2_ge2 : 2 ≤ c ^ 2 := by
    calc (2 : ℝ) ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hνc2_ge1 : 1 ≤ ν * c ^ 2 := by linarith
  refine ⟨hc1, hc2_ge2, fun s hs z => ?_⟩
  let s_c := B0146.overlapAge ν c
  have hw_ge1 : 1 ≤ width ν s := by
    unfold width
    nlinarith
  have ha0 : 0 < width ν s := zero_lt_one.trans_le hw_ge1
  rcases le_total s s_c with hs_le | hs_ge
  · -- Pre-overlap (`s ≤ s_c`)
    have hw_le_c2 : width ν s ≤ c ^ 2 := by
      have hw_sc : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
      have hmono : width ν s ≤ width ν s_c := by
        unfold width
        nlinarith
      exact hmono.trans_eq hw_sc
    obtain ⟨_, hsup_err⟩ := hcomp ν hν hν_e tr htr s hs hw_le_c2
    simp only [Nat.cast_zero] at hsup_err
    have herr_norm : ‖tr.v s z - Vc ν c s z‖ ≤
        Ce * ν⁻¹ * width ν s ^ (-((5 + (0 : ℝ)) / 2)) * Real.exp (-(be * c ^ 2 / width ν s)) :=
      norm_le_of_supNormD_zero_le (by positivity) hsup_err z
    have herr_v2 : |tr.v s z 1 - Vc ν c s z 1| ≤ Ce * be⁻¹ * (width ν s) ^ (-(3 / 2 : ℝ)) := by
      have h1 : |tr.v s z 1 - Vc ν c s z 1| ≤ ‖tr.v s z - Vc ν c s z‖ := by
        simpa using ss_abs_apply_le (tr.v s z - Vc ν c s z) 1
      have hfac := preOverlap_v2_err_factor_le hν hc0 ha0 hbe hνc2_ge1
      calc |tr.v s z 1 - Vc ν c s z 1|
          ≤ Ce * (ν⁻¹ * width ν s ^ (-((5 + (0 : ℝ)) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s))) := by
            linarith [herr_norm]
        _ ≤ Ce * (be⁻¹ * (width ν s) ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hfac hCe.le
        _ = Ce * be⁻¹ * (width ν s) ^ (-(3 / 2 : ℝ)) := by ring
    have hVc_v2 := hVc ν c s hc0 hw_ge1 hw_le_c2 z
    have htri : |tr.v s z 1| ≤ |tr.v s z 1 - Vc ν c s z 1| + |Vc ν c s z 1| := by
      simpa using abs_add_le (tr.v s z 1 - Vc ν c s z 1) (Vc ν c s z 1)
    calc |tr.v s z 1|
        ≤ Ce * be⁻¹ * (width ν s) ^ (-(3 / 2 : ℝ)) + CV * (width ν s) ^ (-(3 / 2 : ℝ)) :=
          htri.trans (add_le_add herr_v2 hVc_v2)
      _ = K_pre * (width ν s) ^ (-(3 / 2 : ℝ)) := by dsimp [K_pre]; ring
      _ ≤ max K_pre K_post * (width ν s) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ha0.le _)
  · -- Post-overlap (`s_c ≤ s`)
    let T : ℝ := ν * (s - s_c) / c ^ 2
    have hT_nn : 0 ≤ T := by
      dsimp [T]
      have : 0 ≤ s - s_c := sub_nonneg.2 hs_ge
      positivity
    have hs_eq : B0146.overlapAge ν c + c ^ 2 * T / ν = s := by
      dsimp [T, s_c]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    let U := overlapField ν c tr.v T
    obtain ⟨hU1, _, _, _, _, hW_sup⟩ := hov ν hν hν_ov_le tr htr T hT_nn
    let y : Plane := c⁻¹ • z
    have hcy : c • y = z := smul_inv_smul₀ hc0.ne' z
    have hUy1 : hfluct 1 U y 1 = c ^ 3 * tr.v s z 1 := by
      have hmean0 : (hmean 1 U y.2) 1 = 0 := hU1 y.2
      have hU_apply : U y 1 = c ^ 3 * tr.v s z 1 := by
        dsimp [U, overlapField]
        rw [hs_eq, hcy]
      change U y 1 - (hmean 1 U y.2) 1 = c ^ 3 * tr.v s z 1
      rw [hmean0, sub_zero, hU_apply]
    have hW_norm : ‖hfluct 1 U y‖ ≤ C_ov * Real.exp (-(lam * T)) :=
      norm_le_of_supNormD_zero_le (by positivity) hW_sup y
    have hW_y1 : |c ^ 3 * tr.v s z 1| ≤ C_ov * Real.exp (-(lam * T)) := by
      rw [← hUy1]
      exact (ss_abs_apply_le (hfluct 1 U y) 1).trans hW_norm
    have hc3_pos : 0 < c ^ 3 := pow_pos hc0 3
    have hv2_exp : |tr.v s z 1| ≤ C_ov * (c ^ 3)⁻¹ * Real.exp (-(lam * T)) := by
      rw [abs_mul, abs_of_pos hc3_pos] at hW_y1
      calc |tr.v s z 1|
          = (c ^ 3)⁻¹ * (c ^ 3 * |tr.v s z 1|) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc3_pos.ne', one_mul]
        _ ≤ (c ^ 3)⁻¹ * (C_ov * Real.exp (-(lam * T))) :=
            mul_le_mul_of_nonneg_left hW_y1 (inv_nonneg.2 hc3_pos.le)
        _ = C_ov * (c ^ 3)⁻¹ * Real.exp (-(lam * T)) := by ring
    have hw_eq : width ν s = c ^ 2 * (1 + T) := by
      unfold width
      rw [← hs_eq]
      unfold B0146.overlapAge
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    have hc2_rpow : (c ^ 2) ^ (-(3 / 2 : ℝ)) = (c ^ 3)⁻¹ := by
      have hc2 : c ^ 2 = c ^ (2 : ℝ) := (Real.rpow_two c).symm
      have hc3 : c ^ 3 = c ^ (3 : ℝ) := (Real.rpow_natCast c 3).symm
      rw [hc2, ← Real.rpow_mul hc0.le, show (2 : ℝ) * -(3 / 2 : ℝ) = -3 by norm_num,
        Real.rpow_neg hc0.le, hc3]
    have hw_rpow : (width ν s) ^ (-(3 / 2 : ℝ)) = (c ^ 3)⁻¹ * (1 + T) ^ (-(3 / 2 : ℝ)) := by
      rw [hw_eq, Real.mul_rpow (sq_nonneg c) (by positivity), hc2_rpow]
    have hexp_T := exp_neg_le_rpow_neg_three_halves hlam hT_nn
    calc |tr.v s z 1|
        ≤ C_ov * (c ^ 3)⁻¹ * Real.exp (-(lam * T)) := hv2_exp
      _ ≤ C_ov * (c ^ 3)⁻¹ * ((1 + (lam / 2)⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp_T (by positivity)
      _ = K_post * ((c ^ 3)⁻¹ * (1 + T) ^ (-(3 / 2 : ℝ))) := by dsimp [K_post]; ring
      _ = K_post * (width ν s) ^ (-(3 / 2 : ℝ)) := by rw [← hw_rpow]
      _ ≤ max K_pre K_post * (width ν s) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ha0.le _)

/-- The explicit smooth vertical drift primitive
`A(r) = (2 * K_v / ν) * (1 - (1 + ν * r) ^ (-(1 / 2 : ℝ)))`. -/
def driftPrimitive (K_v ν r : ℝ) : ℝ :=
  2 * K_v / ν * (1 - (1 + ν * r) ^ (-(1 / 2 : ℝ)))

@[simp]
theorem driftPrimitive_zero (K_v ν : ℝ) : driftPrimitive K_v ν 0 = 0 := by
  simp [driftPrimitive]

theorem driftPrimitive_nonneg {K_v ν r : ℝ} (hK : 0 ≤ K_v) (hν : 0 < ν) (hr : 0 ≤ r) :
    0 ≤ driftPrimitive K_v ν r := by
  unfold driftPrimitive
  have hw1 : 1 ≤ 1 + ν * r := by nlinarith
  have hrpow : (1 + ν * r) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    calc (1 + ν * r) ^ (-(1 / 2 : ℝ))
        ≤ (1 + ν * r) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
      _ = 1 := Real.rpow_zero _
  have hsub : 0 ≤ 1 - (1 + ν * r) ^ (-(1 / 2 : ℝ)) := sub_nonneg.2 hrpow
  positivity

theorem driftPrimitive_le {K_v ν r : ℝ} (hK : 0 ≤ K_v) (hν : 0 < ν) (hr : 0 ≤ r) :
    driftPrimitive K_v ν r ≤ 2 * K_v / ν := by
  unfold driftPrimitive
  have hw0 : 0 < 1 + ν * r := by nlinarith
  have hrpow : 0 ≤ (1 + ν * r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hw0.le _
  have hsub : 1 - (1 + ν * r) ^ (-(1 / 2 : ℝ)) ≤ 1 := by linarith
  calc 2 * K_v / ν * (1 - (1 + ν * r) ^ (-(1 / 2 : ℝ)))
      ≤ 2 * K_v / ν * 1 := mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = 2 * K_v / ν := mul_one _

theorem driftPrimitive_hasDerivAt {K_v ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (driftPrimitive K_v ν) (K_v * (width ν r) ^ (-(3 / 2 : ℝ))) r := by
  have hw0 : 0 < 1 + ν * r := by nlinarith
  have hd1 : HasDerivAt (fun t : ℝ => 1 + ν * t) ν r := by
    simpa using ((hasDerivAt_id r).const_mul ν).const_add 1
  have hd2 : HasDerivAt (fun t : ℝ => (1 + ν * t) ^ (-(1 / 2 : ℝ)))
      (ν * -(1 / 2 : ℝ) * (1 + ν * r) ^ (-(1 / 2 : ℝ) - 1)) r :=
    hd1.rpow_const (Or.inl hw0.ne')
  have hd3 : HasDerivAt (driftPrimitive K_v ν)
      (2 * K_v / ν * (0 - (ν * -(1 / 2 : ℝ) * (1 + ν * r) ^ (-(1 / 2 : ℝ) - 1)))) r :=
    ((hasDerivAt_const r (1 : ℝ)).sub hd2).const_mul (2 * K_v / ν)
  refine hd3.congr_deriv ?_
  have hexp : -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) := by norm_num
  rw [hexp]
  unfold width
  have hν0 : ν ≠ 0 := hν.ne'
  field_simp
  ring

/-! ### 2. The Gaussian supersolution and parabolic comparison at `(ℓ, j) = (0, 0)` -/

/-- Spatial exponential slice `w ↦ P * exp(a * w.2)`. -/
def expSlice (P a : ℝ) (w : Plane) : ℝ :=
  P * Real.exp (a * w.2)

theorem expSlice_contDiff (P a : ℝ) : ContDiff ℝ 2 (expSlice P a) := by
  unfold expSlice
  have hl : ContDiff ℝ 2 (fun w : Plane => a * w.2) :=
    (contDiff_const : ContDiff ℝ 2 (fun _ : Plane => a)).mul contDiff_snd
  exact (contDiff_const : ContDiff ℝ 2 (fun _ : Plane => P)).mul (Real.contDiff_exp.comp hl)

theorem expSlice_partialQ (P a : ℝ) (z : Plane) :
    Cyl.partialQ (expSlice P a) z = 0 := by
  unfold Cyl.partialQ expSlice
  simp [deriv_const]

theorem expSlice_partialEta (P a : ℝ) (z : Plane) :
    Cyl.partialEta (expSlice P a) z = a * expSlice P a z := by
  unfold Cyl.partialEta expSlice
  have hd : HasDerivAt (fun η : ℝ => P * Real.exp (a * η))
      (P * (Real.exp (a * z.2) * a)) z.2 :=
    ((ss_lin a z.2).exp).const_mul P
  rw [hd.deriv]
  ring

theorem expSlice_lapS (P a : ℝ) (z : Plane) :
    Train.lapS (expSlice P a) z = a ^ 2 * expSlice P a z := by
  have hQ : Cyl.partialQ (expSlice P a) = fun _ => 0 :=
    funext (expSlice_partialQ P a)
  have hE : Cyl.partialEta (expSlice P a) = expSlice (a * P) a := by
    funext w
    rw [expSlice_partialEta]
    unfold expSlice
    ring
  unfold Train.lapS
  rw [hQ, hE, expSlice_partialEta]
  have hQ2 : Cyl.partialQ (fun _ : Plane => (0 : ℝ)) z = 0 := by
    unfold Cyl.partialQ
    simp [deriv_const]
  rw [hQ2]
  unfold expSlice
  ring

/-- Time-dependent amplitude `M₀ * exp(lam * A(r) + (2 + ν * r) * lam²)` of the Gaussian
supersolution. -/
def gaussTimeFactor (M₀ K_v ν lam r : ℝ) : ℝ :=
  M₀ * Real.exp (lam * driftPrimitive K_v ν r + (2 + ν * r) * lam ^ 2)

/-- The Gaussian supersolution
`G(r, w) = M₀ * exp(-lam * (τ * w.2 - A(r)) + (2 + ν * r) * lam²)`
written in factored form `gaussTimeFactor M₀ K_v ν lam r * exp(-(lam * τ) * w.2)`. -/
def gaussSupersol (M₀ K_v ν lam τ : ℝ) (r : ℝ) (w : Plane) : ℝ :=
  expSlice (gaussTimeFactor M₀ K_v ν lam r) (-(lam * τ)) w

theorem gaussSupersol_eq_exp (M₀ K_v ν lam τ r : ℝ) (w : Plane) :
    gaussSupersol M₀ K_v ν lam τ r w =
      M₀ * Real.exp (-(lam * (τ * w.2 - driftPrimitive K_v ν r)) + (2 + ν * r) * lam ^ 2) := by
  unfold gaussSupersol expSlice gaussTimeFactor
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gaussSupersol_pos {M₀ : ℝ} (hM₀ : 0 < M₀) (K_v ν lam τ r : ℝ) (w : Plane) :
    0 < gaussSupersol M₀ K_v ν lam τ r w := by
  rw [gaussSupersol_eq_exp]
  exact mul_pos hM₀ (Real.exp_pos _)

theorem gaussSupersol_slice_contDiff (M₀ K_v ν lam τ r : ℝ) :
    ContDiff ℝ 2 (gaussSupersol M₀ K_v ν lam τ r) :=
  expSlice_contDiff (gaussTimeFactor M₀ K_v ν lam r) (-(lam * τ))

theorem gaussSupersol_contDiffOn {ν : ℝ} (hν : 0 < ν) (M₀ K_v lam τ T : ℝ) :
    ContDiffOn ℝ 2 (fun x : ℝ × Plane => gaussSupersol M₀ K_v ν lam τ x.1 x.2)
      (Icc 0 T ×ˢ univ) := by
  let S : Set (ℝ × Plane) := Icc 0 T ×ˢ univ
  have hw : ContDiffOn ℝ 2 (fun x : ℝ × Plane => 1 + ν * x.1) S :=
    contDiffOn_const.add (contDiffOn_const.mul contDiffOn_fst)
  have hw_ne : ∀ x ∈ S, 1 + ν * x.1 ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x.1 := hx.1.1
    positivity
  have hrpow : ContDiffOn ℝ 2 (fun x : ℝ × Plane => (1 + ν * x.1) ^ (-(1 / 2 : ℝ))) S :=
    hw.rpow_const_of_ne hw_ne
  have hA : ContDiffOn ℝ 2 (fun x : ℝ × Plane => driftPrimitive K_v ν x.1) S :=
    contDiffOn_const.mul (contDiffOn_const.sub hrpow)
  have hexp_t : ContDiffOn ℝ 2 (fun x : ℝ × Plane => gaussTimeFactor M₀ K_v ν lam x.1) S := by
    have hlin : ContDiffOn ℝ 2
        (fun x : ℝ × Plane => lam * driftPrimitive K_v ν x.1 + (2 + ν * x.1) * lam ^ 2) S :=
      (contDiffOn_const.mul hA).add
        ((contDiffOn_const.add (contDiffOn_const.mul contDiffOn_fst)).mul contDiffOn_const)
    exact contDiffOn_const.mul (Real.contDiff_exp.comp_contDiffOn hlin)
  have hexp_w : ContDiffOn ℝ 2 (fun x : ℝ × Plane => Real.exp (-(lam * τ) * x.2.2)) S :=
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_snd.comp contDiff_snd))).contDiffOn
  exact hexp_t.mul hexp_w

theorem gaussSupersol_hasDerivAt_t {M₀ K_v ν lam τ r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (z : Plane) :
    HasDerivAt (fun t : ℝ => gaussSupersol M₀ K_v ν lam τ t z)
      ((lam * (K_v * (width ν r) ^ (-(3 / 2 : ℝ))) + ν * lam ^ 2) *
        gaussSupersol M₀ K_v ν lam τ r z) r := by
  have hA := driftPrimitive_hasDerivAt (K_v := K_v) hν hr
  have hlin : HasDerivAt (fun t : ℝ => 2 + ν * t) ν r := by
    simpa using ((hasDerivAt_id r).const_mul ν).const_add 2
  have hexp_arg : HasDerivAt
      (fun t : ℝ => lam * driftPrimitive K_v ν t + (2 + ν * t) * lam ^ 2)
      (lam * (K_v * (width ν r) ^ (-(3 / 2 : ℝ))) + ν * lam ^ 2) r :=
    (hA.const_mul lam).add (hlin.mul_const (lam ^ 2))
  have hTF : HasDerivAt (gaussTimeFactor M₀ K_v ν lam)
      (M₀ * (Real.exp (lam * driftPrimitive K_v ν r + (2 + ν * r) * lam ^ 2) *
        (lam * (K_v * (width ν r) ^ (-(3 / 2 : ℝ))) + ν * lam ^ 2))) r :=
    (hexp_arg.exp).const_mul M₀
  have hG := hTF.mul_const (Real.exp (-(lam * τ) * z.2))
  refine hG.congr_deriv ?_
  unfold gaussSupersol expSlice gaussTimeFactor
  ring

theorem gaussSupersol_vorticityOp_eq {M₀ K_v ν lam τ r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hτ : τ ^ 2 = 1) (b : ℝ → Plane → Vec) (z : Plane) :
    vorticityOp ν b (gaussSupersol M₀ K_v ν lam τ) r z =
      lam * (K_v * (width ν r) ^ (-(3 / 2 : ℝ)) - τ * b r z 1) *
        gaussSupersol M₀ K_v ν lam τ r z := by
  unfold vorticityOp
  rw [(gaussSupersol_hasDerivAt_t hν hr z).deriv]
  unfold gaussSupersol
  rw [expSlice_partialQ, expSlice_partialEta, expSlice_lapS]
  have hτ2 : (-(lam * τ)) ^ 2 = lam ^ 2 := by
    calc (-(lam * τ)) ^ 2 = lam ^ 2 * τ ^ 2 := by ring
      _ = lam ^ 2 * 1 := by rw [hτ]
      _ = lam ^ 2 := mul_one _
  rw [hτ2]
  ring

theorem gaussSupersol_vorticityOp_nonneg {M₀ K_v ν lam τ r : ℝ} (hM₀ : 0 < M₀) (hν : 0 < ν)
    (hr : 0 ≤ r) (hlam : 0 ≤ lam) (hτ : τ ^ 2 = 1) {b : ℝ → Plane → Vec} {z : Plane}
    (hb : |b r z 1| ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ))) :
    0 ≤ vorticityOp ν b (gaussSupersol M₀ K_v ν lam τ) r z := by
  rw [gaussSupersol_vorticityOp_eq hν hr hτ b z]
  have hτ_abs : |τ| ≤ 1 := by
    have hsq : |τ| ^ 2 ≤ 1 ^ 2 := by rw [sq_abs, hτ, one_pow]
    exact (abs_le_of_sq_le_sq' hsq zero_le_one).2
  have hτb : τ * b r z 1 ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ)) := by
    calc τ * b r z 1
        ≤ |τ * b r z 1| := le_abs_self _
      _ = |τ| * |b r z 1| := abs_mul _ _
      _ ≤ 1 * (K_v * (width ν r) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul hτ_abs hb (abs_nonneg _) zero_le_one
      _ = K_v * (width ν r) ^ (-(3 / 2 : ℝ)) := one_mul _
  have hsub : 0 ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ)) - τ * b r z 1 := sub_nonneg.2 hτb
  exact mul_nonneg (mul_nonneg hlam hsub) (gaussSupersol_pos hM₀ K_v ν lam τ r z).le

/-- At `r = 0`, `gaussSupersol 40 K_v ν lam τ 0 z` dominates `|Cyl.curl (tr.v 0) z|` whenever
`2 ≤ c²` and `τ² = 1`. -/
theorem gaussSupersol_datum_le {ν c : ℝ} (hc2 : 2 ≤ c ^ 2) (tr : B0140.TrainSol ν c)
    (K_v lam τ : ℝ) (hτ : τ ^ 2 = 1) (z : Plane) :
    |Cyl.curl (tr.v 0) z| ≤ gaussSupersol 40 K_v ν lam τ 0 z := by
  have hc_ne : c ≠ 0 := by
    intro h
    rw [h, sq, mul_zero] at hc2
    linarith
  rw [B0169.curl_train_initial tr.isTrain hc_ne z]
  have htilt := B0169.abs_initialVorticity_le_tilt hc2 (lam * τ) z
  have hτ2 : (lam * τ) ^ 2 = lam ^ 2 := by
    calc (lam * τ) ^ 2 = lam ^ 2 * τ ^ 2 := by ring
      _ = lam ^ 2 * 1 := by rw [hτ]
      _ = lam ^ 2 := mul_one _
  rw [hτ2] at htilt
  refine htilt.trans (le_of_eq ?_)
  rw [gaussSupersol_eq_exp, driftPrimitive_zero]
  congr 2
  ring

/-- Core minimum-principle step comparing `σ * om r w` against
`gaussSupersol M₀ K_v ν lam τ r w + coshBarrier ε K 1 r w`. -/
theorem gaussSupersol_core
    (ν c T β M₀ K_v lam τ Mw K : ℝ) (b : ℝ → Plane → Vec) (om : ℝ → Plane → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hT : 0 < T) (hM₀ : 0 < M₀) (hlam : 0 ≤ lam) (hτ : τ ^ 2 = 1)
    (hK : β + ν < K)
    (hb : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : Plane, ‖b r w‖ ≤ β)
    (hb1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : Plane, |b r w 1| ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ)))
    (hcont : ContinuousOn (fun x : ℝ × Plane => om x.1 x.2) (Icc 0 T ×ˢ univ))
    (hC2 : ContDiffOn ℝ 2 (fun x : ℝ × Plane => om x.1 x.2) (Ioo 0 T ×ˢ univ))
    (hper : ∀ r ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (om r))
    (hMw : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : Plane, |om r w| ≤ Mw)
    (hop : ∀ r ∈ Ioo (0 : ℝ) T, ∀ w : Plane, vorticityOp ν b om r w = 0)
    (hG0 : ∀ w : Plane, |om 0 w| ≤ gaussSupersol M₀ K_v ν lam τ 0 w)
    (σ : ℝ) (hσ : |σ| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ r ∈ Ico (0 : ℝ) T, ∀ w : Plane,
      σ * om r w ≤ gaussSupersol M₀ K_v ν lam τ r w + coshBarrier ε K 1 r w := by
  let G := gaussSupersol M₀ K_v ν lam τ
  have hsig : ∀ x : ℝ, σ * x ≤ |x| := fun x => by
    calc σ * x ≤ |σ * x| := le_abs_self _
      _ = |σ| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hσ (abs_nonneg x)
      _ = |x| := one_mul _
  have hpb : ∀ t w, pbF 0 ε K 1 t w = coshBarrier ε K 1 t w := by
    intro t w
    simp [pbF, sechBarrier]
  have hβ : 0 ≤ β := (norm_nonneg (b 0 0)).trans (hb 0 ⟨le_rfl, hT.le⟩ 0)
  have hK0 : 0 ≤ K := by linarith
  have hF : ContDiff ℝ 2 (fun x : ℝ × Plane => pbF 0 ε K 1 x.1 x.2) := pbF_contDiff 0 ε K 1
  have hG_cd : ContDiffOn ℝ 2 (fun x : ℝ × Plane => G x.1 x.2) (Icc 0 T ×ˢ univ) :=
    gaussSupersol_contDiffOn hν M₀ K_v lam τ T
  have hcosh_pos : ∀ t w, 0 < coshBarrier ε K 1 t w := by
    intro t w
    unfold coshBarrier
    exact mul_pos (mul_pos hε (Real.exp_pos _)) (Real.cosh_pos _)
  have hDcont : ContinuousOn
      (fun x : ℝ × Plane => (pbF 0 ε K 1 x.1 x.2 - (-1) * G x.1 x.2) - σ * om x.1 x.2)
      (Icc 0 T ×ˢ univ) :=
    ((hF.continuous.continuousOn).sub (continuousOn_const.mul hG_cd.continuousOn)).sub
      (continuousOn_const.mul hcont)
  have hDcd : ContDiffOn ℝ 2
      (fun x : ℝ × Plane => (pbF 0 ε K 1 x.1 x.2 - (-1) * G x.1 x.2) - σ * om x.1 x.2)
      (Ioo 0 T ×ˢ univ) := by
    have hG_oo : ContDiffOn ℝ 2 (fun x : ℝ × Plane => G x.1 x.2) (Ioo 0 T ×ˢ univ) :=
      hG_cd.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)
    exact (hF.contDiffOn.sub (contDiffOn_const.mul hG_oo)).sub (contDiffOn_const.mul hC2)
  have hDper : ∀ r ∈ Icc (0 : ℝ) T,
      Cyl.IsPeriodic c (fun w => (pbF 0 ε K 1 r w - (-1) * G r w) - σ * om r w) := by
    intro r hr w
    have hp : om r (w.1 + c, w.2) = om r w := hper r hr w
    have hq : pbF 0 ε K 1 r (w.1 + c, w.2) = pbF 0 ε K 1 r w := rfl
    have hg : G r (w.1 + c, w.2) = G r w := rfl
    show (pbF 0 ε K 1 r (w.1 + c, w.2) - (-1) * G r (w.1 + c, w.2)) - σ * om r (w.1 + c, w.2)
        = (pbF 0 ε K 1 r w - (-1) * G r w) - σ * om r w
    rw [hp, hq, hg]
  have hD0 : ∀ w : Plane, 0 ≤ (pbF 0 ε K 1 0 w - (-1) * G 0 w) - σ * om 0 w := by
    intro w
    rw [hpb]
    have h1 := hsig (om 0 w)
    have h3 := hG0 w
    have h4 := hcosh_pos 0 w
    linarith
  obtain ⟨R, hR0, hRM⟩ := pb_exists_R 1 ε Mw one_pos hε
  have hDR : ∀ r ∈ Icc (0 : ℝ) T, ∀ w : Plane, R ≤ |w.2| →
      0 ≤ (pbF 0 ε K 1 r w - (-1) * G r w) - σ * om r w := by
    intro r hr w hRw
    have hcosh_le : Real.cosh (1 * R) ≤ Real.cosh (1 * w.2) := by
      rw [Real.cosh_le_cosh, one_mul, one_mul, abs_of_nonneg hR0]
      exact hRw
    have hexp1 : 1 ≤ Real.exp (K * r) := Real.one_le_exp (mul_nonneg hK0 hr.1)
    have hΦ : Mw ≤ coshBarrier ε K 1 r w := by
      have h1 : ε * Real.cosh (1 * R) ≤ ε * Real.cosh (1 * w.2) :=
        mul_le_mul_of_nonneg_left hcosh_le hε.le
      have h2 : Real.cosh (1 * w.2) ≤ Real.exp (K * r) * Real.cosh (1 * w.2) :=
        le_mul_of_one_le_left (Real.cosh_pos _).le hexp1
      have h3 : ε * Real.cosh (1 * w.2) ≤ ε * (Real.exp (K * r) * Real.cosh (1 * w.2)) :=
        mul_le_mul_of_nonneg_left h2 hε.le
      unfold coshBarrier
      rw [mul_assoc]
      linarith [hRM]
    have hsx := hsig (om r w)
    have hMr := hMw r hr w
    have hmo : σ * om r w ≤ Mw := hsx.trans hMr
    have hG_pos : 0 < G r w := gaussSupersol_pos hM₀ K_v ν lam τ r w
    rw [hpb]
    linarith
  have hDop : ∀ r ∈ Ioo (0 : ℝ) T, ∀ w : Plane,
      (fun t u => (pbF 0 ε K 1 t u - (-1) * G t u) - σ * om t u) r w < 0 →
        0 < vorticityOp ν b (fun t u => (pbF 0 ε K 1 t u - (-1) * G t u) - σ * om t u) r w := by
    intro r hr w _
    have hrI : r ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hr
    have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => pbF 0 ε K 1 x.1 x.2) (r, w) :=
      (hF.differentiable (by norm_num)) (r, w)
    have hFt : DifferentiableAt ℝ (fun t => pbF 0 ε K 1 t w) r := pb_tslice_diffAt hd
    have hGt_G : DifferentiableAt ℝ (fun t => G t w) r :=
      (gaussSupersol_hasDerivAt_t hν hrI.1 w).differentiableAt
    have hGd : DifferentiableAt ℝ (fun x : ℝ × Plane => om x.1 x.2) (r, w) :=
      (hC2.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ w⟩)
    have hGt : DifferentiableAt ℝ (fun t => om t w) r := pb_tslice_diffAt hGd
    have hFs : ContDiff ℝ 2 (fun u => pbF 0 ε K 1 r u) := pb_slice_contDiff hF r
    have hGs : ContDiff ℝ 2 (G r) := gaussSupersol_slice_contDiff M₀ K_v ν lam τ r
    have hOs : ContDiff ℝ 2 (om r) := pb_slice_contDiff_om hC2 hr
    have hEt : DifferentiableAt ℝ (fun t => pbF 0 ε K 1 t w - (-1) * G t w) r :=
      hFt.sub (hGt_G.const_mul (-1))
    have hEs : ContDiff ℝ 2 (fun u => pbF 0 ε K 1 r u - (-1) * G r u) :=
      hFs.sub (contDiff_const.mul hGs)
    have hl1 : vorticityOp ν b (fun t u => pbF 0 ε K 1 t u - (-1) * G t u) r w
        = vorticityOp ν b (fun t u => pbF 0 ε K 1 t u) r w
          - (-1) * vorticityOp ν b G r w :=
      pb_vorticityOp_sub ν b (fun t u => pbF 0 ε K 1 t u) G (-1) r w
        hFs hGs hFt hGt_G
    have hl2 : vorticityOp ν b (fun t u => (pbF 0 ε K 1 t u - (-1) * G t u) - σ * om t u) r w
        = vorticityOp ν b (fun t u => pbF 0 ε K 1 t u - (-1) * G t u) r w
          - σ * vorticityOp ν b om r w :=
      pb_vorticityOp_sub ν b (fun t u => pbF 0 ε K 1 t u - (-1) * G t u) om σ r w
        hEs hOs hEt hGt
    have hG_op : 0 ≤ vorticityOp ν b G r w :=
      gaussSupersol_vorticityOp_nonneg hM₀ hν hrI.1 hlam hτ (hb1 r hrI w)
    have hop' := hop r hr w
    have hpos : 0 < vorticityOp ν b (fun t u => pbF 0 ε K 1 t u) r w := by
      have h2 := sechSupersolution ν β 0 ε K 1 b r w hν.le one_pos le_rfl hε.le (hb r hrI w)
      have hsech0 : sechBarrier 0 K 1 r w = 0 := by simp [sechBarrier]
      have hLpos : 0 < (K - β * 1 - ν * 1 ^ 2) *
          (sechBarrier 0 K 1 r w + coshBarrier ε K 1 r w) := by
        rw [hsech0, zero_add]
        have e : K - β * 1 - ν * 1 ^ 2 = K - β - ν := by ring
        rw [e]
        exact mul_pos (by linarith) (hcosh_pos r w)
      exact lt_of_lt_of_le hLpos h2
    rw [hl2, hl1, hop']
    linarith
  have hmin := parabolicMinPrinciple ν c T R b
    (fun t u => (pbF 0 ε K 1 t u - (-1) * G t u) - σ * om t u)
    hν hc hT hDcont hDcd hDper hD0 hDR hDop
  intro r hr w
  have h := hmin r hr w
  rw [hpb] at h
  linarith

/-- Pointwise comparison against `gaussSupersol 40 K_v ν lam τ` for all `s ≥ 0`, `lam ≥ 0`, and
`τ² = 1`. -/
theorem gaussSupersol_comparison {ν c K_v : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hc2 : 2 ≤ c ^ 2)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hv2 : ∀ r : ℝ, 0 ≤ r → ∀ w : Plane, |tr.v r w 1| ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ)))
    {lam τ : ℝ} (hlam : 0 ≤ lam) (hτ : τ ^ 2 = 1) (s : ℝ) (hs : 0 ≤ s) (z : Plane) :
    |Cyl.curl (tr.v s) z| ≤ gaussSupersol 40 K_v ν lam τ s z := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hT : (0 : ℝ) < s + 1 := by linarith
  have cl := trainSol_isClassicalOn tr (s + 1)
  obtain ⟨hcont, hC2, ⟨Mw, hMw⟩, hper⟩ :=
    curlRegularity c (s + 1) tr.v hc0 hT cl.smooth_v cl.periodic_v (htr (s + 1) hT.le)
  obtain ⟨β0, hβ0⟩ := vfm_sup_bound (htr (s + 1) hT.le)
  have hop : ∀ r ∈ Ioo (0 : ℝ) (s + 1), ∀ w : Plane,
      vorticityOp ν tr.v (fun t u => Cyl.curl (tr.v t) u) r w = 0 :=
    fun r hr w => localVorticityEquation ν c (s + 1) tr.v tr.p hν hc1 hT cl r hr w
  have hb : ∀ r ∈ Icc (0 : ℝ) (s + 1), ∀ w : Plane, ‖tr.v r w‖ ≤ |β0| :=
    fun r hr w => (hβ0 r hr w).trans (le_abs_self β0)
  have hb1 : ∀ r ∈ Icc (0 : ℝ) (s + 1), ∀ w : Plane,
      |tr.v r w 1| ≤ K_v * (width ν r) ^ (-(3 / 2 : ℝ)) :=
    fun r hr w => hv2 r hr.1 w
  have hG0 : ∀ w : Plane, |Cyl.curl (tr.v 0) w| ≤ gaussSupersol 40 K_v ν lam τ 0 w :=
    gaussSupersol_datum_le hc2 tr K_v lam τ hτ
  let K : ℝ := |β0| + ν + 1
  have hK : |β0| + ν < K := by dsimp [K]; linarith
  have key1 : ∀ σ : ℝ, |σ| ≤ 1 → ∀ ε : ℝ, 0 < ε →
      σ * Cyl.curl (tr.v s) z ≤ gaussSupersol 40 K_v ν lam τ s z + coshBarrier ε K 1 s z :=
    fun σ hσ ε hε =>
      gaussSupersol_core ν c (s + 1) |β0| 40 K_v lam τ Mw K tr.v
        (fun t u => Cyl.curl (tr.v t) u) hν hc0 hT (by norm_num) hlam hτ hK hb hb1 hcont hC2
        hper hMw hop hG0 σ hσ ε hε s ⟨hs, by linarith⟩ z
  have hlim : ∀ σ : ℝ, |σ| ≤ 1 →
      σ * Cyl.curl (tr.v s) z ≤ gaussSupersol 40 K_v ν lam τ s z := by
    intro σ hσ
    refine linf_limit _ (gaussSupersol 40 K_v ν lam τ s z)
      (Real.exp (K * s) * Real.cosh (1 * z.2)) ?_ ?_
    · exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    · intro ε hε
      have e : coshBarrier ε K 1 s z = ε * (Real.exp (K * s) * Real.cosh (1 * z.2)) := by
        unfold coshBarrier
        ring
      rw [← e]
      exact key1 σ hσ ε hε
  have h1 := hlim 1 (by norm_num)
  have h2 := hlim (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **Pointwise Gaussian vorticity tail at `(ℓ, j) = (0, 0)`
(`train_vorticity_gaussian_tail_zero_pointwise`)** (source lines 486-494):
optimizing `τ = ±1` and `lam = max (|z.2| - (2 * K_v) / ν) 0 / (2 * (2 + ν * s))` in
`gaussSupersol_comparison` gives
`|Cyl.curl (tr.v s) z| ≤ 40 * exp(-((1/4) * (max (|z.2| - C'/ν) 0)² / (2 + ν * s)))`
with `C' = 2 * K_v`, `b = 1/4`, `C₀ = 2`. -/
theorem train_vorticity_gaussian_tail_zero_pointwise (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C' ν₀ : ℝ, 0 < C' ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 ≤ s → ∀ z : Plane,
            let d := max (|z.2| - C' / ν) 0
            |Cyl.curl (tr.v s) z| ≤
              40 * Real.exp (-((1 / 4 : ℝ) * d ^ 2 / (2 + ν * s))) := by
  obtain ⟨K_v, ν₀, hK_v, hν₀, hv2_all⟩ := train_v2_uniform_decay hOv ρ hρ
  let C' : ℝ := 2 * K_v
  have hC' : 0 < C' := by positivity
  refine ⟨C', ν₀, hC', hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs z
  obtain ⟨hc1, hc2, hv2⟩ := hv2_all ν hν hν_le tr htr
  let d : ℝ := max (|z.2| - C' / ν) 0
  have hd_nn : 0 ≤ d := le_max_right _ _
  have hden_pos : 0 < 2 + ν * s := by nlinarith
  let lam : ℝ := d / (2 * (2 + ν * s))
  have hlam_nn : 0 ≤ lam := div_nonneg hd_nn (by positivity)
  obtain ⟨τ, hτ_sq, hτ_z⟩ : ∃ τ : ℝ, τ ^ 2 = 1 ∧ τ * z.2 = |z.2| := by
    rcases le_total 0 z.2 with hz | hz
    · exact ⟨1, by norm_num, by rw [one_mul, abs_of_nonneg hz]⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [abs_of_nonpos hz]
      ring
  have hcomp := gaussSupersol_comparison hν hc1 hc2 tr htr hv2 hlam_nn hτ_sq s hs z
  rw [gaussSupersol_eq_exp, hτ_z] at hcomp
  have hA_le : driftPrimitive K_v ν s ≤ C' / ν := driftPrimitive_le hK_v.le hν hs
  have h_sub_ge : -(lam * (|z.2| - driftPrimitive K_v ν s)) ≤ -(lam * d) := by
    apply neg_le_neg
    by_cases hd0 : |z.2| - C' / ν ≤ 0
    · have hd_eq0 : d = 0 := max_eq_right hd0
      have hlam_eq0 : lam = 0 := by dsimp [lam]; rw [hd_eq0, zero_div]
      rw [hlam_eq0, zero_mul, zero_mul]
    · have hd0' : 0 < |z.2| - C' / ν := not_le.mp hd0
      have hd_eq : d = |z.2| - C' / ν := max_eq_left hd0'.le
      have hle : d ≤ |z.2| - driftPrimitive K_v ν s := by linarith
      exact mul_le_mul_of_nonneg_left hle hlam_nn
  have hexp_alg : -(lam * d) + (2 + ν * s) * lam ^ 2 =
      -((1 / 4 : ℝ) * d ^ 2 / (2 + ν * s)) := by
    dsimp [lam]
    have hden_ne : 2 + ν * s ≠ 0 := hden_pos.ne'
    field_simp
    ring
  calc |Cyl.curl (tr.v s) z|
      ≤ 40 * Real.exp (-(lam * (|z.2| - driftPrimitive K_v ν s)) + (2 + ν * s) * lam ^ 2) := hcomp
    _ ≤ 40 * Real.exp (-(lam * d) + (2 + ν * s) * lam ^ 2) := by
        gcongr
    _ = 40 * Real.exp (-((1 / 4 : ℝ) * d ^ 2 / (2 + ν * s))) := by
        rw [hexp_alg]

/-- The `(ℓ, j) = (0, 0)` norm of `ageJet` equals the absolute value of the scalar field. -/
theorem norm_ageJet_zero_zero (F : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) :
    ‖ageJet 0 0 F s z‖ = |F s z| := by
  unfold ageJet jet
  rw [norm_iteratedFDeriv_zero, iteratedDeriv_zero, Real.norm_eq_abs]

/-- **The `(ℓ, j) = (0, 0)` case of `TrainVorticityGaussianTail` (`TrainVorticityGaussianTailZero`)**,
proved unconditionally below. -/
def TrainVorticityGaussianTailZero : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            let c := trainPeriod ρ ν
            let d := max (|z.2| - C' / ν) 0
            ‖ageJet 0 0 (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
              polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))

/-- **Unconditional proof of `TrainVorticityGaussianTailZero` (`train_vorticity_gaussian_tail_zero`)**
from `hOv : TrainOverlap`. -/
theorem train_vorticity_gaussian_tail_zero (hOv : TrainOverlap) :
    TrainVorticityGaussianTailZero := by
  intro ρ hρ
  obtain ⟨C', ν₀, hC', hν₀, hpt⟩ := train_vorticity_gaussian_tail_zero_pointwise hOv ρ hρ
  refine ⟨1 / 4, 2, C', by norm_num, by norm_num, hC', 40, 0, ν₀, by norm_num, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs z
  dsimp only
  rw [norm_ageJet_zero_zero]
  have h := hpt ν hν hν_le tr htr s hs.le z
  have hpoly : polyP 40 0 ν (trainPeriod ρ ν) = 40 := by
    unfold polyP
    simp
  rw [hpoly]
  exact h

/-! ### 3. Spatial derivative transfer (`ℓ = 0`, all `j : ℕ`) -/

namespace PartI_T20

/-- Smoothness of `Cyl.curl u` from `ContDiff ℝ ∞ u`. -/
theorem contDiff_curl_of_contDiff {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (Cyl.curl u) := by
  have h1 : ContDiff ℝ ∞ (fun x : Plane => u x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have h0 : ContDiff ℝ ∞ (fun x : Plane => u x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  exact (B0151.contDiff_derivWord h1 [true]).sub (B0151.contDiff_derivWord h0 [false])

/-- Smoothness of a velocity slice `tr.v s` at any `s ≥ 0`. -/
theorem contDiff_train_v_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hmap : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.1
    (tr.isTrain.smooth_v.comp hmap.contDiffOn (fun z _ => ⟨hs, mem_univ _⟩))

/-- Pre-overlap pointwise bound on `‖jet m (Vc ν c s) z‖` at any `s > 0`. -/
theorem preOverlap_Vc_jet_norm_le (m : ℕ) :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 < s → 1 ≤ width ν s → width ν s ≤ c ^ 2 → ∀ z : Plane,
        ‖jet m (Vc ν c s) z‖ ≤ CV := by
  obtain ⟨C, _, hC, _, hVc⟩ := Train.Vc_bounds m 0
  let CV : ℝ := (2 * (2 : ℝ) ^ m) * (C + 1)
  have hCV : 0 < CV := by positivity
  refine ⟨CV, hCV, fun ν c s hν hc hs ha1 hac z => ?_⟩
  have hsm : ContDiff ℝ ∞ (Vc ν c s) := vcSmoothPosE_proof ν c hν hc s hs
  have hpt := jl2_pointwise m (Vc ν c s) hsm z
  have hword : ∀ i ∈ wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2)),
      |wordComp i.1 (Vc ν c s) i.2 z| ≤ C + 1 := by
    intro i hi
    have hw : i.1.length = m := jsb_mem_wordsOfLength.1 (Finset.mem_product.1 hi).1
    have h0 := (hVc ν c s hc ha1 hac).1 i.1 hw i.2 z
    simp only [pow_zero, one_mul] at h0
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hrpow_le1 : (width ν s) ^ (-(3 + (m : ℝ)) / 2) ≤ 1 := by
      calc (width ν s) ^ (-(3 + (m : ℝ)) / 2)
          ≤ (width ν s) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
        _ = 1 := Real.rpow_zero _
    calc |wordComp i.1 (Vc ν c s) i.2 z|
        ≤ C * (width ν s) ^ (-(3 + (m : ℝ)) / 2) := h0
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hrpow_le1 hC
      _ ≤ C + 1 := by linarith
  have hsum : ∑ i ∈ wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2)),
      |wordComp i.1 (Vc ν c s) i.2 z| ≤
      ((wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) * (C + 1) := by
    calc ∑ i ∈ wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2)),
          |wordComp i.1 (Vc ν c s) i.2 z|
        ≤ ∑ _i ∈ wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2)), (C + 1) :=
          Finset.sum_le_sum hword
      _ = ((wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) * (C + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤ 2 * (2 : ℝ) ^ m := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hW : (wordsOfLength m).card ≤ 2 ^ m := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_image_le
        _ = 2 ^ m := by simp
    have hW' : (wordsOfLength m).card * 2 ≤ 2 * 2 ^ m := by omega
    exact_mod_cast hW'
  calc ‖jet m (Vc ν c s) z‖
      ≤ ((wordsOfLength m ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) * (C + 1) :=
        hpt.trans hsum
    _ ≤ (2 * (2 : ℝ) ^ m) * (C + 1) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Uniform global polynomial bound on `‖jet m (tr.v s) z‖` for all `s > 0` and `z : Plane`. -/
theorem train_v_jet_sup_bound (ρ : ℝ) (hρ : 1 / 2 < ρ) (m : ℕ) :
    ∃ C_v ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            ‖jet m (tr.v s) z‖ ≤ polyP C_v 1 ν (trainPeriod ρ ν) := by
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ m
  obtain ⟨CV, hCV, hVc⟩ := preOverlap_Vc_jet_norm_le m
  obtain ⟨C_ov, ν_ov, hC_ov, hν_ov, hov⟩ := overlap_highnorm_bound_j ρ hρ m
  obtain ⟨νp, hνp, _, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  let C_v : ℝ := Ce + CV + C_ov
  have hC_v : 0 < C_v := by positivity
  refine ⟨C_v, min νe (min ν_ov νp), hC_v, lt_min hνe (lt_min hν_ov hνp), ?_⟩
  intro ν hν hν_le tr htr s hs z
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_ov_le : ν ≤ ν_ov := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hc1, _⟩ := hp ν hν hν_p
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let s_c := B0146.overlapAge ν c
  have hw_ge1 : 1 ≤ width ν s := by
    unfold width
    nlinarith
  rcases le_total s s_c with hs_le | hs_ge
  · -- Pre-overlap (`0 < s ≤ s_c`)
    have hw_le_c2 : width ν s ≤ c ^ 2 := by
      have hw_sc : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
      have hmono : width ν s ≤ width ν s_c := by
        unfold width
        nlinarith
      exact hmono.trans_eq hw_sc
    obtain ⟨_, hsup_err⟩ := hcomp ν hν hν_e tr htr s hs.le hw_le_c2
    have herr_z : ‖jet m (fun w => tr.v s w - Vc ν c s w) z‖ ≤
        Ce * ν⁻¹ * width ν s ^ (-((5 + (m : ℝ)) / 2)) *
          Real.exp (-(be * c ^ 2 / width ν s)) :=
      norm_jet_le_of_supNormD_le m (by positivity) hsup_err z
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hrpow_le1 : width ν s ^ (-((5 + (m : ℝ)) / 2)) ≤ 1 := by
      calc width ν s ^ (-((5 + (m : ℝ)) / 2) : ℝ)
          ≤ width ν s ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw_ge1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have hexp_le1 : Real.exp (-(be * c ^ 2 / width ν s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have ha0 : 0 < width ν s := zero_lt_one.trans_le hw_ge1
      have : 0 ≤ be * c ^ 2 / width ν s := by positivity
      linarith
    have herr_le : ‖jet m (fun w => tr.v s w - Vc ν c s w) z‖ ≤ Ce * ν⁻¹ := by
      calc ‖jet m (fun w => tr.v s w - Vc ν c s w) z‖
          ≤ Ce * ν⁻¹ * (width ν s ^ (-((5 + (m : ℝ)) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s))) := by linarith [herr_z]
        _ ≤ Ce * ν⁻¹ * (1 * 1) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul hrpow_le1 hexp_le1 (Real.exp_pos _).le zero_le_one
            · positivity
        _ = Ce * ν⁻¹ := by ring
    have hVc_le : ‖jet m (Vc ν c s) z‖ ≤ CV := hVc ν c s hν hc0 hs hw_ge1 hw_le_c2 z
    have hv_sm : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs.le
    have hVc_sm : ContDiff ℝ ∞ (Vc ν c s) := vcSmoothPosE_proof ν c hν hc0 s hs
    have hadd_fn : tr.v s = (fun w => tr.v s w - Vc ν c s w) + Vc ν c s := by
      funext w
      simp [Pi.add_apply]
    have hjet_add : jet m (tr.v s) z =
        jet m (fun w => tr.v s w - Vc ν c s w) z + jet m (Vc ν c s) z := by
      unfold jet
      conv_lhs => rw [hadd_fn]
      have hm_le : (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
      exact iteratedFDeriv_add_apply
        (((hv_sm.sub hVc_sm).of_le hm_le).contDiffAt)
        ((hVc_sm.of_le hm_le).contDiffAt)
    have htri : ‖jet m (tr.v s) z‖ ≤ Ce * ν⁻¹ + CV := by
      rw [hjet_add]
      exact (norm_add_le _ _).trans (add_le_add herr_le hVc_le)
    calc ‖jet m (tr.v s) z‖
        ≤ Ce * ν⁻¹ + CV := htri
      _ ≤ polyP C_v 1 ν c := by
          unfold polyP
          dsimp [C_v]
          rw [pow_one]
          have : 0 ≤ Ce * (1 + c) := by positivity
          have : 0 ≤ CV * (c + ν⁻¹) := by positivity
          have : 0 ≤ C_ov * (1 + c + ν⁻¹) := by positivity
          linarith
  · -- Post-overlap (`s_c ≤ s`)
    let T : ℝ := ν * (s - s_c) / c ^ 2
    have hT_nn : 0 ≤ T := by
      dsimp [T]
      have : 0 ≤ s - s_c := sub_nonneg.2 hs_ge
      positivity
    have hs_eq : B0146.overlapAge ν c + c ^ 2 * T / ν = s := by
      dsimp [T, s_c]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    have hU_eq : overlapField ν c tr.v T = scaleField c (tr.v s) := by
      funext y
      simp [overlapField, scaleField, hs_eq]
    obtain ⟨_, hsup_U⟩ := hov ν hν hν_ov_le tr htr T hT_nn
    rw [hU_eq] at hsup_U
    have hsup_v : B0277.supNormD m (tr.v s) ≤ ENNReal.ofReal C_ov :=
      (PartI_T22.supNormD_le_supNormD_scaleField hc1 m (tr.v s)).trans hsup_U
    have hv_z : ‖jet m (tr.v s) z‖ ≤ C_ov :=
      norm_jet_le_of_supNormD_le m hC_ov.le hsup_v z
    calc ‖jet m (tr.v s) z‖
        ≤ C_ov := hv_z
      _ ≤ polyP C_v 1 ν c := by
          unfold polyP
          dsimp [C_v]
          rw [pow_one]
          have : 0 ≤ (Ce + CV) * (1 + c + ν⁻¹) := by positivity
          have : 0 ≤ C_ov * (c + ν⁻¹) := by positivity
          linarith

/-- Uniform global polynomial bound on `|B0151.derivWord w (Cyl.curl (tr.v s)) z|` for every
spatial word `w : List Bool` and every `s > 0`, `z : Plane`. -/
theorem train_curl_derivWord_sup_bound (ρ : ℝ) (hρ : 1 / 2 < ρ) (w : List Bool) :
    ∃ C_w ν₀ : ℝ, 0 < C_w ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            |B0151.derivWord w (Cyl.curl (tr.v s)) z| ≤ polyP C_w 1 ν (trainPeriod ρ ν) := by
  obtain ⟨C_cb, hC_cb, hcb⟩ := curlJetBound_proof w.length
  obtain ⟨C_v, ν₀, hC_v, hν₀, hv⟩ := train_v_jet_sup_bound ρ hρ (w.length + 1)
  let C_w : ℝ := (C_cb + 1) * C_v
  have hC_w : 0 < C_w := by positivity
  refine ⟨C_w, ν₀, hC_w, hν₀, fun ν hν hν_le tr htr s hs z => ?_⟩
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs.le
  have hcurl_sm : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := contDiff_curl_of_contDiff hv_sm
  have h1 := (cylJetWord_proof (Cyl.curl (tr.v s)) hcurl_sm w.length z).1 w rfl
  have h2 := hcb (tr.v s) hv_sm z
  have h3 : ‖iteratedFDeriv ℝ (w.length + 1) (tr.v s) z‖ ≤
      polyP C_v 1 ν (trainPeriod ρ ν) := hv ν hν hν_le tr htr s hs z
  calc |B0151.derivWord w (Cyl.curl (tr.v s)) z|
      ≤ ‖iteratedFDeriv ℝ w.length (Cyl.curl (tr.v s)) z‖ := h1
    _ ≤ C_cb * ‖iteratedFDeriv ℝ (w.length + 1) (tr.v s) z‖ := h2
    _ ≤ (C_cb + 1) * ‖iteratedFDeriv ℝ (w.length + 1) (tr.v s) z‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ (C_cb + 1) * polyP C_v 1 ν (trainPeriod ρ ν) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = polyP C_w 1 ν (trainPeriod ρ ν) := by
        unfold polyP
        dsimp [C_w]
        ring

/-- **1D Landau-Kolmogorov ray inequality (`deriv_abs_le_three_sqrt_of_ray`)**:
for any smooth `φ : ℝ → ℝ` and `A, B > 0`, setting `h = √(A / B) > 0`, if `|φ 0| ≤ A`,
`|φ h| ≤ A`, and `|deriv (deriv φ) t| ≤ B` for all `t ∈ [0, h]`, then
`|deriv φ 0| ≤ 3 * √(A * B)`. -/
theorem deriv_abs_le_three_sqrt_of_ray {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (h0 : |φ 0| ≤ A) (hh : |φ (Real.sqrt (A / B))| ≤ A)
    (h2 : ∀ t ∈ Icc (0 : ℝ) (Real.sqrt (A / B)), |deriv (deriv φ) t| ≤ B) :
    |deriv φ 0| ≤ 3 * Real.sqrt (A * B) := by
  set h : ℝ := Real.sqrt (A / B)
  have hh_pos : 0 < h := Real.sqrt_pos.2 (div_pos hA hB)
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdφ_cd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdφ_diff : Differentiable ℝ (deriv φ) := hdφ_cd.differentiable (by simp)
  obtain ⟨c₁, ⟨hc₁_pos, hc₁_lt⟩, hc₁_eq⟩ := exists_deriv_eq_slope φ hh_pos
    hφ_diff.continuous.continuousOn hφ_diff.differentiableOn
  obtain ⟨c₂, ⟨hc₂_pos, hc₂_lt⟩, hc₂_eq⟩ := exists_deriv_eq_slope (deriv φ) hc₁_pos
    hdφ_diff.continuous.continuousOn hdφ_diff.differentiableOn
  rw [sub_zero] at hc₁_eq hc₂_eq
  have hd0_eq : deriv φ 0 = (φ h - φ 0) / h - c₁ * deriv (deriv φ) c₂ := by
    have hc₁_ne : c₁ ≠ 0 := hc₁_pos.ne'
    have hsub : deriv φ c₁ - deriv φ 0 = c₁ * deriv (deriv φ) c₂ := by
      rw [hc₂_eq, mul_div_cancel₀ _ hc₁_ne]
    linarith
  have hslope_abs : |(φ h - φ 0) / h| ≤ 2 * A / h := by
    rw [abs_div, abs_of_pos hh_pos]
    have hnum : |φ h - φ 0| ≤ 2 * A := by
      calc |φ h - φ 0|
          ≤ |φ h| + |φ 0| := abs_sub _ _
        _ ≤ A + A := add_le_add hh h0
        _ = 2 * A := by ring
    exact div_le_div_of_nonneg_right hnum hh_pos.le
  have hc₂_mem : c₂ ∈ Icc (0 : ℝ) h := ⟨hc₂_pos.le, hc₂_lt.le.trans hc₁_lt.le⟩
  have hrem_abs : |c₁ * deriv (deriv φ) c₂| ≤ B * h := by
    rw [abs_mul, abs_of_pos hc₁_pos, mul_comm B h]
    exact mul_le_mul hc₁_lt.le (h2 c₂ hc₂_mem) (abs_nonneg _) hh_pos.le
  have hbound : |deriv φ 0| ≤ 2 * A / h + B * h := by
    rw [hd0_eq]
    exact (abs_sub _ _).trans (add_le_add hslope_abs hrem_abs)
  have halg : 2 * A / h + B * h = 3 * Real.sqrt (A * B) := by
    set sa : ℝ := Real.sqrt A
    set sb : ℝ := Real.sqrt B
    have hsa_ne : sa ≠ 0 := (Real.sqrt_pos.2 hA).ne'
    have hsb_ne : sb ≠ 0 := (Real.sqrt_pos.2 hB).ne'
    have hh_eq : h = sa / sb := Real.sqrt_div hA.le B
    have hAB_eq : Real.sqrt (A * B) = sa * sb := Real.sqrt_mul hA.le B
    have hA_eq : A = sa * sa := (Real.mul_self_sqrt hA.le).symm
    have hB_eq : B = sb * sb := (Real.mul_self_sqrt hB.le).symm
    calc 2 * A / h + B * h
        = 2 * (sa * sa) / (sa / sb) + (sb * sb) * (sa / sb) := by
          rw [hh_eq, hA_eq, hB_eq]
      _ = 3 * (sa * sb) := by
          field_simp
          ring
      _ = 3 * Real.sqrt (A * B) := by
          rw [hAB_eq]
  exact hbound.trans_eq halg

/-- Horizontal ray `t ↦ g (z.1 + t, z.2)`. -/
def rayQ (g : Plane → ℝ) (z : Plane) (t : ℝ) : ℝ :=
  g (z.1 + t, z.2)

theorem contDiff_rayQ {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    ContDiff ℝ ∞ (rayQ g z) := by
  unfold rayQ
  exact hg.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const)

theorem deriv_rayQ_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    deriv (rayQ g z) = rayQ (Cyl.partialQ g) z := by
  funext t
  have hslice : ContDiff ℝ ∞ (fun q : ℝ => g (q, z.2)) :=
    hg.comp (contDiff_id.prodMk contDiff_const)
  have hd_inner : HasDerivAt (fun s : ℝ => z.1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add z.1
  have hd_outer : HasDerivAt (fun q : ℝ => g (q, z.2))
      (Cyl.partialQ g (z.1 + t, z.2)) (z.1 + t) :=
    (hslice.differentiable (by simp) (z.1 + t)).hasDerivAt
  have hd := hd_outer.comp t hd_inner
  exact hd.deriv.trans (mul_one _)

/-- Outward vertical ray `t ↦ g (z.1, z.2 + τ * t)`. -/
def rayEta (g : Plane → ℝ) (z : Plane) (τ t : ℝ) : ℝ :=
  g (z.1, z.2 + τ * t)

theorem contDiff_rayEta {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) (τ : ℝ) :
    ContDiff ℝ ∞ (rayEta g z τ) := by
  unfold rayEta
  exact hg.comp (contDiff_const.prodMk (contDiff_const.add (contDiff_const.mul contDiff_id)))

theorem deriv_rayEta_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) (τ : ℝ) :
    deriv (rayEta g z τ) = fun t => τ * rayEta (Cyl.partialEta g) z τ t := by
  funext t
  have hslice : ContDiff ℝ ∞ (fun η : ℝ => g (z.1, η)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hd_inner : HasDerivAt (fun s : ℝ => z.2 + τ * s) τ t := by
    simpa using ((hasDerivAt_id t).const_mul τ).const_add z.2
  have hd_outer : HasDerivAt (fun η : ℝ => g (z.1, η))
      (Cyl.partialEta g (z.1, z.2 + τ * t)) (z.2 + τ * t) :=
    (hslice.differentiable (by simp) (z.2 + τ * t)).hasDerivAt
  have hd := hd_outer.comp t hd_inner
  exact hd.deriv.trans (mul_comm _ _)

theorem deriv2_rayEta_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) {τ : ℝ}
    (hτ : τ ^ 2 = 1) :
    deriv (deriv (rayEta g z τ)) = rayEta (Cyl.partialEta (Cyl.partialEta g)) z τ := by
  have hg1 : ContDiff ℝ ∞ (Cyl.partialEta g) := B0151.contDiff_derivWord hg [false]
  rw [deriv_rayEta_eq hg z τ]
  funext t
  rw [deriv_const_mul _ ((contDiff_rayEta hg1 z τ).differentiable (by simp) t),
    deriv_rayEta_eq hg1 z τ]
  have hτ2 : τ * (τ * rayEta (Cyl.partialEta (Cyl.partialEta g)) z τ t) =
      τ ^ 2 * rayEta (Cyl.partialEta (Cyl.partialEta g)) z τ t := by ring
  rw [hτ2, hτ, one_mul]

/-- Outward sign choice `τ = ±1` such that `|η + τ * t| = |η| + t` for all `t ≥ 0`. -/
theorem exists_outward_sign (η : ℝ) :
    ∃ τ : ℝ, τ ^ 2 = 1 ∧ |τ| = 1 ∧ ∀ t : ℝ, 0 ≤ t → |η| ≤ |η + τ * t| := by
  rcases le_total 0 η with hη | hη
  · refine ⟨1, by norm_num, by norm_num, fun t ht => ?_⟩
    rw [one_mul, abs_of_nonneg hη, abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨-1, by norm_num, by norm_num, fun t ht => ?_⟩
    have h1 : η + -1 * t ≤ 0 := by linarith
    rw [abs_of_nonpos hη, abs_of_nonpos h1]
    linarith

/-- Monotonicity of the Gaussian factor `exp(-(b * (max (|η| - K) 0)² / D))` along `|η| ≤ |η'|`. -/
theorem gaussian_tail_antitone_abs {b K D η η' : ℝ} (hb : 0 < b) (hD : 0 < D)
    (hη : |η| ≤ |η'|) :
    Real.exp (-(b * (max (|η'| - K) 0) ^ 2 / D)) ≤
      Real.exp (-(b * (max (|η| - K) 0) ^ 2 / D)) := by
  apply Real.exp_le_exp.2
  apply neg_le_neg
  have hmax : max (|η| - K) 0 ≤ max (|η'| - K) 0 :=
    max_le_max (sub_le_sub_right hη K) le_rfl
  have hsq : (max (|η| - K) 0) ^ 2 ≤ (max (|η'| - K) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hmax 2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hb.le) hD.le

/-- Algebraic combination `3 * √((polyP C₁ N₁ ν c * exp(-(b * d² / D))) * polyP C₂ N₂ ν c) ≤
polyP (3 * √(C₁ * C₂)) (N₁ + N₂) ν c * exp(-((b / 2) * d² / D))`. -/
theorem three_sqrt_polyP_exp_le {C₁ C₂ b d D ν c : ℝ} {N₁ N₂ : ℕ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hν : 0 < ν) (hc : 0 < c) :
    3 * Real.sqrt (polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D)) * polyP C₂ N₂ ν c) ≤
      polyP (3 * Real.sqrt (C₁ * C₂)) (N₁ + N₂) ν c *
        Real.exp (-((b / 2) * d ^ 2 / D)) := by
  set X : ℝ := 1 + c + ν⁻¹
  have hX1 : 1 ≤ X := by
    dsimp [X]
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hX_pow : X ^ (N₁ + N₂) ≤ X ^ (2 * (N₁ + N₂)) :=
    pow_le_pow_right₀ hX1 (by omega)
  have hexp_sq : Real.exp (-(b * d ^ 2 / D)) = (Real.exp (-((b / 2) * d ^ 2 / D))) ^ 2 := by
    rw [sq (Real.exp _), ← Real.exp_add]
    congr 1
    ring
  have hprod_le : polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D)) * polyP C₂ N₂ ν c ≤
      (Real.sqrt (C₁ * C₂) * X ^ (N₁ + N₂) * Real.exp (-((b / 2) * d ^ 2 / D))) ^ 2 := by
    calc polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D)) * polyP C₂ N₂ ν c
        = C₁ * C₂ * X ^ (N₁ + N₂) * Real.exp (-(b * d ^ 2 / D)) := by
          unfold polyP
          dsimp [X]
          rw [pow_add]
          ring
      _ ≤ C₁ * C₂ * X ^ (2 * (N₁ + N₂)) * Real.exp (-(b * d ^ 2 / D)) := by
          gcongr
      _ = (Real.sqrt (C₁ * C₂) * X ^ (N₁ + N₂) * Real.exp (-((b / 2) * d ^ 2 / D))) ^ 2 := by
          rw [hexp_sq, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul,
            mul_comm (N₁ + N₂) 2]
  have hrhs_nn : 0 ≤ Real.sqrt (C₁ * C₂) * X ^ (N₁ + N₂) * Real.exp (-((b / 2) * d ^ 2 / D)) := by
    positivity
  have hsqrt := Real.sqrt_le_sqrt hprod_le
  rw [Real.sqrt_sq hrhs_nn] at hsqrt
  calc 3 * Real.sqrt (polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D)) * polyP C₂ N₂ ν c)
      ≤ 3 * (Real.sqrt (C₁ * C₂) * X ^ (N₁ + N₂) * Real.exp (-((b / 2) * d ^ 2 / D))) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = polyP (3 * Real.sqrt (C₁ * C₂)) (N₁ + N₂) ν c *
          Real.exp (-((b / 2) * d ^ 2 / D)) := by
        unfold polyP
        dsimp [X]
        ring

/-- Single spatial derivative step (`b_dir :: w` from `w` and `b_dir :: b_dir :: w`) for a smooth
scalar field `g : Plane → ℝ`. -/
theorem spatial_step_gaussian_tail {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    {C₁ C₂ b K D ν c : ℝ} {N₁ N₂ : ℕ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hb : 0 < b) (hD : 0 < D) (hν : 0 < ν) (hc : 0 < c)
    (h0 : ∀ z : Plane,
      |g z| ≤ polyP C₁ N₁ ν c * Real.exp (-(b * (max (|z.2| - K) 0) ^ 2 / D)))
    (b_dir : Bool)
    (h2 : ∀ z : Plane, |B0151.derivWord [b_dir, b_dir] g z| ≤ polyP C₂ N₂ ν c)
    (z : Plane) :
    let d := max (|z.2| - K) 0
    |B0151.derivWord [b_dir] g z| ≤
      polyP (3 * Real.sqrt (C₁ * C₂)) (N₁ + N₂) ν c *
        Real.exp (-((b / 2) * d ^ 2 / D)) := by
  intro d
  set A : ℝ := polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D))
  set B : ℝ := polyP C₂ N₂ ν c
  have hA : 0 < A := by dsimp [A, polyP]; positivity
  have hB : 0 < B := by dsimp [B, polyP]; positivity
  cases b_dir with
  | true =>
    have hg1 : ContDiff ℝ ∞ (Cyl.partialQ g) := B0151.contDiff_derivWord hg [true]
    have hray_cd : ContDiff ℝ ∞ (rayQ g z) := contDiff_rayQ hg z
    have hray_0 : |rayQ g z 0| ≤ A := by
      unfold rayQ
      rw [add_zero]
      exact h0 z
    have hray_h : |rayQ g z (Real.sqrt (A / B))| ≤ A := by
      unfold rayQ
      exact h0 (z.1 + Real.sqrt (A / B), z.2)
    have hray_2 : ∀ t ∈ Icc (0 : ℝ) (Real.sqrt (A / B)),
        |deriv (deriv (rayQ g z)) t| ≤ B := by
      intro t _ht
      rw [deriv_rayQ_eq hg z, deriv_rayQ_eq hg1 z]
      exact h2 (z.1 + t, z.2)
    have hLK := deriv_abs_le_three_sqrt_of_ray hray_cd hA hB hray_0 hray_h hray_2
    rw [deriv_rayQ_eq hg z] at hLK
    unfold rayQ at hLK
    rw [add_zero] at hLK
    exact hLK.trans (three_sqrt_polyP_exp_le hC₁ hC₂ hν hc)
  | false =>
    obtain ⟨τ, hτ_sq, hτ_abs, hτ_out⟩ := exists_outward_sign z.2
    have hray_cd : ContDiff ℝ ∞ (rayEta g z τ) := contDiff_rayEta hg z τ
    have hray_0 : |rayEta g z τ 0| ≤ A := by
      unfold rayEta
      rw [mul_zero, add_zero]
      exact h0 z
    have hray_h : |rayEta g z τ (Real.sqrt (A / B))| ≤ A := by
      unfold rayEta
      have h_out : |z.2| ≤ |z.2 + τ * Real.sqrt (A / B)| :=
        hτ_out (Real.sqrt (A / B)) (Real.sqrt_nonneg _)
      have h_anti := gaussian_tail_antitone_abs hb hD (K := K) h_out
      calc |g (z.1, z.2 + τ * Real.sqrt (A / B))|
          ≤ polyP C₁ N₁ ν c *
              Real.exp (-(b * (max (|z.2 + τ * Real.sqrt (A / B)| - K) 0) ^ 2 / D)) :=
            h0 (z.1, z.2 + τ * Real.sqrt (A / B))
        _ ≤ polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / D)) :=
            mul_le_mul_of_nonneg_left h_anti (by unfold polyP; positivity)
    have hray_2 : ∀ t ∈ Icc (0 : ℝ) (Real.sqrt (A / B)),
        |deriv (deriv (rayEta g z τ)) t| ≤ B := by
      intro t _ht
      rw [deriv2_rayEta_eq hg z hτ_sq]
      exact h2 (z.1, z.2 + τ * t)
    have hLK := deriv_abs_le_three_sqrt_of_ray hray_cd hA hB hray_0 hray_h hray_2
    rw [deriv_rayEta_eq hg z τ] at hLK
    unfold rayEta at hLK
    dsimp only at hLK
    rw [mul_zero, add_zero, abs_mul, hτ_abs, one_mul] at hLK
    exact hLK.trans (three_sqrt_polyP_exp_le hC₁ hC₂ hν hc)

/-- By induction on the word `w : List Bool`, every spatial word derivative
`B0151.derivWord w (Cyl.curl (tr.v s))` satisfies the Gaussian transverse tail with the same
`C'` and `C₀ = 2` as `train_vorticity_gaussian_tail_zero_pointwise` and exponent
`b_w = (1 / 4) / 2 ^ w.length`. -/
theorem train_curl_derivWord_gaussian_tail (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ w : List Bool, ∃ C_w : ℝ, ∃ N_w : ℕ, ∃ ν_w : ℝ, 0 < C_w ∧ 0 < ν_w ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν_w →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → ∀ z : Plane,
              let c := trainPeriod ρ ν
              let d := max (|z.2| - C' / ν) 0
              |B0151.derivWord w (Cyl.curl (tr.v s)) z| ≤
                polyP C_w N_w ν c *
                  Real.exp (-(((1 / 4 : ℝ) / (2 : ℝ) ^ w.length) * d ^ 2 / (2 + ν * s))) := by
  obtain ⟨C', ν₀, hC', hν₀, hpt0⟩ := train_vorticity_gaussian_tail_zero_pointwise hOv ρ hρ
  refine ⟨C', hC', fun w => ?_⟩
  induction w with
  | nil =>
    refine ⟨40, 0, ν₀, by norm_num, hν₀, fun ν hν hν_le tr htr s hs z => ?_⟩
    simp only [List.length_nil, pow_zero, div_one, B0151.derivWord]
    have hpoly : polyP 40 0 ν (trainPeriod ρ ν) = 40 := by
      unfold polyP
      simp
    rw [hpoly]
    exact hpt0 ν hν hν_le tr htr s hs.le z
  | cons b_dir w ih =>
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hw⟩ := ih
    obtain ⟨C₂, ν₂, hC₂, hν₂, h2⟩ := train_curl_derivWord_sup_bound ρ hρ (b_dir :: b_dir :: w)
    refine ⟨3 * Real.sqrt (C₁ * C₂), N₁ + 1, min ν₁ ν₂, by positivity, lt_min hν₁ hν₂,
      fun ν hν hν_le tr htr s hs z => ?_⟩
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
    have hv_sm : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs.le
    have hcurl_sm : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := contDiff_curl_of_contDiff hv_sm
    have hg_sm : ContDiff ℝ ∞ (B0151.derivWord w (Cyl.curl (tr.v s))) :=
      B0151.contDiff_derivWord hcurl_sm w
    have hb_pos : 0 < (1 / 4 : ℝ) / (2 : ℝ) ^ w.length := by positivity
    have hD_pos : 0 < 2 + ν * s := by nlinarith
    have hstep := spatial_step_gaussian_tail hg_sm hC₁ hC₂ hb_pos hD_pos hν hc0
      (fun z' => hw ν hν hν₁_le tr htr s hs z') b_dir
      (fun z' => by
        rw [jsb_derivWord_append [b_dir, b_dir] w]
        exact h2 ν hν hν₂_le tr htr s hs z') z
    have hbw : ((1 / 4 : ℝ) / (2 : ℝ) ^ w.length) / 2 =
        (1 / 4 : ℝ) / (2 : ℝ) ^ (b_dir :: w).length := by
      simp only [List.length_cons, pow_succ]
      ring
    have hbw_eq : B0151.derivWord [b_dir] (B0151.derivWord w (Cyl.curl (tr.v s))) z =
        B0151.derivWord (b_dir :: w) (Cyl.curl (tr.v s)) z := by
      rw [jsb_derivWord_append [b_dir] w]
      rfl
    dsimp only at hstep ⊢
    rwa [hbw_eq, hbw] at hstep

/-- Finset combination of `train_curl_derivWord_gaussian_tail` over `wordsOfLength j`. -/
theorem finset_curl_derivWord_gaussian_tail (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (j : ℕ) (S : Finset (List Bool)), (∀ w ∈ S, w.length = j) →
        ∃ C_S : ℝ, ∃ N_S : ℕ, ∃ ν_S : ℝ, 0 < C_S ∧ 0 < ν_S ∧
          ∀ ν : ℝ, 0 < ν → ν ≤ ν_S →
            ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
              ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ w ∈ S,
                let c := trainPeriod ρ ν
                let d := max (|z.2| - C' / ν) 0
                |B0151.derivWord w (Cyl.curl (tr.v s)) z| ≤
                  polyP C_S N_S ν c *
                    Real.exp (-(((1 / 4 : ℝ) / (2 : ℝ) ^ j) * d ^ 2 / (2 + ν * s))) := by
  obtain ⟨C', hC', hword⟩ := train_curl_derivWord_gaussian_tail hOv ρ hρ
  refine ⟨C', hC', fun j S hS => ?_⟩
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, 0, 1, one_pos, one_pos, fun _ _ _ _ _ _ _ _ _ hw => (Finset.notMem_empty _ hw).elim⟩
  | @insert w₀ S hw₀ ih =>
    have hS' : ∀ w ∈ S, w.length = j := fun w hw => hS w (Finset.mem_insert_of_mem hw)
    have hw₀_len : w₀.length = j := hS w₀ (Finset.mem_insert_self w₀ S)
    obtain ⟨C_S, N_S, ν_S, hC_S, hν_S, h_ih⟩ := ih hS'
    obtain ⟨C₀, N₀, ν₀, hC₀, hν₀, h_w₀⟩ := hword w₀
    refine ⟨max C₀ C_S, max N₀ N_S, min ν₀ ν_S, lt_max_of_lt_left hC₀, lt_min hν₀ hν_S,
      fun ν hν hν_le tr htr s hs z w hw => ?_⟩
    let c := trainPeriod ρ ν
    have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
    have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 < ν⁻¹ := inv_pos.2 hν
      linarith
    rcases Finset.mem_insert.1 hw with rfl | hw_S
    · have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
      have h0 := h_w₀ ν hν hν₀_le tr htr s hs z
      dsimp only at h0 ⊢
      rw [hw₀_len] at h0
      have hpoly : polyP C₀ N₀ ν c ≤ polyP (max C₀ C_S) (max N₀ N_S) ν c := by
        unfold polyP
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
          (by positivity) (by positivity)
      exact h0.trans (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le)
    · have hνS_le : ν ≤ ν_S := hν_le.trans (min_le_right _ _)
      have h0 := h_ih ν hν hνS_le tr htr s hs z w hw_S
      dsimp only at h0 ⊢
      have hpoly : polyP C_S N_S ν c ≤ polyP (max C₀ C_S) (max N₀ N_S) ν c := by
        unfold polyP
        exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
          (by positivity) (by positivity)
      exact h0.trans (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le)

end PartI_T20

/-- **The `ℓ = 0`, arbitrary `j : ℕ` case of `TrainVorticityGaussianTail`
(`TrainVorticitySpatialJetTail`)** (source lines 483-497):
for every `ρ > 1/2` and spatial derivative order `j : ℕ`, `ageJet 0 j (fun r w => Cyl.curl (tr.v r) w)`
satisfies the Gaussian transverse tail with polynomial prefactor `polyP C N ν c`. -/
def TrainVorticitySpatialJetTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            let c := trainPeriod ρ ν
            let d := max (|z.2| - C' / ν) 0
            ‖ageJet 0 j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
              polyP C N ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))

/-- **Unconditional proof of `TrainVorticitySpatialJetTail` (`train_vorticity_spatial_jet_tail`)**
from `hOv : TrainOverlap` (source lines 483-497). -/
theorem train_vorticity_spatial_jet_tail (hOv : TrainOverlap) :
    TrainVorticitySpatialJetTail := by
  intro ρ hρ j
  obtain ⟨C', hC', hfin⟩ := PartI_T20.finset_curl_derivWord_gaussian_tail hOv ρ hρ
  obtain ⟨C_S, N_S, ν_S, hC_S, hν_S, hbound⟩ :=
    hfin j (wordsOfLength j) (fun _ hw => jsb_mem_wordsOfLength.1 hw)
  let b : ℝ := (1 / 4 : ℝ) / (2 : ℝ) ^ j
  have hb : 0 < b := by positivity
  let C : ℝ := (2 : ℝ) ^ j * C_S
  have hC : 0 < C := by positivity
  refine ⟨b, 2, C', hb, by norm_num, hC', C, N_S, ν_S, hC, hν_S,
    fun ν hν hν_le tr htr s hs z => ?_⟩
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  let d := max (|z.2| - C' / ν) 0
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := PartI_T20.contDiff_train_v_slice tr hs.le
  have hcurl_sm : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := PartI_T20.contDiff_curl_of_contDiff hv_sm
  have hjet_eq : ageJet 0 j (fun r w => Cyl.curl (tr.v r) w) s z =
      iteratedFDeriv ℝ j (Cyl.curl (tr.v s)) z := rfl
  rw [hjet_eq]
  have hpt := (cylJetWord_proof (Cyl.curl (tr.v s)) hcurl_sm j z).2
  let E : ℝ := polyP C_S N_S ν c * Real.exp (-(b * d ^ 2 / (2 + ν * s)))
  have hE_nn : 0 ≤ E := by dsimp [E, polyP]; positivity
  have hsum : ∑ w ∈ wordsOfLength j, |B0151.derivWord w (Cyl.curl (tr.v s)) z| ≤
      ((wordsOfLength j).card : ℝ) * E := by
    calc ∑ w ∈ wordsOfLength j, |B0151.derivWord w (Cyl.curl (tr.v s)) z|
        ≤ ∑ _w ∈ wordsOfLength j, E :=
          Finset.sum_le_sum (fun w hw => hbound ν hν hν_le tr htr s hs z w hw)
      _ = ((wordsOfLength j).card : ℝ) * E := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((wordsOfLength j).card : ℝ) ≤ (2 : ℝ) ^ j := by
    have hW : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
        _ = 2 ^ j := by simp
    exact_mod_cast hW
  calc ‖iteratedFDeriv ℝ j (Cyl.curl (tr.v s)) z‖
      ≤ ((wordsOfLength j).card : ℝ) * E := hpt.trans hsum
    _ ≤ (2 : ℝ) ^ j * E := mul_le_mul_of_nonneg_right hcard hE_nn
    _ = polyP C N_S ν c * Real.exp (-(b * d ^ 2 / (2 + ν * s))) := by
        dsimp [E, C, polyP]
        ring

/-! ### 4. Age-derivative induction leaf (`PartI:T20/1`) and conditional assembly -/

/-- **Leaf (`PartI:T20/1`): age-derivative induction from `ℓ = 0` (`TrainVorticityAgeDerivFromZero`)**
(source lines 523-526):
finite induction in the age derivative order `ℓ` via the differentiated vorticity equation
`∂_s ω = ν Δω - v · ∇ω` (where each differentiated term retains a spatial derivative of `ω`,
hence a Gaussian vorticity factor from `TrainVorticitySpatialJetTail`, multiplied by mixed
age/spatial derivatives of `v` bounded by `polyP C N ν c`) transfers the `ℓ = 0` Gaussian
transverse tail (`TrainVorticitySpatialJetTail`) to all mixed jets
`ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w)`. -/
def TrainVorticityAgeDerivFromZero : Prop :=
  TrainOverlap → TrainVorticitySpatialJetTail → TrainVorticityGaussianTail

/-- **Conditional assembly of `PartI:T20` (`train_vorticity_gaussian_tail_of`)**:
combines the unconditional proof of the `ℓ = 0` spatial-jet Gaussian vorticity tail
(`train_vorticity_spatial_jet_tail`, covering all `j : ℕ`) with the age-derivative induction leaf
`TrainVorticityAgeDerivFromZero` (`PartI:T20/1`). -/
theorem train_vorticity_gaussian_tail_of (hAge : TrainVorticityAgeDerivFromZero)
    (hOv : TrainOverlap) : TrainVorticityGaussianTail :=
  hAge hOv (train_vorticity_spatial_jet_tail hOv)

end UnforcedLeray.Short.PartI
