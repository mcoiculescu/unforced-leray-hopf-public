import UnforcedLeray.Short.PartI.Sub.PartI_T23
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive.MeanStreamDiffDuhamelL1.Helpers
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanCoeff
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemainderSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2_1_3.Leaf1
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `PartI:T23/2` (`Sub/PartI_T23_2.lean`): 1D heat Duhamel decomposition and `L^p` Taylor remainder bounds (`sct:expansion`)

Source of record: `the November 2 reference manuscript`, lines 448-459 and
528-539, in the proof of Lemma `sct:expansion`.

This module establishes the unconditional infrastructure and decomposition for `PartI:T23/2`:
1. **`PartI_T23.eLpNorm_pow_mul_le_of_pointwise`**: reduces any weighted `L^p(ℝ)` bound (`1 ≤ p ≤ ∞`)
   with exponent `α + (2p)⁻¹` at scale `R ≥ 1` to the two pointwise (`p = ∞`) bounds at weights `m`
   and `m + 2`.
2. **`PartI_T23.heatKernel1_weighted_jet_bound`**: uniform-in-`ν ∈ (0, 1]` weighted mixed-jet bound
   `(1 + |η|)^m |∂_η^b ∂_s^ℓ G_{ν s}(η)| ≤ polyP D (b + 1) ν c * s^{(m - b - 1)/2 - ℓ}` for `s ≥ 1`.
3. **`PartI_T23.meanCoeff_bound_of_fluctDecay`**: polynomial bound `|meanCoeff tr j| ≤ polyP C M ν c`
   for every `j : ℕ` from `TrainFluctuationDecay`.
4. **`PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay`**: all-order weighted mixed-derivative
   exponential decay `(1 + η²)^k |∂_η^b ∂_t^ℓ meanStress tr t η| ≤ polyP C M ν c * e^{-κ ν t / c²}`
   for all `t > 0` and `η ∈ ℝ` from `TrainFluctuationDecay`.
5. **1D heat Duhamel decomposition of `meanRemainder`**:
   * `meanDatumDuhamel`, `meanSourceDuhamel`, `meanDatumCoeff`, `meanSourceCoeff`,
     `meanDatumRemainder`, `meanSourceRemainder`.
   * `PartI_T23.meanDatumDuhamel_eq_vortexMeanStream`: proves that for `ν > 0`, `c ≥ 1`, and `s > 0`,
     `meanDatumDuhamel tr s η = vortexMeanStream ν c s η = -(8π c⁻¹) G_{1 + ν s}(η)` via the 1D
     Gaussian semigroup law `G_{ν s} * G_1 = G_{1 + ν s}` (`PartI_T23.integral_heatKernel1_conv`).
   * `PartI_T23.contDiffOn_meanDatumRemainder` and `PartI_T23.meanRemainder_slice_eq_add_of_duhamel`:
     proves joint `C^∞` smoothness of `meanDatumRemainder` and (under Duhamel) of
     `meanSourceRemainder` on `(0, ∞) × ℝ`, and additivity of all mixed `(s, η)` slice derivatives
     `∂_η^b ∂_s^ℓ (meanRemainder tr N) = ∂_η^b ∂_s^ℓ (meanDatumRemainder tr N) + ∂_η^b ∂_s^ℓ (meanSourceRemainder tr N)`.
6. **Three focused leaves (`PartI:T23/2/1`–`PartI:T23/2/3`) and conditional assembly**:
   * `TrainMeanStreamDuhamel` (`PartI:T23/2/1`),
   * `TrainMeanDatumRemainderBound` (`PartI:T23/2/2`),
   * `TrainMeanSourceRemainderBound` (`PartI:T23/2/3`),
   * `trainMeanRemainderPointwiseBound_of`, `trainMeanRemainderLpBound_of`,
     `trainMeanRemainderPointwiseBound_of_lp`, and `trainMeanRemainderLpBound_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

/-! ### 1. Definitions of the datum and source Duhamel parts of `meanRemainder` -/

/-- Homogeneous 1D heat evolution of the initial mean stream `S(0) = meanStream tr 0`
(source lines 410-412, 529-531):
`meanDatumDuhamel tr s η = ∫ ξ : ℝ, G_{ν s}(η - ξ) S(0, ξ) dξ`. -/
def meanDatumDuhamel {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  ∫ ξ : ℝ, heatKernel1 (ν * s) (η - ξ) * meanStream tr 0 ξ

/-- Inhomogeneous 1D heat Duhamel integral of the mean Reynolds stress `g = meanStress tr`
(source lines 410-412, 531-538):
`meanSourceDuhamel tr s η = ∫_0^s ∫_ℝ G_{ν(s - t)}(η - ξ) g(t, ξ) dξ dt`. -/
def meanSourceDuhamel {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, ∫ ξ : ℝ, heatKernel1 (ν * (s - t)) (η - ξ) * meanStress tr t ξ

/-- Initial-datum moment coefficient `a_{2j}^{(0)} = (∫ η^{2j} S(0, η) dη) / (2j)!`
(first summand of `meanCoeff`, source line 453). -/
def meanDatumCoeff {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) : ℝ :=
  (∫ η : ℝ, η ^ (2 * j) * meanStream tr 0 η) / ((2 * j).factorial : ℝ)

/-- Source moment coefficient
`a_{2j}^{(g)} = ∫_0^∞ ∑_{k+ℓ=j} (-(ν t))^ℓ / (ℓ! (2k)!) (∫ η^{2k} g(t, η) dη) dt`
(second summand of `meanCoeff`, source lines 454-456). -/
def meanSourceCoeff {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
    ((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
      ∫ η : ℝ, η ^ (2 * kl.1) * meanStress tr t η

/-- Order-`N` Taylor remainder of the initial-datum heat evolution `meanDatumDuhamel`
(source lines 451-453, 529-535):
`R_N^{(0)}(s, η) = meanDatumDuhamel tr s η - ∑_{j=0}^N a_{2j}^{(0)} ∂_η^{2j} G_{ν s}(η)`. -/
def meanDatumRemainder {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (s η : ℝ) : ℝ :=
  meanDatumDuhamel tr s η -
    ∑ j ∈ Finset.range (N + 1), meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

/-- Order-`N` Taylor remainder of the inhomogeneous source Duhamel integral `meanSourceDuhamel`
(source lines 451-456, 531-538):
`R_N^{(g)}(s, η) = meanSourceDuhamel tr s η - ∑_{j=0}^N a_{2j}^{(g)} ∂_η^{2j} G_{ν s}(η)`. -/
def meanSourceRemainder {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (s η : ℝ) : ℝ :=
  meanSourceDuhamel tr s η -
    ∑ j ∈ Finset.range (N + 1), meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

namespace PartI_T23

/-! ### 2. Reduction of weighted `L^p(ℝ)` bounds (`1 ≤ p ≤ ∞`) to pointwise bounds -/

/-- The `L^p(ℝ)` norm (`1 ≤ p ≤ ∞`) of `η ↦ (1 + (η / √R)²)⁻¹` for `R ≥ 1` is at most
`π * R^{(2p)⁻¹}`. -/
theorem eLpNorm_inv_one_add_div_sq_le {R : ℝ} (hR : 1 ≤ R) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun η : ℝ => (1 + (η / Real.sqrt R) ^ 2)⁻¹) p volume ≤
      ENNReal.ofReal (Real.pi * R ^ (p.toReal⁻¹ / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hsqR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hpi1 : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
  by_cases htop : p = ⊤
  · subst htop
    simp only [ENNReal.toReal_top, inv_zero, zero_div, Real.rpow_zero, mul_one]
    rw [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (1 + (η / Real.sqrt R) ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [sq_nonneg (η / Real.sqrt R)])
    exact h1.trans hpi1
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hq1 : 1 ≤ p.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono htop hp
    have hq0 : 0 < p.toReal := lt_of_lt_of_le one_pos hq1
    have hqinv_nn : 0 ≤ p.toReal⁻¹ := inv_nonneg.2 hq0.le
    have hqinv_le : p.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    rw [eLpNorm_eq_eLpNorm' hp0 htop, eLpNorm']
    have hpt : ∀ η : ℝ, ‖(1 + (η / Real.sqrt R) ^ 2)⁻¹‖ₑ ^ p.toReal ≤
        ENNReal.ofReal ((1 + (η / Real.sqrt R) ^ 2)⁻¹) := by
      intro η
      have hden : 1 ≤ 1 + (η / Real.sqrt R) ^ 2 := by linarith [sq_nonneg (η / Real.sqrt R)]
      have hinv_pos : 0 < (1 + (η / Real.sqrt R) ^ 2)⁻¹ := inv_pos.2 (by linarith)
      have hinv_le1 : (1 + (η / Real.sqrt R) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
      rw [Real.enorm_eq_ofReal hinv_pos.le, ENNReal.ofReal_rpow_of_pos hinv_pos]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_le_one hinv_pos.le hinv_le1 hq1)
    have hint : Integrable (fun η : ℝ => (1 + (η / Real.sqrt R) ^ 2)⁻¹) volume := by
      have h := integrable_inv_one_add_sq.comp_div hsqR.ne'
      exact h
    have hval : ∫ η : ℝ, (1 + (η / Real.sqrt R) ^ 2)⁻¹ = Real.sqrt R * Real.pi := by
      have h := Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) (Real.sqrt R)
      rw [abs_of_pos hsqR, smul_eq_mul, integral_univ_inv_one_add_sq] at h
      exact h
    have hlint : (∫⁻ η : ℝ, ‖(1 + (η / Real.sqrt R) ^ 2)⁻¹‖ₑ ^ p.toReal) ≤
        ENNReal.ofReal (Real.sqrt R * Real.pi) := by
      calc (∫⁻ η : ℝ, ‖(1 + (η / Real.sqrt R) ^ 2)⁻¹‖ₑ ^ p.toReal)
          ≤ ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt R) ^ 2)⁻¹) := lintegral_mono hpt
        _ = ENNReal.ofReal (∫ η : ℝ, (1 + (η / Real.sqrt R) ^ 2)⁻¹) :=
            (ofReal_integral_eq_lintegral_ofReal hint
              (Eventually.of_forall fun η => by positivity)).symm
        _ = ENNReal.ofReal (Real.sqrt R * Real.pi) := by rw [hval]
    calc (∫⁻ η : ℝ, ‖(1 + (η / Real.sqrt R) ^ 2)⁻¹‖ₑ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (ENNReal.ofReal (Real.sqrt R * Real.pi)) ^ (1 / p.toReal) :=
          ENNReal.rpow_le_rpow hlint (by positivity)
      _ = ENNReal.ofReal ((Real.sqrt R * Real.pi) ^ p.toReal⁻¹) := by
          rw [one_div, ENNReal.ofReal_rpow_of_pos (by positivity)]
      _ ≤ ENNReal.ofReal (Real.pi * R ^ (p.toReal⁻¹ / 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.mul_rpow hsqR.le Real.pi_pos.le, Real.sqrt_eq_rpow,
            ← Real.rpow_mul hR0.le, show (1 / 2 : ℝ) * p.toReal⁻¹ = p.toReal⁻¹ / 2 by ring,
            mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hR0.le _)
          calc Real.pi ^ p.toReal⁻¹ ≤ Real.pi ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hpi1 hqinv_le
            _ = Real.pi := Real.rpow_one Real.pi

/-- **Pointwise-to-`L^p(ℝ)` reduction (`1 ≤ p ≤ ∞`)**: if `|η|^m |F η| ≤ A₀ R^α` and
`|η|^{m+2} |F η| ≤ A₂ R^{α+1}` for all `η ∈ ℝ` with `R ≥ 1`, then
`‖η ↦ η^m F(η)‖_{L^p(ℝ)} ≤ π (A₀ + A₂) R^{α + (2p)⁻¹}`. -/
theorem eLpNorm_pow_mul_le_of_pointwise (F : ℝ → ℝ) (m : ℕ) {R α A₀ A₂ : ℝ}
    (hR : 1 ≤ R) (hA₀ : 0 ≤ A₀) (hA₂ : 0 ≤ A₂) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h0 : ∀ η : ℝ, |η| ^ m * |F η| ≤ A₀ * R ^ α)
    (h2 : ∀ η : ℝ, |η| ^ (m + 2) * |F η| ≤ A₂ * R ^ (α + 1)) :
    eLpNorm (fun η : ℝ => η ^ m * F η) p volume ≤
      ENNReal.ofReal (Real.pi * (A₀ + A₂) * R ^ (α + p.toReal⁻¹ / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hpt : ∀ η : ℝ, ‖η ^ m * F η‖ ≤
      ((A₀ + A₂) * R ^ α) * ‖(1 + (η / Real.sqrt R) ^ 2)⁻¹‖ := by
    intro η
    have hden : 0 < 1 + (η / Real.sqrt R) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.norm_of_nonneg (inv_nonneg.2 hden.le),
      le_mul_inv_iff₀ hden]
    have hsq : (η / Real.sqrt R) ^ 2 = R⁻¹ * |η| ^ 2 := by
      rw [div_pow, Real.sq_sqrt hR0.le, sq_abs, div_eq_inv_mul]
    have h2' : (η / Real.sqrt R) ^ 2 * (|η| ^ m * |F η|) ≤ A₂ * R ^ α := by
      calc (η / Real.sqrt R) ^ 2 * (|η| ^ m * |F η|)
          = R⁻¹ * (|η| ^ (m + 2) * |F η|) := by
              rw [hsq, pow_add]
              ring
        _ ≤ R⁻¹ * (A₂ * R ^ (α + 1)) :=
              mul_le_mul_of_nonneg_left (h2 η) (inv_nonneg.2 hR0.le)
        _ = A₂ * R ^ α := by
              rw [Real.rpow_add hR0, Real.rpow_one]
              field_simp [hR0.ne']
    calc (|η| ^ m * |F η|) * (1 + (η / Real.sqrt R) ^ 2)
        = |η| ^ m * |F η| + (η / Real.sqrt R) ^ 2 * (|η| ^ m * |F η|) := by ring
      _ ≤ A₀ * R ^ α + A₂ * R ^ α := add_le_add (h0 η) h2'
      _ = (A₀ + A₂) * R ^ α := by ring
  have hmono : eLpNorm (fun η : ℝ => η ^ m * F η) p volume ≤
      eLpNorm (((A₀ + A₂) * R ^ α) • fun η : ℝ => (1 + (η / Real.sqrt R) ^ 2)⁻¹) p volume := by
    refine eLpNorm_mono fun η => ?_
    rw [Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (add_nonneg hA₀ hA₂) (Real.rpow_nonneg hR0.le _))]
    exact hpt η
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal
    (mul_nonneg (add_nonneg hA₀ hA₂) (Real.rpow_nonneg hR0.le _))] at hmono
  refine hmono.trans ((mul_le_mul_of_nonneg_left
    (eLpNorm_inv_one_add_div_sq_le hR hp) zero_le).trans ?_)
  rw [← ENNReal.ofReal_mul (mul_nonneg (add_nonneg hA₀ hA₂) (Real.rpow_nonneg hR0.le _))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Real.rpow_add hR0]
  ring

/-! ### 3. Uniform-in-`ν` weighted mixed-jet bound for `heatKernel1 (ν * r)` -/

/-- Parabolic `ν`-scaling of `heatKernel1`: `G_{ν r}(e) = (√ν)⁻¹ G_r((√ν)⁻¹ e)` for `ν, r > 0`. -/
theorem heatKernel1_nu_scale {ν : ℝ} (hν : 0 < ν) (r e : ℝ) :
    heatKernel1 (ν * r) e = (Real.sqrt ν)⁻¹ * heatKernel1 (1 * r) ((Real.sqrt ν)⁻¹ * e) := by
  unfold heatKernel1
  have h1 : 4 * Real.pi * (ν * r) = ν * (4 * Real.pi * (1 * r)) := by ring
  have h2 : -(((Real.sqrt ν)⁻¹ * e) ^ 2) / (4 * (1 * r)) = -(e ^ 2) / (4 * (ν * r)) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hν.le]
    field_simp [hν.ne']
  rw [h1, Real.sqrt_mul hν.le, mul_inv, h2]
  ring

/-- Uniform-in-`ν ∈ (0, 1]` weighted mixed-jet bound for `heatKernel1 (ν * r)`:
for every `m, b, ℓ : ℕ`, there exists `D > 0` such that for all `0 < ν ≤ 1`, `c ≥ 0`, `s ≥ 1`,
and `η ∈ ℝ`,
`(1 + |η|)^m |∂_η^b ∂_s^ℓ G_{ν s}(η)| ≤ polyP D (b + 1) ν c * s^{(m - b - 1)/2 - ℓ}`. -/
theorem heatKernel1_weighted_jet_bound (m b ℓ : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ν c : ℝ}, 0 < ν → ν ≤ 1 → 0 ≤ c → ∀ {s : ℝ}, 1 ≤ s → ∀ η : ℝ,
      (1 + |η|) ^ m * |iteratedDeriv b
          (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η| ≤
        polyP D (b + 1) ν c * s ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  obtain ⟨D₀, hD₀⟩ := _root_.heatKernelWeightedBound 1 one_pos m b ℓ
  refine ⟨max D₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro ν c hν hν1 hc s hs η
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hsqν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsqν1 : Real.sqrt ν ≤ 1 := by simpa using Real.sqrt_le_sqrt hν1
  have hinv_ge1 : 1 ≤ (Real.sqrt ν)⁻¹ := one_le_inv₀ hsqν |>.2 hsqν1
  have hr_eq : ∀ e : ℝ, iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s =
      (Real.sqrt ν)⁻¹ * iteratedDeriv ℓ (fun r => heatKernel1 (1 * r) ((Real.sqrt ν)⁻¹ * e)) s := by
    intro e
    have hfun : (fun r => heatKernel1 (ν * r) e) =
        fun r => (Real.sqrt ν)⁻¹ * heatKernel1 (1 * r) ((Real.sqrt ν)⁻¹ * e) :=
      funext fun r => heatKernel1_nu_scale hν r e
    rw [hfun, iteratedDeriv_const_mul_field]
  have hslice_smooth : ContDiff ℝ ∞
      (fun y : ℝ => iteratedDeriv ℓ (fun r => heatKernel1 (1 * r) y) s) := by
    have hH := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1
      (fun r y => heatKernel1 (1 * r) y)
      (UnforcedLeray.Short.PartIIa.heatKernel1_contDiffOn_scaled one_pos) ℓ
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => heatKernel1 (1 * r) x.2) x.1) ∘
          (fun y : ℝ => ((s, y) : ℝ × ℝ))) univ :=
      hH.comp (contDiffOn_univ.mpr (contDiff_const.prodMk contDiff_id)) (fun _ _ => ⟨hs0, trivial⟩)
    exact contDiffOn_univ.mp hcomp
  have hb_eq : iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) η =
      ((Real.sqrt ν)⁻¹) ^ (b + 1) *
        UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet
          (fun r y => heatKernel1 (1 * r) y) b ℓ s ((Real.sqrt ν)⁻¹ * η) := by
    have hfun : (fun e => iteratedDeriv ℓ (fun r => heatKernel1 (ν * r) e) s) =
        fun e => (Real.sqrt ν)⁻¹ *
          (fun y => iteratedDeriv ℓ (fun r => heatKernel1 (1 * r) y) s) ((Real.sqrt ν)⁻¹ * e) :=
      funext hr_eq
    rw [hfun, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_const_mul (hslice_smooth.of_le (by exact_mod_cast le_top)), pow_succ']
    unfold UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet
    ring
  rw [hb_eq, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hsqν) (b + 1))]
  have h1y : 1 + |η| ≤ 1 + |(Real.sqrt ν)⁻¹ * η| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hsqν)]
    nlinarith [abs_nonneg η]
  have h1y_pow : (1 + |η|) ^ m ≤ (1 + |(Real.sqrt ν)⁻¹ * η|) ^ m :=
    pow_le_pow_left₀ (by positivity) h1y m
  have hjet_bd := hD₀ s hs ((Real.sqrt ν)⁻¹ * η)
  rw [Real.norm_eq_abs] at hjet_bd
  have hν_inv_le : (Real.sqrt ν)⁻¹ ≤ 1 + c + ν⁻¹ := by
    have h1 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ :=
      inv_le_inv₀ hsqν hν |>.2 (by nlinarith [Real.sq_sqrt hν.le, hsqν1])
    linarith
  have hpow_ν : ((Real.sqrt ν)⁻¹) ^ (b + 1) ≤ (1 + c + ν⁻¹) ^ (b + 1) :=
    pow_le_pow_left₀ (by positivity) hν_inv_le (b + 1)
  have hD_le : D₀ ≤ max D₀ 1 := le_max_left _ _
  calc (1 + |η|) ^ m * (((Real.sqrt ν)⁻¹) ^ (b + 1) *
        |UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet
          (fun r y => heatKernel1 (1 * r) y) b ℓ s ((Real.sqrt ν)⁻¹ * η)|)
      = ((Real.sqrt ν)⁻¹) ^ (b + 1) *
          ((1 + |η|) ^ m *
            |UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet
              (fun r y => heatKernel1 (1 * r) y) b ℓ s ((Real.sqrt ν)⁻¹ * η)|) := by ring
    _ ≤ ((Real.sqrt ν)⁻¹) ^ (b + 1) *
          ((1 + |(Real.sqrt ν)⁻¹ * η|) ^ m *
            |UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet
              (fun r y => heatKernel1 (1 * r) y) b ℓ s ((Real.sqrt ν)⁻¹ * η)|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h1y_pow (abs_nonneg _)) (by positivity)
    _ ≤ ((Real.sqrt ν)⁻¹) ^ (b + 1) *
          (D₀ * s ^ (((m : ℝ) - b - 1) / 2 - ℓ)) :=
        mul_le_mul_of_nonneg_left hjet_bd (by positivity)
    _ ≤ (1 + c + ν⁻¹) ^ (b + 1) *
          (max D₀ 1 * s ^ (((m : ℝ) - b - 1) / 2 - ℓ)) := by
        refine mul_le_mul hpow_ν
          (mul_le_mul_of_nonneg_right hD_le (Real.rpow_nonneg hs0.le _))
          (le_trans (by positivity) hjet_bd) (by positivity)
    _ = polyP (max D₀ 1) (b + 1) ν c * s ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
        unfold polyP
        ring

/-! ### 4. Unconditional polynomial bound on `meanCoeff tr j` from `TrainFluctuationDecay` -/

/-- **Polynomial bound on `meanCoeff tr j`** from `TrainFluctuationDecay` (wrapping
`PartIIa.lateMeanCoeff_of` and `trainMeanEquations_proof`). -/
theorem meanCoeff_bound_of_fluctDecay (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        |meanCoeff tr j| ≤ polyP C M ν (trainPeriod ρ ν) := by
  obtain ⟨C₀, M, ν₀, hν₀, hbd⟩ :=
    UnforcedLeray.Short.PartIIa.lateMeanCoeff_of hFD trainMeanEquations_proof ρ j hρ
  refine ⟨max C₀ 1, M, ν₀, lt_max_of_lt_right one_pos, hν₀, ?_⟩
  intro ν hν hν_le tr htr
  have h := hbd ν hν hν_le tr htr
  unfold UnforcedLeray.Short.PartIIa.polyConst at h
  refine h.trans ?_
  unfold polyP trainPeriod
  have hX : 0 ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ M := by
    have : 0 ≤ ν ^ (-ρ) := Real.rpow_nonneg hν.le _
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX

/-! ### 5. Unconditional weighted mixed-derivative exponential decay of `meanStress` -/

/-- **All-order weighted mixed-derivative exponential decay of `meanStress`** from
`TrainFluctuationDecay` (source lines 397-404, 439-446, 528-551): for every `ρ > 1/2` and
`k, b, ℓ : ℕ`, there exist `C > 0`, `M : ℕ`, `κ > 0`, and `ν₀ > 0` such that for all
`0 < ν ≤ ν₀`, every `BUC` train `tr`, and all `t > 0`, `η ∈ ℝ`,
`(1 + η²)^k |∂_η^b ∂_t^ℓ meanStress tr t η| ≤ polyP C M ν c * exp (-(κ ν t / c²))`. -/
theorem meanStress_weighted_jet_decay_of_fluctDecay (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (k b ℓ : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ κ ν₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ t : ℝ, 0 < t → ∀ η : ℝ,
          (1 + η ^ 2) ^ k *
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) t) η| ≤
              polyP C M ν c * Real.exp (-(κ * ν * t / c ^ 2)) := by
  let hSm := UnforcedLeray.Short.PartIIa.meanStressSmooth_of hmeanContDiff
  let hMix := UnforcedLeray.Short.PartIIa.hmeanMixedDeriv_of
    UnforcedLeray.Short.PartIIa.ageDerivSmooth
    (UnforcedLeray.Short.PartIIa.hmeanAgeIter_of hmeanDerivS
      UnforcedLeray.Short.PartIIa.ageDerivSmooth)
    UnforcedLeray.Short.PartIIa.hmeanEtaDeriv
  let hDF := UnforcedLeray.Short.PartIIa.meanStressDerivForm_of
    trainMeanEquations_proof UnforcedLeray.Short.PartIIa.hmeanMulFluct hMix hSm
  let hL := UnforcedLeray.Short.PartIIa.mixedLeibniz_of UnforcedLeray.Short.PartIIa.ageDerivSmooth
  let hSlice := UnforcedLeray.Short.PartIIa.fluctVelSliceBound_of hFD
    (UnforcedLeray.Short.PartIIa.sliceJetBound_of UnforcedLeray.Short.PartIIa.profileDict) hSm
  have hterm : ∀ p ∈ UnforcedLeray.Short.PartIIa.meanPairs b ℓ,
      ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
        ∀ j : UnforcedLeray.Short.PartIIa.MeanIdx ρ, (0 < j.1 ∧ 0 < j.2.2.2.2) → j.1 ≤ ν₀ →
          (1 + j.2.2.2.1 ^ 2) ^ k *
            (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                (fun r => hfluct (j.1 ^ (-ρ)) (fun w => j.2.1.1.v r w 0) (j.2.2.1, e))
                j.2.2.2.2) j.2.2.2.1| *
              |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                (fun r => hfluct (j.1 ^ (-ρ)) (fun w => j.2.1.1.v r w 1) (j.2.2.1, e))
                j.2.2.2.2) j.2.2.2.1|) ≤
            UnforcedLeray.Short.PartIIa.polyConst C N j.1 (j.1 ^ (-ρ)) *
              Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)) := by
    intro p _
    obtain ⟨C1, N1, κ1, ν1, hκ1, hν1, H1⟩ := hSlice ρ k p.1 p.2 hρ
    obtain ⟨C2, N2, κ2, ν2, hκ2, hν2, H2⟩ := hSlice ρ 0 (b - p.1) (ℓ - p.2) hρ
    refine ⟨C1 * C2, N1 + N2, min κ1 κ2, min ν1 ν2, lt_min hκ1 hκ2, lt_min hν1 hν2, ?_⟩
    rintro ⟨ν, ⟨tr, hb⟩, q, η, t⟩ ⟨hν, ht⟩ hν_le
    have h1 := H1 ν hν (hν_le.trans (min_le_left _ _)) tr hb 0 q η t ht
    have h2 := H2 ν hν (hν_le.trans (min_le_right _ _)) tr hb 1 q η t ht
    rw [pow_zero, one_mul] at h2
    have hE1 : Real.exp (-(κ1 * ν * t / (ν ^ (-ρ)) ^ 2)) ≤
        Real.exp (-(min κ1 κ2 * ν * t / (ν ^ (-ρ)) ^ 2)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have : 0 ≤ ν * t := mul_nonneg hν.le ht.le
      nlinarith [min_le_left κ1 κ2]
    have hE2 : Real.exp (-(κ2 * ν * t / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.2
      have : 0 ≤ κ2 * ν * t / (ν ^ (-ρ)) ^ 2 := by positivity
      linarith
    have hP1_nn : 0 ≤ (1 + η ^ 2) ^ k *
        |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
          (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) t) η| := by positivity
    have hC1_nn : 0 ≤ UnforcedLeray.Short.PartIIa.polyConst C1 N1 ν (ν ^ (-ρ)) :=
      (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 (hP1_nn.trans h1)
    have hC2_nn : 0 ≤ UnforcedLeray.Short.PartIIa.polyConst C2 N2 ν (ν ^ (-ρ)) :=
      (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans h2)
    have h1' : (1 + η ^ 2) ^ k *
        |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
          (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) t) η| ≤
        UnforcedLeray.Short.PartIIa.polyConst C1 N1 ν (ν ^ (-ρ)) *
          Real.exp (-(min κ1 κ2 * ν * t / (ν ^ (-ρ)) ^ 2)) :=
      h1.trans (mul_le_mul_of_nonneg_left hE1 hC1_nn)
    have h2' : |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
          (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) t) η| ≤
        UnforcedLeray.Short.PartIIa.polyConst C2 N2 ν (ν ^ (-ρ)) := by
      calc _ ≤ UnforcedLeray.Short.PartIIa.polyConst C2 N2 ν (ν ^ (-ρ)) *
            Real.exp (-(κ2 * ν * t / (ν ^ (-ρ)) ^ 2)) := h2
        _ ≤ UnforcedLeray.Short.PartIIa.polyConst C2 N2 ν (ν ^ (-ρ)) * 1 :=
            mul_le_mul_of_nonneg_left hE2 hC2_nn
        _ = _ := mul_one _
    calc (1 + η ^ 2) ^ k *
          (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
              (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) t) η| *
            |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) t) η|)
        = ((1 + η ^ 2) ^ k *
            |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
              (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) t) η|) *
          |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) t) η| := by ring
      _ ≤ (UnforcedLeray.Short.PartIIa.polyConst C1 N1 ν (ν ^ (-ρ)) *
            Real.exp (-(min κ1 κ2 * ν * t / (ν ^ (-ρ)) ^ 2))) *
          UnforcedLeray.Short.PartIIa.polyConst C2 N2 ν (ν ^ (-ρ)) :=
          mul_le_mul h1' h2' (abs_nonneg _) (by positivity)
      _ = UnforcedLeray.Short.PartIIa.polyConst (C1 * C2) (N1 + N2) ν (ν ^ (-ρ)) *
            Real.exp (-(min κ1 κ2 * ν * t / (ν ^ (-ρ)) ^ 2)) := by
          unfold UnforcedLeray.Short.PartIIa.polyConst
          rw [pow_add]
          ring
  obtain ⟨C₀, M, κ, ν₀, hκ, hν₀, H⟩ :=
    UnforcedLeray.Short.PartIIa.finite_uniform
      (ι := UnforcedLeray.Short.PartIIa.MeanIdx ρ)
      (UnforcedLeray.Short.PartIIa.meanPairs b ℓ)
      (fun j => 0 < j.1 ∧ 0 < j.2.2.2.2)
      (fun j => j.1) (fun j => j.1 ^ (-ρ))
      (fun κ j => Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)))
      (fun κ j _ => (Real.exp_pos _).le)
      (fun κ κ' j hj _ hκκ' => by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have : 0 ≤ j.1 * j.2.2.2.2 := mul_nonneg hj.1.le hj.2.le
        nlinarith)
      (fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _⟩)
      (fun p => (b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ))
      (fun p j => (1 + j.2.2.2.1 ^ 2) ^ k *
        (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
            (fun r => hfluct (j.1 ^ (-ρ)) (fun w => j.2.1.1.v r w 0) (j.2.2.1, e))
            j.2.2.2.2) j.2.2.2.1| *
          |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
            (fun r => hfluct (j.1 ^ (-ρ)) (fun w => j.2.1.1.v r w 1) (j.2.2.1, e))
            j.2.2.2.2) j.2.2.2.1|))
      hterm
  refine ⟨max C₀ 1, M, κ, ν₀, lt_max_of_lt_right one_pos, hκ, hν₀, ?_⟩
  intro ν hν hν_le tr htr c t ht η
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  rw [hDF ν c hν hc0 tr htr b ℓ t η ht]
  dsimp only [c, trainPeriod] at tr htr hc0 ⊢
  have havg := UnforcedLeray.Short.PartIIa.avg_bound (c := ν ^ (-ρ)) (η := η) hc0
    (by positivity : 0 ≤ (1 + η ^ 2) ^ k)
    (fun q η' => iteratedDeriv b (fun e => iteratedDeriv ℓ
      (fun r => UnforcedLeray.Short.PartIIa.fluctProd tr r (q, e)) t) η')
    (fun q _ => by
      have hleib := UnforcedLeray.Short.PartIIa.leib_inst hL hSm ρ ν hν tr htr q t η ht b ℓ
      have hH := H ⟨ν, ⟨tr, htr⟩, q, η, t⟩ ⟨hν, ht⟩ hν_le
      dsimp only at hH
      rw [hleib]
      refine (UnforcedLeray.Short.PartIIa.abs_sum_mul_le
        (UnforcedLeray.Short.PartIIa.meanPairs b ℓ) ((1 + η ^ 2) ^ k) (by positivity) _
        (fun p => |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
          ((1 + η ^ 2) ^ k *
            (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) t) η| *
              |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) t) η|)))
        (fun p _ => by simp only [abs_mul]; ring_nf; exact le_rfl)).trans hH)
  refine havg.trans ?_
  unfold UnforcedLeray.Short.PartIIa.polyConst polyP
  have hX : 0 ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ M * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2)) := by
    have : 0 ≤ ν ^ (-ρ) := Real.rpow_nonneg hν.le _
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  calc C₀ * (1 + ν ^ (-ρ) + ν⁻¹) ^ M * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2))
      = C₀ * ((1 + ν ^ (-ρ) + ν⁻¹) ^ M * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2))) := by ring
    _ ≤ max C₀ 1 * ((1 + ν ^ (-ρ) + ν⁻¹) ^ M * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    _ = max C₀ 1 * (1 + ν ^ (-ρ) + ν⁻¹) ^ M * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2)) := by ring

/-! ### 6. 1D Gaussian semigroup law, `meanDatumDuhamel = vortexMeanStream`, and slice-derivative split -/

/-- Completing the square for `heatKernel1`:
`G_α(y - w) * G_β(w) = G_{α + β}(y) * G_{α β / (α + β)}(w - (β / (α + β)) y)` for `α, β > 0`. -/
theorem heatKernel1_product {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y w : ℝ) :
    heatKernel1 α (y - w) * heatKernel1 β w =
      heatKernel1 (α + β) y *
        heatKernel1 (α * β / (α + β)) (w - β / (α + β) * y) := by
  unfold heatKernel1
  have hab : 0 < α + β := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hab' := hab.ne'
  have hpre : (Real.sqrt (4 * Real.pi * α))⁻¹ * (Real.sqrt (4 * Real.pi * β))⁻¹ =
      (Real.sqrt (4 * Real.pi * (α + β)))⁻¹ *
        (Real.sqrt (4 * Real.pi * (α * β / (α + β))))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  have hexp : -((y - w) ^ 2) / (4 * α) + -(w ^ 2) / (4 * β) =
      -(y ^ 2) / (4 * (α + β)) +
        -((w - β / (α + β) * y) ^ 2) / (4 * (α * β / (α + β))) := by
    field_simp
    ring
  calc _ = ((Real.sqrt (4 * Real.pi * α))⁻¹ * (Real.sqrt (4 * Real.pi * β))⁻¹) *
        Real.exp (-((y - w) ^ 2) / (4 * α) + -(w ^ 2) / (4 * β)) := by
          rw [Real.exp_add]; ring
    _ = _ := by rw [hpre, hexp, Real.exp_add]; ring

/-- Normalization `∫_ℝ G_a(η) dη = 1` for `a > 0`. -/
theorem integral_heatKernel1_eq_one {a : ℝ} (ha : 0 < a) :
    ∫ η : ℝ, heatKernel1 a η = 1 := by
  have hfun : heatKernel1 a = fun η : ℝ =>
      (Real.sqrt (4 * Real.pi * a))⁻¹ * Real.exp (-(4 * a)⁻¹ * η ^ 2) := by
    funext η
    unfold heatKernel1
    rw [show -(η ^ 2) / (4 * a) = -(4 * a)⁻¹ * η ^ 2 by ring]
  rw [hfun, integral_const_mul, integral_gaussian,
    show Real.pi / (4 * a)⁻¹ = 4 * Real.pi * a by field_simp,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne']

/-- 1D heat semigroup convolution identity: `∫_ℝ G_α(y - w) G_β(w) dw = G_{α + β}(y)` for `α, β > 0`. -/
theorem integral_heatKernel1_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (y : ℝ) :
    ∫ w : ℝ, heatKernel1 α (y - w) * heatKernel1 β w = heatKernel1 (α + β) y := by
  simp_rw [heatKernel1_product hα hβ y]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_heatKernel1_eq_one (by positivity),
    mul_one]

/-- For `ν > 0`, `c ≥ 1`, and `s > 0`, the initial-datum heat convolution
`meanDatumDuhamel tr s η = ∫ ξ, G_{ν s}(η - ξ) S(0, ξ) dξ` equals the closed-form Gaussian
`vortexMeanStream ν c s η = -(8π c⁻¹) G_{1 + ν s}(η)`. -/
theorem meanDatumDuhamel_eq_vortexMeanStream {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    meanDatumDuhamel tr s η = vortexMeanStream ν c s η := by
  unfold meanDatumDuhamel
  have hfun : (fun ξ : ℝ => heatKernel1 (ν * s) (η - ξ) * meanStream tr 0 ξ) =
      fun ξ : ℝ => -(8 * Real.pi * c⁻¹) * (heatKernel1 (ν * s) (η - ξ) * heatKernel1 1 ξ) := by
    funext ξ
    rw [meanStream_zero_eq_vortexMeanStream hc1 tr ξ]
    unfold vortexMeanStream width
    simp only [mul_zero, add_zero]
    ring
  rw [hfun, integral_const_mul, integral_heatKernel1_conv (mul_pos hν hs) one_pos η]
  unfold vortexMeanStream width
  rw [add_comm]

/-- Joint `C^∞` smoothness of `meanDatumDuhamel tr` on `(0, ∞) × ℝ` for `ν > 0` and `c ≥ 1`. -/
theorem contDiffOn_meanDatumDuhamel {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanDatumDuhamel tr x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => vortexMeanStream ν c x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (contDiffOn_vortexMeanStream hν).mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  exact hv.congr fun x hx => meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hx.1 x.2

/-- Joint `C^∞` smoothness of `meanDatumRemainder tr N` on `(0, ∞) × ℝ` for `ν > 0` and `c ≥ 1`. -/
theorem contDiffOn_meanDatumRemainder {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (N : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanDatumRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hD := contDiffOn_meanDatumDuhamel hν hc1 tr
  have hsum : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1),
        meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * x.1)) x.2)
      (Ioi 0 ×ˢ univ) :=
    ContDiffOn.sum fun j _ =>
      contDiffOn_const.mul (UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν hν (2 * j))
  exact (hD.sub hsum).congr fun x _ => rfl

/-- `meanCoeff tr j` decomposes as `meanDatumCoeff tr j + meanSourceCoeff tr j`. -/
theorem meanCoeff_eq_add {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) :
    meanCoeff tr j = meanDatumCoeff tr j + meanSourceCoeff tr j := rfl

/-- Under the Duhamel decomposition `meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e`,
`meanRemainder tr N r e` decomposes as `meanDatumRemainder tr N r e + meanSourceRemainder tr N r e`. -/
theorem meanRemainder_eq_add_of_duhamel {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) {r e : ℝ}
    (hD : meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e) :
    meanRemainder tr N r e = meanDatumRemainder tr N r e + meanSourceRemainder tr N r e := by
  unfold meanRemainder meanDatumRemainder meanSourceRemainder
  rw [hD]
  have hsum : (∑ j ∈ Finset.range (N + 1),
        meanCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e) =
      (∑ j ∈ Finset.range (N + 1),
        meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e) +
      (∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [meanCoeff_eq_add, add_mul]
  linarith

/-- Additivity of nested slice derivatives `∂_η^b ∂_s^ℓ (A + B)` at `s > 0` for jointly `C^∞`
functions `A, B` on `(0, ∞) × ℝ`. -/
theorem iteratedDeriv_slice_add_aux {A B : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => A x.1 x.2) (Ioi 0 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => B x.1 x.2) (Ioi 0 ×ˢ univ))
    (b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => A r e + B r e) s) η =
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => A r e) s) η +
        iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => B r e) s) η := by
  have hr_eq : ∀ e : ℝ, iteratedDeriv ℓ (fun r => A r e + B r e) s =
      iteratedDeriv ℓ (fun r => A r e) s + iteratedDeriv ℓ (fun r => B r e) s := by
    intro e
    have hφ : ContDiff ℝ ∞ (fun r : ℝ => ((r, e) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    have hA_r : ContDiffOn ℝ ∞ (fun r : ℝ => A r e) (Ioi 0) :=
      hA.comp hφ.contDiffOn (fun r hr => ⟨hr, trivial⟩)
    have hB_r : ContDiffOn ℝ ∞ (fun r : ℝ => B r e) (Ioi 0) :=
      hB.comp hφ.contDiffOn (fun r hr => ⟨hr, trivial⟩)
    have hA_at : ContDiffAt ℝ ℓ (fun r : ℝ => A r e) s :=
      (hA_r.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)
    have hB_at : ContDiffAt ℝ ℓ (fun r : ℝ => B r e) s :=
      (hB_r.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)
    exact iteratedDeriv_add hA_at hB_at
  have hHA := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 A hA ℓ
  have hHB := UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 B hB ℓ
  have hψ : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hA_e : ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => A r e) s) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => A r x.2) x.1) ∘
          (fun e : ℝ => ((s, e) : ℝ × ℝ))) univ :=
      hHA.comp (contDiffOn_univ.mpr hψ) (fun _ _ => ⟨hs, trivial⟩)
    exact contDiffOn_univ.mp hcomp
  have hB_e : ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => B r e) s) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => B r x.2) x.1) ∘
          (fun e : ℝ => ((s, e) : ℝ × ℝ))) univ :=
      hHB.comp (contDiffOn_univ.mpr hψ) (fun _ _ => ⟨hs, trivial⟩)
    exact contDiffOn_univ.mp hcomp
  have hfun : (fun e => iteratedDeriv ℓ (fun r => A r e + B r e) s) =
      fun e => iteratedDeriv ℓ (fun r => A r e) s + iteratedDeriv ℓ (fun r => B r e) s :=
    funext hr_eq
  rw [hfun]
  exact iteratedDeriv_add
    (hA_e.contDiffAt.of_le (by exact_mod_cast le_top))
    (hB_e.contDiffAt.of_le (by exact_mod_cast le_top))

/-- Under the Duhamel formula `meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e`
for `r > 0`, `meanSourceRemainder tr N` is jointly `C^∞` on `(0, ∞) × ℝ` and every nested slice
derivative of `meanRemainder tr N` at `s > 0` splits into the sum of the nested slice derivatives
of `meanDatumRemainder tr N` and `meanSourceRemainder tr N`. -/
theorem meanRemainder_slice_eq_add_of_duhamel {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η =
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η +
        iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRemSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of
      trainMeanEquations_proof UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν c hν hc0 tr htr N
  have hDatSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanDatumRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_meanDatumRemainder hν hc1 tr N
  have hSrcSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanSourceRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) := by
    refine (hRemSm.sub hDatSm).congr fun x hx => ?_
    have h := meanRemainder_eq_add_of_duhamel tr N (hD x.1 hx.1 x.2)
    linarith
  have hr_congr : ∀ e : ℝ, iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s =
      iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e + meanSourceRemainder tr N r e) s := by
    intro e
    refine Filter.EventuallyEq.iteratedDeriv_eq ℓ ?_
    filter_upwards [Ioi_mem_nhds hs] with r hr
      using meanRemainder_eq_add_of_duhamel tr N (hD r hr e)
  have hfun : (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) =
      fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e + meanSourceRemainder tr N r e) s :=
    funext hr_congr
  rw [hfun]
  exact iteratedDeriv_slice_add_aux hDatSm hSrcSm b ℓ hs η

end PartI_T23

/-! ### 7. Leaves (`PartI:T23/2/1`–`PartI:T23/2/3`) and conditional assembly of `TrainMeanRemainderLpBound` -/

/-- **Leaf 1 (`PartI:T23/2/1`): 1D heat Duhamel representation of `meanStream`**
(source lines 397-412, 448-456, 528-534): for every `ρ > 1/2`, there exists `ν₀ > 0` such that
for all `0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, and all `s > 0`,
`η ∈ ℝ`,
`meanStream tr s η = meanDatumDuhamel tr s η + meanSourceDuhamel tr s η`. -/
def TrainMeanStreamDuhamel : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → ∀ η : ℝ,
        meanStream tr s η = meanDatumDuhamel tr s η + meanSourceDuhamel tr s η

/-- **Leaf 2 (`PartI:T23/2/2`): weighted pointwise Taylor remainder bound for the initial-datum
part `meanDatumRemainder`** (source lines 451-458, 528-535): Taylor-expanding `G_{ν s}(η - ξ)`
through order `2N + 1` in `meanDatumDuhamel tr s η = ∫ ξ, G_{ν s}(η - ξ) S(0, ξ) dξ` (where odd
moments vanish by evenness `hTails.1` and the integral remainder is controlled by the `(2N + 2)`-th
spatial derivative of `G_{ν s}` and the `(2N + 2)`-th moment of `S(0)`) yields
`|η|^m |∂_η^b ∂_s^ℓ R_N^{(0)}(s, η)| ≤ polyP C M ν c * s^{(m - b - 2N - 3)/2 - ℓ}` for `s ≥ 1`. -/
def TrainMeanDatumRemainderBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ N m b ℓ : ℕ, ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        |η| ^ m * |iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η| ≤
          polyP C M ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ)

/-- **Leaf 3 (`PartI:T23/2/3`): weighted pointwise Taylor remainder bound for the inhomogeneous
source Duhamel part `meanSourceRemainder`** (source lines 451-458, 531-538): in the source Duhamel
integral, splitting at `t = s / 2`, jointly Taylor-expanding `G_{ν(s - t)}(η - ξ)` in `(ξ, t)` for
`t ≤ s / 2` retaining `k + ℓ' ≤ N` using `∂_s G_{ν s} = ν ∂_η² G_{ν s}`, and transferring
derivatives onto the exponentially decaying source `g = meanStress tr` for `t ≥ s / 2` yields
`|η|^m |∂_η^b ∂_s^ℓ R_N^{(g)}(s, η)| ≤ polyP C M ν c * s^{(m - b - 2N - 3)/2 - ℓ}` for `s ≥ 1`. -/
def TrainMeanSourceRemainderBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ N m b ℓ : ℕ, ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        |η| ^ m * |iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| ≤
          polyP C M ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ)

/-- **Pointwise (`p = ∞`) Taylor remainder bound for the 1D heat Duhamel expansion of `meanStream`**
(source lines 448-458, 528-551): for every `ρ > 1/2` and `N, m, b, ℓ : ℕ`, there exist `C > 0`,
`M : ℕ`, and `ν₀ > 0` such that for all `0 < ν ≤ ν₀`, every `BUC` train `tr`, `s ≥ 1`, and `η ∈ ℝ`,
`|η|^m |∂_η^b ∂_s^ℓ R_N(s, η)| ≤ polyP C M ν c * s^{(m - b - 2N - 3)/2 - ℓ}`. -/
def TrainMeanRemainderPointwiseBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ N m b ℓ : ℕ, ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        |η| ^ m * |iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η| ≤
          polyP C M ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ)

/-- **Conditional assembly of `TrainMeanRemainderPointwiseBound` from the three leaves
`TrainMeanStreamDuhamel`, `TrainMeanDatumRemainderBound`, and `TrainMeanSourceRemainderBound`**. -/
theorem trainMeanRemainderPointwiseBound_of
    (hDuh : TrainMeanStreamDuhamel)
    (hDat : TrainMeanDatumRemainderBound)
    (hSrc : TrainMeanSourceRemainderBound) :
    TrainMeanRemainderPointwiseBound := by
  intro ρ hρ N m b ℓ
  obtain ⟨νD, hνD, hD⟩ := hDuh ρ hρ
  obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hB₁⟩ := hDat ρ hρ N m b ℓ
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, hB₂⟩ := hSrc ρ hρ N m b ℓ
  refine ⟨C₁ + C₂, max M₁ M₂, min (min νD 1) (min ν₁ ν₂),
    add_pos hC₁ hC₂, lt_min (lt_min hνD one_pos) (lt_min hν₁ hν₂), ?_⟩
  intro ν hν hν_le tr htr c s hs η
  have hνD_le : ν ≤ νD := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ c := zero_le_one.trans hc1
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hP₁ : polyP C₁ M₁ ν c ≤ polyP C₁ (max M₁ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
  have hP₂ : polyP C₂ M₂ ν c ≤ polyP C₂ (max M₁ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
  have hsplit := PartI_T23.meanRemainder_slice_eq_add_of_duhamel
    hν hc1 tr htr (hD ν hν hνD_le tr htr) N b ℓ hs0 η
  rw [hsplit]
  set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2 - ℓ
  have hsα_nn : 0 ≤ s ^ α := Real.rpow_nonneg hs0.le _
  have h1 := (hB₁ ν hν hν₁_le tr htr s hs η).trans
    (mul_le_mul_of_nonneg_right hP₁ hsα_nn)
  have h2 := (hB₂ ν hν hν₂_le tr htr s hs η).trans
    (mul_le_mul_of_nonneg_right hP₂ hsα_nn)
  calc |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η +
          iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η|
      ≤ |η| ^ m * (|iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η| +
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ = |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η| +
          |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| := by
        ring
    _ ≤ polyP C₁ (max M₁ M₂) ν c * s ^ α + polyP C₂ (max M₁ M₂) ν c * s ^ α :=
        add_le_add h1 h2
    _ = polyP (C₁ + C₂) (max M₁ M₂) ν c * s ^ α := by
        unfold polyP
        ring

/-- **Conditional assembly of `TrainMeanRemainderLpBound` (`PartI:T23/2`) from
`TrainMeanRemainderPointwiseBound`**: reduces the full `L^p(ℝ)` bound (`1 ≤ p ≤ ∞`) to
`TrainMeanRemainderPointwiseBound` at weights `m` and `m + 2` via
`PartI_T23.eLpNorm_pow_mul_le_of_pointwise`. -/
theorem trainMeanRemainderLpBound_of (hPt : TrainMeanRemainderPointwiseBound) :
    TrainMeanRemainderLpBound := by
  intro ρ hρ N m b ℓ p hp
  obtain ⟨C₀, M₀, ν₀, hC₀, hν₀, h0⟩ := hPt ρ hρ N m b ℓ
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, h2⟩ := hPt ρ hρ N (m + 2) b ℓ
  refine ⟨Real.pi * (C₀ + C₂), max M₀ M₂, min ν₀ ν₂,
    mul_pos Real.pi_pos (add_pos hC₀ hC₂), lt_min hν₀ hν₂, ?_⟩
  intro ν hν hν_le tr htr c s hs
  have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hP₀ : polyP C₀ M₀ ν c ≤ polyP C₀ (max M₀ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₀.le
  have hP₂ : polyP C₂ M₂ ν c ≤ polyP C₂ (max M₀ M₂) ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_right _ _)) hC₂.le
  set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2 - ℓ
  have hα2 : (((m + 2 : ℕ) : ℝ) - b - 2 * N - 3) / 2 - ℓ = α + 1 := by
    dsimp [α]
    push_cast
    ring
  have hpt0 : ∀ η : ℝ, |η| ^ m * |iteratedDeriv b
      (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η| ≤
      polyP C₀ (max M₀ M₂) ν c * s ^ α := fun η =>
    (h0 ν hν hν₀_le tr htr s hs η).trans
      (mul_le_mul_of_nonneg_right hP₀ (Real.rpow_nonneg (zero_le_one.trans hs) _))
  have hpt2 : ∀ η : ℝ, |η| ^ (m + 2) * |iteratedDeriv b
      (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η| ≤
      polyP C₂ (max M₀ M₂) ν c * s ^ (α + 1) := by
    intro η
    have h := h2 ν hν hν₂_le tr htr s hs η
    rw [hα2] at h
    exact h.trans (mul_le_mul_of_nonneg_right hP₂ (Real.rpow_nonneg (zero_le_one.trans hs) _))
  have hA₀ : 0 ≤ polyP C₀ (max M₀ M₂) ν c := by unfold polyP; positivity
  have hA₂ : 0 ≤ polyP C₂ (max M₀ M₂) ν c := by unfold polyP; positivity
  refine (PartI_T23.eLpNorm_pow_mul_le_of_pointwise
    (fun η => iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η)
    m hs hA₀ hA₂ hp hpt0 hpt2).trans (le_of_eq ?_)
  congr 1
  unfold polyP
  ring

/-- **Converse extraction of `TrainMeanRemainderPointwiseBound` from `TrainMeanRemainderLpBound`**
at `p = ⊤` using continuity of the slice derivatives of `meanRemainder`. -/
theorem trainMeanRemainderPointwiseBound_of_lp (hLp : TrainMeanRemainderLpBound) :
    TrainMeanRemainderPointwiseBound := by
  intro ρ hρ N m b ℓ
  obtain ⟨C, M, ν₀, hC, hν₀, hbd⟩ := hLp ρ hρ N m b ℓ ⊤ le_top
  refine ⟨C, M, ν₀, hC, hν₀, ?_⟩
  intro ν hν hνle tr htr c s hs η
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hR' := hbd ν hν hνle tr htr s hs
  simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero] at hR'
  have hSm := UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of
    trainMeanEquations_proof UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν c hν hc0 tr htr N
  have hSC := UnforcedLeray.Short.PartIIa.sliceDerivContinuous_of
    UnforcedLeray.Short.PartIIa.ageDerivSmooth
  have hD : Continuous (fun η' : ℝ =>
      iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η') :=
    hSC (fun r e => meanRemainder tr N r e) hSm b ℓ s (lt_of_lt_of_le one_pos hs)
  have hfc : Continuous (fun η' : ℝ =>
      η' ^ m * iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η') :=
    (continuous_pow m).mul hD
  have hB0 : 0 ≤ polyP C M ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ) := by
    unfold polyP
    have : 0 ≤ c := hc0.le
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ s := zero_le_one.trans hs
    positivity
  have hES' := UnforcedLeray.Short.PartIIa.essSupPointwise _ hfc _ hB0 hR' η
  rwa [abs_mul, abs_pow] at hES'

/-- **Conditional assembly of `TrainMeanRemainderLpBound` (`PartI:T23/2`) directly from the three
leaves `TrainMeanStreamDuhamel`, `TrainMeanDatumRemainderBound`, and `TrainMeanSourceRemainderBound`**. -/
theorem trainMeanRemainderLpBound_of_leaves
    (hDuh : TrainMeanStreamDuhamel)
    (hDat : TrainMeanDatumRemainderBound)
    (hSrc : TrainMeanSourceRemainderBound) :
    TrainMeanRemainderLpBound :=
  trainMeanRemainderLpBound_of (trainMeanRemainderPointwiseBound_of hDuh hDat hSrc)

end UnforcedLeray.Short.PartI
