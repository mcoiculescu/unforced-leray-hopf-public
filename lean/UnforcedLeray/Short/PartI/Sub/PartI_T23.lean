import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `PartI:T23` (`Sub/PartI_T23.lean`): heat-kernel expansion and remainder bounds for the mean stream (`sct:expansion`)

Source of record: `the November 2 reference manuscript`, lines 447-462, 528-540.

This module proves:
1. Continuity and Gaussian decay `|meanStream tr 0 η| ≤ 20 e^{-η²/4}` of the initial mean stream
   `S(0) = meanStream tr 0`, and integrability of all spatial moments
   `η ↦ η^{2j} meanStream tr 0 η` for every `j : ℕ` (`PartI_T23.integrable_pow_mul_meanStream_zero`).
2. Joint smoothness `ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ)`
   (`PartI_T23.contDiffOn_meanStress`) and evenness `meanStress tr s (-η) = meanStress tr s η`
   (`PartI_T23.meanStress_even`) of the mean Reynolds stress `g = meanStress tr`.
3. Pointwise decay `|meanStress tr t η| ≤ K² / (1 + η²)^m`, spatial moment integrability
   `Integrable (fun η => η^{2k} * meanStress tr t η)`, and moment bound
   `‖∫ η, η^{2k} * meanStress tr t η‖ ≤ π K²` from `trainMeanEquations_proof` (`\bar v₂ = 0`) and
   a weighted sup-norm bound on `hfluct c (tr.v t)` (`PartI_T23.meanStress_bound_of_wSupNorm`,
   `PartI_T23.integrable_pow_mul_meanStress_of_wSupNorm`).
4. Space and time integrability and exponential decay of the moments
   `η^{2k} meanStress tr t η` for every fixed `k : ℕ` from `TrainFluctuationDecay`
   (`PartI_T23.meanStress_moment_integrable_of_fluctDecay`).
5. Conditional assembly `trainMeanExpansion_of` combining evenness (`hTails.1`), the proved
   initial-datum moment integrability (`integrable_pow_mul_meanStream_zero`), and the three
   remaining leaves (`TrainMeanStressMomentsAllOrders`, `TrainMeanRemainderLpBound`,
   `TrainMeanStreamLpBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)

namespace PartI_T23

/-! ### 1. Continuity, smoothness, evenness, and initial mean-stream moments -/

/-- For a continuous function `F : Plane → ℝ` and `c ≥ 0`, `hmean c F` is continuous on `ℝ`. -/
theorem continuous_hmean_of_continuous {c : ℝ} (hc : 0 ≤ c) {F : Plane → ℝ}
    (hF : Continuous F) : Continuous (hmean c F) := by
  have hle : -c / 2 ≤ c / 2 := by linarith
  have hfun : hmean c F = fun η : ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), F (q, η) := by
    funext η
    unfold hmean
    rw [smul_eq_mul, intervalIntegral.integral_of_le hle]
  rw [hfun]
  have hcont_uncurry : Continuous (Function.uncurry (fun (η q : ℝ) => F (q, η))) :=
    hF.comp (continuous_snd.prodMk continuous_fst)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hcont_uncurry (-c / 2) (c / 2))

/-- For `s ≥ 0` and `c ≥ 0`, `η ↦ meanStream tr s η` is continuous. -/
theorem continuous_meanStream {ν c : ℝ} (hc : 0 ≤ c) (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) : Continuous (meanStream tr s) :=
  continuous_hmean_of_continuous hc (tr.isTrain.stream_differentiable s hs).continuous

/-- For `s ≥ 0` and `c ≥ 0`, `η ↦ meanStress tr s η` is continuous. -/
theorem continuous_meanStress {ν c : ℝ} (hc : 0 ≤ c) (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) : Continuous (meanStress tr s) := by
  have hv : Continuous (tr.v s) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hs, mem_univ _⟩)
  have hprod : Continuous (fun z : Plane => tr.v s z 0 * tr.v s z 1) :=
    ((PiLp.continuous_apply 2 _ 0).comp hv).mul ((PiLp.continuous_apply 2 _ 1).comp hv)
  exact continuous_hmean_of_continuous hc hprod

/-- Joint `C^∞` smoothness of `meanStress tr` on `(0, ∞) × ℝ` for `c > 0`. -/
theorem contDiffOn_meanStress {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv0 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 0) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have hv1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  exact hmeanContDiff c hc (fun s z => tr.v s z 0 * tr.v s z 1) (hv0.mul hv1)

/-- Evenness of `meanStress tr s` for `c > 0` and `s ≥ 0`:
`meanStress tr s (-η) = meanStress tr s η` from central oddness `tr.isTrain.odd`. -/
theorem meanStress_even {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 ≤ s) (η : ℝ) :
    meanStress tr s (-η) = meanStress tr s η := by
  unfold meanStress hmean
  congr 1
  have hle : -c / 2 ≤ c / 2 := by linarith
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  have hodd := tr.isTrain.odd s hs
  have heq : (fun q : ℝ => tr.v s (q, -η) 0 * tr.v s (q, -η) 1) =
      fun q : ℝ => tr.v s (-q, η) 0 * tr.v s (-q, η) 1 := by
    funext q
    have h0 : tr.v s (q, -η) 0 = -tr.v s (-q, η) 0 := by
      have h := congrArg (fun w : Vec => w 0) (hodd (-q, η))
      simpa using h
    have h1 : tr.v s (q, -η) 1 = -tr.v s (-q, η) 1 := by
      have h := congrArg (fun w : Vec => w 1) (hodd (-q, η))
      simpa using h
    rw [h0, h1, neg_mul_neg]
  rw [heq, intervalIntegral.integral_comp_neg (fun q : ℝ => tr.v s (q, η) 0 * tr.v s (q, η) 1)]
  have h1 : -(c / 2) = -c / 2 := by ring
  have h2 : -(-c / 2) = c / 2 := by ring
  rw [h1, h2]

/-- At `s = 0` and `c ≥ 1`, `‖meanStream tr 0 η‖ ≤ 20 * exp (-(η² / 4))`. -/
theorem norm_meanStream_zero_le {ν c : ℝ} (hc1 : 1 ≤ c) (tr : B0140.TrainSol ν c) (η : ℝ) :
    ‖meanStream tr 0 η‖ ≤ 20 * Real.exp (-(η ^ 2 / 4)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hS0 : meanStream tr 0 η = hmean c (B0140.trainStream c) η := by
    unfold meanStream
    rw [tr.isTrain.stream_zero hc1]
  rw [hS0]
  unfold hmean
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0]
  have hpt : ∀ q ∈ Ioc (-c / 2) (c / 2),
      ‖B0140.trainStream c (q, η)‖ ≤ 20 * Real.exp (-(η ^ 2 / 4)) := by
    intro q _
    rw [Real.norm_eq_abs]
    exact B0140.abs_trainStream_le hc1 (q, η)
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
    (f := fun q => B0140.trainStream c (q, η)) measure_Ioc_lt_top hpt
  rw [Real.volume_real_Ioc_of_le (by linarith)] at h
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), B0140.trainStream c (q, η)‖
      ≤ c⁻¹ * (20 * Real.exp (-(η ^ 2 / 4)) * (c / 2 - -c / 2)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc0.le)
    _ = 20 * Real.exp (-(η ^ 2 / 4)) := by
        rw [show c / 2 - -c / 2 = c by ring]
        field_simp

/-- Every even spatial moment `η ↦ η^{2j} * meanStream tr 0 η` is integrable on `ℝ` for `c ≥ 1`. -/
theorem integrable_pow_mul_meanStream_zero {ν c : ℝ} (hc1 : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (j : ℕ) :
    Integrable (fun η : ℝ => η ^ (2 * j) * meanStream tr 0 η) volume := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hgauss : Integrable (fun η : ℝ => 20 * (η ^ (2 * j) * Real.exp (-(η ^ 2 / 4)))) volume := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)
      (s := ((2 * j : ℕ) : ℝ))
      (by have : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    refine (h.congr (Eventually.of_forall fun η => ?_)).const_mul 20
    simp only [Real.rpow_natCast]
    ring_nf
  have hcont : Continuous (fun η : ℝ => η ^ (2 * j) * meanStream tr 0 η) :=
    (continuous_pow (2 * j)).mul (continuous_meanStream hc0 tr le_rfl)
  refine hgauss.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun η => ?_)
  have hpos : 0 ≤ η ^ (2 * j) := by rw [pow_mul]; positivity
  rw [norm_mul, Real.norm_of_nonneg hpos]
  calc η ^ (2 * j) * ‖meanStream tr 0 η‖
      ≤ η ^ (2 * j) * (20 * Real.exp (-(η ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_left (norm_meanStream_zero_le hc1 tr η) hpos
    _ = 20 * (η ^ (2 * j) * Real.exp (-(η ^ 2 / 4))) := by ring

/-! ### 2. Pointwise decay and spatial/time moment integrability of `meanStress` -/

/-- Pointwise bound from `wSupNorm m f ≤ ofReal K`. -/
theorem jap_mul_norm_sq_le_of_wSupNorm {E : Type*} [NormedAddCommGroup E] (m : ℕ)
    (f : Plane → E) {K : ℝ} (hK : 0 ≤ K) (h : wSupNorm m f ≤ ENNReal.ofReal K) (z : Plane) :
    jap m z * ‖f z‖ ^ 2 ≤ K ^ 2 := by
  have h1 : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ ≤ ENNReal.ofReal K :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z).trans h
  have hj : 0 ≤ jap m z := by unfold jap; positivity
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hK] at h1
  calc jap m z * ‖f z‖ ^ 2 = (Real.sqrt (jap m z) * ‖f z‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hj]
    _ ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) h1 2

theorem norm_ageJet_zero_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → Plane → E) (t : ℝ) (z : Plane) :
    ‖ageJet 0 0 F t z‖ = ‖F t z‖ := by
  simp [ageJet, jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]

/-- Pointwise bound on `meanStress tr t η` from `wSupNorm m` of `hfluct c (tr.v t)`. -/
theorem meanStress_bound_of_wSupNorm {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {t : ℝ} (ht : 0 < t)
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsup : wSupNorm m (ageJet 0 0 (fun r => hfluct c (tr.v r)) t) ≤ ENNReal.ofReal K)
    (η : ℝ) :
    ‖meanStress tr t η‖ ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
  have hE3 : ∀ η' : ℝ, hmean c (fun z => tr.v t z 1) η' = 0 :=
    fun η' => ((trainMeanEquations_proof ν c hν hc tr htr).2 t ht η').2.2
  have hcont : Continuous (tr.v t) := by
    have hc_on : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hc_on.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨ht.le, mem_univ _⟩)
  have hqcont : Continuous (fun q : ℝ => tr.v t (q, η)) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hqi : ∀ i : Fin 2, Continuous (fun q : ℝ => tr.v t (q, η) i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp hqcont
  have hmean1 : hmean c (tr.v t) η 1 = 0 := by
    have hint : Integrable (fun q : ℝ => tr.v t (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      hqcont.integrableOn_Ioc
    have hproj := (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).integral_comp_comm hint
    have happly : hmean c (tr.v t) η 1 = hmean c (fun z => tr.v t z 1) η := by
      unfold hmean
      rw [PiLp.smul_apply]
      congr 1
      simpa using hproj.symm
    rw [happly, hE3 η]
  have hJ : 0 < (1 + η ^ 2) ^ m := by positivity
  have hwb : ∀ q : ℝ, ‖tr.v t (q, η) - hmean c (tr.v t) η‖ ^ 2 ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
    intro q
    have hpt := jap_mul_norm_sq_le_of_wSupNorm m
      (ageJet 0 0 (fun r => hfluct c (tr.v r)) t) hK hsup (q, η)
    rw [norm_ageJet_zero_zero] at hpt
    rw [le_div_iff₀ hJ, mul_comm]
    exact hpt
  set w : ℝ → Vec := fun q => tr.v t (q, η) - hmean c (tr.v t) η with hw
  have hwi : ∀ i : Fin 2, Continuous (fun q => w q i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp (hqcont.sub continuous_const)
  have hid : ∀ q : ℝ, tr.v t (q, η) 0 * tr.v t (q, η) 1 =
      w q 0 * w q 1 + hmean c (tr.v t) η 0 * tr.v t (q, η) 1 := by
    intro q
    have h1 : w q 1 = tr.v t (q, η) 1 := by
      simp only [hw, PiLp.sub_apply, hmean1, sub_zero]
    have h0 : w q 0 = tr.v t (q, η) 0 - hmean c (tr.v t) η 0 := by
      simp only [hw, PiLp.sub_apply]
    rw [h1, h0]
    ring
  have hI1 : Integrable (fun q : ℝ => w q 0 * w q 1) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    ((hwi 0).mul (hwi 1)).integrableOn_Ioc
  have hI2 : Integrable (fun q : ℝ => hmean c (tr.v t) η 0 * tr.v t (q, η) 1)
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (continuous_const.mul (hqi 1)).integrableOn_Ioc
  have hv1 : ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 1 = 0 := by
    have h := hE3 η
    unfold hmean at h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact absurd (inv_eq_zero.mp h1) hc.ne'
    · exact h1
  have hmain : ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1 =
      ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by
    calc ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1
        = ∫ q in Ioc (-c / 2) (c / 2), (w q 0 * w q 1 + hmean c (tr.v t) η 0 * tr.v t (q, η) 1) := by
          congr 1; funext q; exact hid q
      _ = (∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1) +
            hmean c (tr.v t) η 0 * ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 1 := by
          rw [integral_add hI1 hI2, integral_const_mul]
      _ = ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by rw [hv1, mul_zero, add_zero]
  have hbd : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖w q 0 * w q 1‖ ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
    intro q _
    rw [norm_mul]
    have h0 := PiLp.norm_apply_le (w q) 0
    have h1 := PiLp.norm_apply_le (w q) 1
    calc ‖w q 0‖ * ‖w q 1‖ ≤ ‖w q‖ * ‖w q‖ := mul_le_mul h0 h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖w q‖ ^ 2 := (sq _).symm
      _ ≤ K ^ 2 / (1 + η ^ 2) ^ m := hwb q
  have hint_bd : ‖∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1‖ ≤
      K ^ 2 / (1 + η ^ 2) ^ m * c := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (-c / 2) (c / 2)) measure_Ioc_lt_top hbd
    rw [Real.volume_real_Ioc_of_le (by linarith)] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hms : meanStress tr t η = c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by
    rw [← hmain]
    unfold meanStress hmean
    rw [smul_eq_mul]
  rw [hms, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1‖
      ≤ c⁻¹ * (K ^ 2 / (1 + η ^ 2) ^ m * c) :=
        mul_le_mul_of_nonneg_left hint_bd (inv_nonneg.2 hc.le)
    _ = K ^ 2 / (1 + η ^ 2) ^ m := by field_simp

/-- Spatial integrability and `L¹` bound for `η ↦ η^{2k} * meanStress tr t η` from a weight-`(k+1)`
sup-norm bound on `hfluct c (tr.v t)`. -/
theorem integrable_pow_mul_meanStress_of_wSupNorm {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {t : ℝ} (ht : 0 < t)
    (k : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsup : wSupNorm (k + 1) (ageJet 0 0 (fun r => hfluct c (tr.v r)) t) ≤ ENNReal.ofReal K) :
    Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume ∧
    ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖ ≤ Real.pi * K ^ 2 := by
  have hg : Integrable (fun η : ℝ => K ^ 2 * (1 + η ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  have hcont : Continuous (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) :=
    (continuous_pow (2 * k)).mul (continuous_meanStress hc.le tr ht.le)
  have hpt : ∀ η : ℝ, ‖η ^ (2 * k) * meanStress tr t η‖ ≤ K ^ 2 * (1 + η ^ 2)⁻¹ := by
    intro η
    have hpos : 0 ≤ η ^ (2 * k) := by rw [pow_mul]; positivity
    have hle : η ^ (2 * k) ≤ (1 + η ^ 2) ^ k := by
      calc η ^ (2 * k) = (η ^ 2) ^ k := by rw [pow_mul]
        _ ≤ (1 + η ^ 2) ^ k := pow_le_pow_left₀ (sq_nonneg η) (by linarith) k
    have hG := meanStress_bound_of_wSupNorm hν hc tr htr ht (k + 1) hK hsup η
    rw [norm_mul, Real.norm_of_nonneg hpos]
    calc η ^ (2 * k) * ‖meanStress tr t η‖
        ≤ (1 + η ^ 2) ^ k * (K ^ 2 / (1 + η ^ 2) ^ (k + 1)) :=
          mul_le_mul hle hG (norm_nonneg _) (by positivity)
      _ = K ^ 2 * (1 + η ^ 2)⁻¹ := by
          rw [pow_succ]
          field_simp
          ring
  refine ⟨hg.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt), ?_⟩
  calc ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖
      ≤ ∫ η : ℝ, K ^ 2 * (1 + η ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
    _ = Real.pi * K ^ 2 := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        ring

/-- **Fixed-order space and time moment integrability and exponential decay for `meanStress`**
from `TrainFluctuationDecay`: for every `ρ > 1/2` and `k : ℕ`, there exist `C > 0`, `M : ℕ`,
`κ > 0`, and `ν₀ > 0` such that for `0 < ν ≤ ν₀` and `IsBUCTrain tr`:
1. `η ↦ η^{2k} * meanStress tr t η` is integrable on `ℝ` for every `t > 0`,
2. `‖∫ η, η^{2k} * meanStress tr t η‖ ≤ π * (polyP C M ν c)² * exp (-(2 κ ν t / c²))` for `t > 0`,
3. `t ↦ ∫ η, η^{2k} * meanStress tr t η` is integrable on `Ioi 0`. -/
theorem meanStress_moment_integrable_of_fluctDecay (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (k : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ κ ν₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        (∀ t : ℝ, 0 < t → Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume) ∧
        (∀ t : ℝ, 0 < t →
          ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖ ≤
            Real.pi * (polyP C M ν c) ^ 2 * Real.exp (-(2 * κ * ν * t / c ^ 2))) ∧
        IntegrableOn (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η) (Ioi 0) volume := by
  obtain ⟨C, M, κ, ν₀, hC, hκ, hν₀, hF⟩ := hFD ρ hρ (k + 1) 0 0
  refine ⟨C, M, κ, ν₀, hC, hκ, hν₀, ?_⟩
  intro ν hν hν_le tr htr
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν (-ρ)
  have hpt : ∀ t : ℝ, 0 < t →
      Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume ∧
      ‖∫ η : ℝ, η ^ (2 * k) * meanStress tr t η‖ ≤
        Real.pi * (polyP C M ν c) ^ 2 * Real.exp (-(2 * κ * ν * t / c ^ 2)) := by
    intro t ht
    have hsup := (hF ν hν hν_le tr htr t ht).2.1.2
    let K : ℝ := polyP C M ν c * Real.exp (-(κ * ν * t / c ^ 2))
    have hK : 0 ≤ K := by
      dsimp [K, polyP]
      positivity
    obtain ⟨hint, hbd⟩ := integrable_pow_mul_meanStress_of_wSupNorm hν hc0 tr htr ht k hK hsup
    refine ⟨hint, hbd.trans (le_of_eq ?_)⟩
    dsimp [K]
    rw [mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  refine ⟨fun t ht => (hpt t ht).1, fun t ht => (hpt t ht).2, ?_⟩
  -- Measurability of `t ↦ ∫ η, η^{2k} * meanStress tr t η` on `Ioi 0`
  let G : ℝ × ℝ → ℝ := (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
    (fun x : ℝ × ℝ => x.2 ^ (2 * k) * meanStress tr x.1 x.2)
  have hS_meas : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (isOpen_Ioi.prod isOpen_univ).measurableSet
  have hG_contOn : ContinuousOn (fun x : ℝ × ℝ => x.2 ^ (2 * k) * meanStress tr x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (continuousOn_snd.pow (2 * k)).mul (contDiffOn_meanStress hc0 tr).continuousOn
  have hG_aem : AEStronglyMeasurable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (aestronglyMeasurable_indicator_iff hS_meas).2 (hG_contOn.aestronglyMeasurable hS_meas)
  have h_int_aem : AEStronglyMeasurable (fun t : ℝ => ∫ η : ℝ, G (t, η)) volume :=
    hG_aem.integral_prod_right'
  have h_aem_Ioi : AEStronglyMeasurable
      (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η) (volume.restrict (Ioi 0)) := by
    refine h_int_aem.restrict.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    congr 1
    funext η
    have hmem : ((t, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨ht', mem_univ η⟩
    simp [G, hmem]
  have hb_pos : 0 < 2 * κ * ν / c ^ 2 := by positivity
  have hexp_int : IntegrableOn
      (fun t : ℝ => Real.pi * (polyP C M ν c) ^ 2 * Real.exp (-(2 * κ * ν / c ^ 2) * t))
      (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 hb_pos).const_mul (Real.pi * (polyP C M ν c) ^ 2)
  refine hexp_int.mono' h_aem_Ioi ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hbd := (hpt t ht).2
  have he : -(2 * κ * ν * t / c ^ 2) = -(2 * κ * ν / c ^ 2) * t := by ring
  rwa [he] at hbd

end PartI_T23

/-! ### 3. Leaves and conditional assembly `trainMeanExpansion_of` -/

/-- **Leaf 1 (`PartI:T23/1`): all-order spatial and time moment integrability of `meanStress` at
fixed parameters** (source lines 427-435, 450-453, 528-530; cf. `TrainMeanMomentsFixed` in
`Short/PartI/Sub/PartI_TrainHeatFixed.lean`): for every `ρ > 1/2`, there exists `ν₀ > 0` such that
for all `0 < ν ≤ ν₀`, every `BUC` train `tr` at period `c = trainPeriod ρ ν`, and every `k : ℕ`,
`η ↦ η^{2k} meanStress tr t η` is integrable on `ℝ` for all `t > 0` and
`t ↦ ∫ η, η^{2k} meanStress tr t η` is integrable on `(0, ∞)`. -/
def TrainMeanStressMomentsAllOrders : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∀ k : ℕ, (∀ t : ℝ, 0 < t → Integrable (fun η : ℝ => η ^ (2 * k) * meanStress tr t η) volume) ∧
        IntegrableOn (fun t : ℝ => ∫ η : ℝ, η ^ (2 * k) * meanStress tr t η) (Ioi 0) volume

/-- **Leaf 2 (`PartI:T23/2`): `L^p` Taylor remainder bound for the 1D heat Duhamel expansion of
`meanStream`** (source lines 448-458, 528-539): in the 1D heat Duhamel representation for
`S_s - ν S_{ηη} = g`, Taylor-expanding `G_{ν s}(η - ξ)` through order `2N + 1` (odd terms vanish by
evenness) and jointly in `(ξ, t)` for `t ≤ s / 2` retaining `k + ℓ ≤ N` using
`∂_s G_{ν s} = ν ∂_η² G_{ν s}`, and transferring derivatives onto `g` for `t ≥ s / 2`, yields
`‖η^m ∂_η^b ∂_s^ℓ R_N(s)‖_p ≤ P s^{(m - b - 2N - 3)/2 - ℓ + 1/(2p)}` for `s ≥ 1`. -/
def TrainMeanRemainderLpBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ (N m b ℓ : ℕ) (p : ℝ≥0∞), 1 ≤ p → ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ s : ℝ, 1 ≤ s →
        eLpNorm (fun η : ℝ => η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanRemainder tr N r e) s) η) p volume ≤
          ENNReal.ofReal (polyP C M ν c *
            s ^ (((m : ℝ) - b - 2 * N - 3) / 2 - ℓ + p.toReal⁻¹ / 2))

/-- **Leaf 3 (`PartI:T23/3`): `L^p` weighted mixed-derivative bound for `meanStream` itself**
(source lines 459-462, 539-540: "In particular, replacing the remainder power by
`(m - b - 1)/2 - ℓ + 1/(2p)` bounds `S` itself with `s` replaced by `1 + s`"): for all `s ≥ 0`,
`‖η^m ∂_η^b ∂_s^ℓ S(s)‖_p ≤ P (1 + s)^{(m - b - 1)/2 - ℓ + 1/(2p)}`. -/
def TrainMeanStreamLpBound : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ (m b ℓ : ℕ) (p : ℝ≥0∞), 1 ≤ p → ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ,
    0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      let c := trainPeriod ρ ν
      ∀ s : ℝ, 0 ≤ s →
        eLpNorm (fun η : ℝ => η ^ m * iteratedDeriv b
            (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η) p volume ≤
          ENNReal.ofReal (polyP C M ν c *
            (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ + p.toReal⁻¹ / 2))

/-- **Conditional assembly of `TrainMeanExpansion` (`PartI:T23`)**: combines evenness of
`meanStream` from `TrainStreamVelocityPressureTails.1`, the unconditionally proved initial-datum
moment integrability `PartI_T23.integrable_pow_mul_meanStream_zero`,
`TrainMeanStressMomentsAllOrders`, `TrainMeanRemainderLpBound`, and `TrainMeanStreamLpBound`. -/
theorem trainMeanExpansion_of (hTails : TrainStreamVelocityPressureTails)
    (hMom : TrainMeanStressMomentsAllOrders)
    (hRem : TrainMeanRemainderLpBound)
    (hStr : TrainMeanStreamLpBound) :
    TrainMeanExpansion := by
  intro ρ hρ N m b ℓ p hp
  obtain ⟨νM, hνM, hM⟩ := hMom ρ hρ
  obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hR⟩ := hRem ρ hρ N m b ℓ p hp
  obtain ⟨C₂, M₂, ν₂, hC₂, hν₂, hS⟩ := hStr ρ hρ m b ℓ p hp
  refine ⟨max C₁ C₂, max M₁ M₂, min (min νM ν₁) (min ν₂ 1),
    lt_max_of_lt_left hC₁, lt_min (lt_min hνM hν₁) (lt_min hν₂ one_pos), ?_⟩
  intro ν hν hν_le tr htr
  have hνM_le : ν ≤ νM := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₂_le : ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hpoly₁ : polyP C₁ M₁ ν c ≤ polyP (max C₁ C₂) (max M₁ M₂) ν c := by
    unfold polyP
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hX1 (le_max_left _ _))
      (by positivity) (hC₁.le.trans (le_max_left _ _))
  have hpoly₂ : polyP C₂ M₂ ν c ≤ polyP (max C₁ C₂) (max M₁ M₂) ν c := by
    unfold polyP
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hX1 (le_max_right _ _))
      (by positivity) (hC₁.le.trans (le_max_left _ _))
  refine ⟨hTails.1 ρ hρ ν hν tr htr,
    fun j => ⟨PartI_T23.integrable_pow_mul_meanStream_zero hc1 tr j, hM ν hν hνM_le tr htr⟩,
    fun s hs => ?_, fun s hs => ?_⟩
  · have hRs := hR ν hν hν₁_le tr htr s hs
    have hs_pos : 0 ≤ s := zero_le_one.trans hs
    refine hRs.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hpoly₁ (Real.rpow_nonneg hs_pos _)
  · have hSs := hS ν hν hν₂_le tr htr s hs
    have h1s_pos : 0 ≤ 1 + s := by linarith
    refine hSs.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hpoly₂ (Real.rpow_nonneg h1s_pos _)

end UnforcedLeray.Short.PartI
