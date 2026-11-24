import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1_1_1
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Late-age velocity sup: `lateVelSup_of` (task `PartIII-b:C/rep/8/2/pres/4/2/1/1/1/1`)

Source `the November 2 reference manuscript` 2715-2725 (late ages), using
Part I `sct:expansion` (447-459, mean stream, `b = 1`, `p = ∞`) and `sct:fluctuation` (439-446).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.LateVelAux

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

/-- A continuous real function bounded a.e. by `B` is bounded everywhere by `B`. -/
theorem pw_of_ae_le {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ≥0∞}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ₑ ≤ B) (x : ℝ) : ‖f x‖ₑ ≤ B := by
  by_contra hx
  simp only [not_le] at hx
  have hU : IsOpen {y : ℝ | B < ‖f y‖ₑ} := isOpen_lt continuous_const hf.enorm
  have hpos : 0 < (volume : Measure ℝ) {y : ℝ | B < ‖f y‖ₑ} := hU.measure_pos volume ⟨x, hx⟩
  have hae : (volume : Measure ℝ) {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = 0 := ae_iff.1 h
  have hset : {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = {y : ℝ | B < ‖f y‖ₑ} := by
    ext y
    simp [not_le]
  rw [hset] at hae
  exact absurd hae (ne_of_gt hpos)

/-- An `eLpNorm ⊤` bound by `ofReal B` gives the pointwise real bound, for continuous `f`. -/
theorem norm_le_of_eLpNorm_top {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f ⊤ (volume : Measure ℝ) ≤ ENNReal.ofReal B) (x : ℝ) : ‖f x‖ ≤ B := by
  have h1 : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal B := by
    have h0 := enorm_ae_le_eLpNormEssSup f (volume : Measure ℝ)
    rw [← eLpNorm_exponent_top] at h0
    filter_upwards [h0] with y hy
    exact hy.trans h
  have h2 := pw_of_ae_le hf h1 x
  rw [Real.enorm_eq_ofReal_abs] at h2
  rw [Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h2

/-- Norm on `Vec2` is bounded by the sum of the absolute components. -/
theorem vec_norm_le_comp (x : UnforcedLeray.Cyl.Vec2) : ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  simp only [Real.norm_eq_abs]
  nlinarith [sq_abs (x 0), sq_abs (x 1), abs_nonneg (x 0), abs_nonneg (x 1),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

/-- The horizontal average of a continuous `Vec2` field is bounded by its component averages. -/
theorem hmean_norm_le_comp {c : ℝ} (hc : 0 < c) (f : Plane → UnforcedLeray.Cyl.Vec2)
    (hf : Continuous f) (η : ℝ) :
    ‖hmean c f η‖ ≤ |hmean c (fun z => f z 0) η| + |hmean c (fun z => f z 1) η| := by
  have hint : IntegrableOn (fun q : ℝ => f (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h0 : (∫ q in Ioc (-c / 2) (c / 2), f (q, η)) 0 = ∫ q in Ioc (-c / 2) (c / 2), f (q, η) 0 := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (0 : Fin 2)) hint
    simpa using this.symm
  have h1 : (∫ q in Ioc (-c / 2) (c / 2), f (q, η)) 1 = ∫ q in Ioc (-c / 2) (c / 2), f (q, η) 1 := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (1 : Fin 2)) hint
    simpa using this.symm
  have key : ‖∫ q in Ioc (-c / 2) (c / 2), f (q, η)‖ ≤
      |∫ q in Ioc (-c / 2) (c / 2), f (q, η) 0| + |∫ q in Ioc (-c / 2) (c / 2), f (q, η) 1| := by
    rw [← h0, ← h1]
    exact vec_norm_le_comp _
  simp only [hmean, smul_eq_mul]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), f (q, η)‖
      ≤ c⁻¹ * (|∫ q in Ioc (-c / 2) (c / 2), f (q, η) 0| + |∫ q in Ioc (-c / 2) (c / 2), f (q, η) 1|) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hc.le)
    _ = |c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), f (q, η) 0| + |c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), f (q, η) 1| := by
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hc)]
        ring

/-- The period `trainPeriod 2 ν = (ν⁻¹)²`. -/
theorem trainPeriod_two_eq {ν : ℝ} (hν : 0 < ν) : trainPeriod 2 ν = (ν⁻¹) ^ 2 := by
  unfold trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]

theorem trainPeriod_two_pos {ν : ℝ} (hν : 0 < ν) : 0 < trainPeriod 2 ν := by
  rw [trainPeriod_two_eq hν]
  positivity

/-- Mean-stream slope bound (from `TrainMeanExpansion`, `b = 1`, `p = ∞`). -/
theorem mean_slope_bound (hME : TrainMeanExpansion) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ c : ℝ, c = trainPeriod 2 ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → ∀ η : ℝ,
          |deriv (fun e => meanStream tr s e) η| ≤ polyP C M ν c * (1 + s)⁻¹ := by
  obtain ⟨C, M, ν₀, hC, hν₀, hb⟩ := hME 2 (by norm_num) 0 0 1 0 ⊤ le_top
  refine ⟨C, M, ν₀, hC, hν₀, ?_⟩
  intro ν hν hνle c hc tr htr s hs η
  subst hc
  have hcpos := trainPeriod_two_pos hν
  obtain ⟨-, -, -, hb2⟩ := hb ν hν hνle tr htr
  have hb3 := hb2 s hs.le
  simp only [pow_zero, one_mul, iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_zero,
    Nat.cast_one, ENNReal.toReal_top, inv_zero, zero_div, add_zero, zero_sub, sub_zero] at hb3
  rw [show ((-1:ℝ) - 1) / 2 = -1 by norm_num, Real.rpow_neg_one] at hb3
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hmeanContDiff (trainPeriod 2 ν) hcpos tr.ψ (trainStreamSmooth ν (trainPeriod 2 ν) hν hcpos tr htr)
  have hslice : ContDiff ℝ ∞ (fun e : ℝ => meanStream tr s e) :=
    t01_contDiff_slice hS hs
  have hcont : Continuous (deriv (fun e : ℝ => meanStream tr s e)) :=
    (contDiff_infty_iff_deriv.1 hslice).2.continuous
  have hB : 0 ≤ polyP C M ν (trainPeriod 2 ν) * (1 + s)⁻¹ := by
    unfold polyP
    have h1 : 0 ≤ 1 + trainPeriod 2 ν + ν⁻¹ := by
      have := hcpos.le
      have := inv_nonneg.2 hν.le
      linarith
    have h2 : 0 ≤ (1 + s)⁻¹ := inv_nonneg.2 (by linarith)
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg h1 M)) h2
  have := norm_le_of_eLpNorm_top hcont hB hb3 η
  rw [Real.norm_eq_abs] at this
  exact this

/-- Fluctuation bound (from `TrainFluctuationDecay`, `m = ℓ = j = 0`). -/
theorem fluct_bound (hFD : TrainFluctuationDecay) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ c : ℝ, c = trainPeriod 2 ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → ∀ z : Plane,
          ‖hfluct c (tr.v s) z‖ ≤ polyP C N ν c * Real.exp (-(κ * ν * s / c ^ 2)) := by
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, hb⟩ := hFD 2 (by norm_num) 0 0 0
  refine ⟨C, N, κ, ν₀, hC, hκ, hν₀, ?_⟩
  intro ν hν hνle c hc tr htr s hs z
  subst hc
  have hcpos := trainPeriod_two_pos hν
  have hF := (hb ν hν hνle tr htr s hs).2.1.2
  have hle : ‖ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s z‖ₑ ≤
      wSupNorm 0 (ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s) := by
    unfold wSupNorm
    refine le_trans ?_ (le_iSup _ z)
    simp [UnforcedLeray.Train.jap]
  have hage : ‖ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s z‖ =
      ‖hfluct (trainPeriod 2 ν) (tr.v s) z‖ := by
    simp [ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]
  have hK0 : 0 ≤ polyP C N ν (trainPeriod 2 ν) * Real.exp (-(κ * ν * s / trainPeriod 2 ν ^ 2)) := by
    unfold polyP
    have h1 : 0 ≤ 1 + trainPeriod 2 ν + ν⁻¹ := by
      have := hcpos.le
      have := inv_nonneg.2 hν.le
      linarith
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg h1 N)) (Real.exp_pos _).le
  have h2 : ‖ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s z‖ₑ ≤
      ENNReal.ofReal (polyP C N ν (trainPeriod 2 ν) * Real.exp (-(κ * ν * s / trainPeriod 2 ν ^ 2))) :=
    hle.trans hF
  calc ‖hfluct (trainPeriod 2 ν) (tr.v s) z‖
      = ‖ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s z‖ := hage.symm
    _ = ‖ageJet 0 0 (fun r => hfluct (trainPeriod 2 ν) (tr.v r)) s z‖ₑ.toReal := (toReal_enorm _).symm
    _ ≤ _ := ENNReal.toReal_le_of_le_ofReal hK0 h2

/-- Polynomial majorant: `polyP C N ν (ν⁻¹²) ≤ C 3^N ν⁻¹^(2N)` for `0 < ν ≤ 1`. -/
theorem polyP_le (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    polyP C N ν ((ν⁻¹) ^ 2) ≤ C * 3 ^ N * (ν⁻¹) ^ (2 * N) := by
  unfold polyP
  have hq1 : 1 ≤ ν⁻¹ := (one_le_inv_iff₀).2 ⟨hν, hν1⟩
  have h1 : 1 + (ν⁻¹) ^ 2 + ν⁻¹ ≤ 3 * (ν⁻¹) ^ 2 := by nlinarith
  have hbase : 0 ≤ 1 + (ν⁻¹) ^ 2 + ν⁻¹ := by nlinarith [sq_nonneg (ν⁻¹)]
  have h2 := pow_le_pow_left₀ hbase h1 N
  have h3 : (3 * (ν⁻¹) ^ 2) ^ N = 3 ^ N * (ν⁻¹) ^ (2 * N) := by
    rw [mul_pow, ← pow_mul]
  calc C * (1 + (ν⁻¹) ^ 2 + ν⁻¹) ^ N ≤ C * (3 * (ν⁻¹) ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left h2 hC
    _ = C * 3 ^ N * (ν⁻¹) ^ (2 * N) := by rw [h3, mul_assoc]

/-- Exponential factor: `√s · exp(-κνs/c²) ≤ ν⁻¹⁵/κ` with `c = ν⁻¹²`, `s > 1/ν`. -/
theorem exp_bound (κ ν s : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 1 / ν < s) :
    Real.sqrt s * Real.exp (-(κ * ν * s / ((ν⁻¹) ^ 2) ^ 2)) ≤ (ν⁻¹) ^ 5 / κ := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hq1 : 1 ≤ ν⁻¹ := (one_le_inv_iff₀).2 ⟨hν, hν1⟩
  have hqnn : 0 ≤ ν⁻¹ := by linarith
  have hs1 : 1 ≤ s := le_trans (one_le_one_div hν hν1) hs.le
  have hs0 : 0 < s := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x, x = κ * ν * s / ((ν⁻¹) ^ 2) ^ 2 := ⟨_, rfl⟩
  rw [← hxdef]
  have hsx : s = (((ν⁻¹) ^ 2) ^ 2 / (κ * ν)) * x := by
    rw [hxdef]
    field_simp
  have hB : ((ν⁻¹) ^ 2) ^ 2 / (κ * ν) = (ν⁻¹) ^ 5 / κ := by
    field_simp
  have hxe : x * Real.exp (-x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : x ≤ Real.exp x := by linarith
    have he : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
    nlinarith [mul_nonneg (sub_nonneg.2 h3) he]
  have hsq : Real.sqrt s ≤ s := by
    have h1 : 1 ≤ Real.sqrt s := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hs1
    have h2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
    nlinarith
  calc Real.sqrt s * Real.exp (-x) ≤ s * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = (ν⁻¹) ^ 5 / κ * (x * Real.exp (-x)) := by
        rw [hsx, hB]
        ring
    _ ≤ (ν⁻¹) ^ 5 / κ * 1 :=
        mul_le_mul_of_nonneg_left hxe (div_nonneg (pow_nonneg hqnn 5) hκ.le)
    _ = (ν⁻¹) ^ 5 / κ := mul_one _

open UnforcedLeray.Short.PartIIIb.Concrete.LateVelAux in
theorem lateVelSup_of (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    UnforcedLeray.Short.PartIIIb.Concrete.VelSupSub.LateVelSup := by
  obtain ⟨CM, Mm, νM, hCM, hνM, hMb⟩ := mean_slope_bound hME
  obtain ⟨CF, N, κ, νF, hCF, hκ, hνF, hFb⟩ := fluct_bound hFD
  refine ⟨CM * 3 ^ Mm + CF * 3 ^ N / κ, 2 * N + 2 * Mm + 5, min (min νM νF) 1,
    lt_min (lt_min hνM hνF) one_pos, ?_⟩
  intro ν hν hνa tr htr s hs z
  have hν1 : ν ≤ 1 := hνa.trans (min_le_right _ _)
  have hνM' : ν ≤ νM := hνa.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνF' : ν ≤ νF := hνa.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs0 : 0 < s := lt_of_le_of_lt (one_div_nonneg.2 hν.le) hs
  have hs1 : 1 ≤ s := le_trans (one_le_one_div hν hν1) hs.le
  have hcEq : cOf ν = trainPeriod 2 ν := by
    unfold cOf trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  have hcq : cOf ν = (ν⁻¹) ^ 2 := by
    unfold cOf
    rw [inv_pow]
  have hqnn : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hcpos : 0 < cOf ν := by
    rw [hcq]
    exact pow_pos (inv_pos.2 hν) 2
  have hsq : Real.sqrt s ≤ s := by
    have h1 : 1 ≤ Real.sqrt s := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hs1
    have h2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
    nlinarith
  have hsq1 : Real.sqrt s * (1 + s)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hsqrt_nn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  -- mean-stream and fluctuation bounds
  have hB := hMb ν hν hνM' (cOf ν) hcEq tr htr s hs0
  have hF := hFb ν hν hνF' (cOf ν) hcEq tr htr s hs0 z
  have hpolyF : polyP CF N ν (cOf ν) ≤ CF * 3 ^ N * (ν⁻¹) ^ (2 * N) := by
    rw [hcq]
    exact polyP_le CF hCF.le N ν hν hν1
  have hexpF : Real.sqrt s * Real.exp (-(κ * ν * s / (cOf ν) ^ 2)) ≤ (ν⁻¹) ^ 5 / κ := by
    rw [hcq]
    exact exp_bound κ ν s hκ hν hν1 hs
  have hpolyM : polyP CM Mm ν (cOf ν) ≤ CM * 3 ^ Mm * (ν⁻¹) ^ (2 * Mm) := by
    rw [hcq]
    exact polyP_le CM hCM.le Mm ν hν hν1
  have hbaseC : 0 ≤ 1 + cOf ν + ν⁻¹ := by linarith
  have hPF0 : 0 ≤ polyP CF N ν (cOf ν) := by
    unfold polyP
    exact mul_nonneg hCF.le (pow_nonneg hbaseC N)
  have hPM0 : 0 ≤ polyP CM Mm ν (cOf ν) := by
    unfold polyP
    exact mul_nonneg hCM.le (pow_nonneg hbaseC Mm)
  -- continuity of the velocity on the slice `s > 0`
  have hcontS : Continuous (tr.v s) := by
    have h := tr.isTrain.smooth_v.continuousOn
    have hm : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    exact h.comp_continuous hm (fun z => ⟨hs0.le, mem_univ z⟩)
  -- the mean velocity components
  have hm0 := trainMeanV1 ν (cOf ν) hν hcpos tr s hs0 z.2
  have hm1 := trainMeanV2 ν (cOf ν) hν hcpos tr s hs0 z.2
  have hmn := hmean_norm_le_comp hcpos (tr.v s) hcontS z.2
  rw [hm0, hm1, abs_neg, abs_zero, add_zero] at hmn
  have hv : tr.v s z = hfluct (cOf ν) (tr.v s) z + hmean (cOf ν) (tr.v s) z.2 := by
    unfold hfluct
    exact (sub_add_cancel _ _).symm
  have hnorm : ‖tr.v s z‖ ≤ ‖hfluct (cOf ν) (tr.v s) z‖ +
      polyP CM Mm ν (cOf ν) * (1 + s)⁻¹ := by
    calc ‖tr.v s z‖ = ‖hfluct (cOf ν) (tr.v s) z + hmean (cOf ν) (tr.v s) z.2‖ := by
          rw [← hv]
      _ ≤ ‖hfluct (cOf ν) (tr.v s) z‖ + ‖hmean (cOf ν) (tr.v s) z.2‖ := norm_add_le _ _
      _ ≤ ‖hfluct (cOf ν) (tr.v s) z‖ + |deriv (fun e => meanStream tr s e) z.2| :=
          add_le_add le_rfl hmn
      _ ≤ ‖hfluct (cOf ν) (tr.v s) z‖ + polyP CM Mm ν (cOf ν) * (1 + s)⁻¹ :=
          add_le_add le_rfl (hB z.2)
  have hA : Real.sqrt s * ‖hfluct (cOf ν) (tr.v s) z‖ ≤
      (CF * 3 ^ N * (ν⁻¹) ^ (2 * N)) * ((ν⁻¹) ^ 5 / κ) := by
    calc Real.sqrt s * ‖hfluct (cOf ν) (tr.v s) z‖
        ≤ Real.sqrt s * (polyP CF N ν (cOf ν) * Real.exp (-(κ * ν * s / (cOf ν) ^ 2))) :=
          mul_le_mul_of_nonneg_left hF hsqrt_nn
      _ = polyP CF N ν (cOf ν) * (Real.sqrt s * Real.exp (-(κ * ν * s / (cOf ν) ^ 2))) := by ring
      _ ≤ (CF * 3 ^ N * (ν⁻¹) ^ (2 * N)) * ((ν⁻¹) ^ 5 / κ) :=
          mul_le_mul hpolyF hexpF (mul_nonneg hsqrt_nn (Real.exp_pos _).le)
            (mul_nonneg (mul_nonneg hCF.le (by positivity)) (pow_nonneg hqnn _))
  have hBm : Real.sqrt s * (polyP CM Mm ν (cOf ν) * (1 + s)⁻¹) ≤
      CM * 3 ^ Mm * (ν⁻¹) ^ (2 * Mm) := by
    calc Real.sqrt s * (polyP CM Mm ν (cOf ν) * (1 + s)⁻¹)
        = polyP CM Mm ν (cOf ν) * (Real.sqrt s * (1 + s)⁻¹) := by ring
      _ ≤ polyP CM Mm ν (cOf ν) * 1 := mul_le_mul_of_nonneg_left hsq1 hPM0
      _ = polyP CM Mm ν (cOf ν) := mul_one _
      _ ≤ CM * 3 ^ Mm * (ν⁻¹) ^ (2 * Mm) := hpolyM
  have hq1 : 1 ≤ ν⁻¹ := (one_le_inv_iff₀).2 ⟨hν, hν1⟩
  calc Real.sqrt s * ‖tr.v s z‖
      ≤ Real.sqrt s * (‖hfluct (cOf ν) (tr.v s) z‖ + polyP CM Mm ν (cOf ν) * (1 + s)⁻¹) :=
        mul_le_mul_of_nonneg_left hnorm hsqrt_nn
    _ = Real.sqrt s * ‖hfluct (cOf ν) (tr.v s) z‖ +
          Real.sqrt s * (polyP CM Mm ν (cOf ν) * (1 + s)⁻¹) := by ring
    _ ≤ (CF * 3 ^ N * (ν⁻¹) ^ (2 * N)) * ((ν⁻¹) ^ 5 / κ) +
          CM * 3 ^ Mm * (ν⁻¹) ^ (2 * Mm) := add_le_add hA hBm
    _ = (CF * 3 ^ N / κ) * (ν⁻¹) ^ (2 * N + 5) + (CM * 3 ^ Mm) * (ν⁻¹) ^ (2 * Mm) := by ring
    _ ≤ (CF * 3 ^ N / κ) * (ν⁻¹) ^ (2 * N + 2 * Mm + 5) +
          (CM * 3 ^ Mm) * (ν⁻¹) ^ (2 * N + 2 * Mm + 5) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by omega))
            (div_nonneg (mul_nonneg hCF.le (by positivity)) hκ.le))
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by omega))
            (mul_nonneg hCM.le (by positivity)))
    _ = (CM * 3 ^ Mm + CF * 3 ^ N / κ) * (ν⁻¹) ^ (2 * N + 2 * Mm + 5) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.LateVelAux
