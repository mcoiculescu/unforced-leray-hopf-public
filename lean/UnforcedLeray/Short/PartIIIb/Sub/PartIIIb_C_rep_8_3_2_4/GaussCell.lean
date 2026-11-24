import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_4
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureLap

/-!
# `PartIII-b:C/rep/8/3/2/4/2`: `GaussCellFromPartI`

Source `the November 2 reference manuscript` 5484-5492, Part I 468-478.
Pointwise `jet ≤ 4(a+b+P)` gives `jet² ≤ 48(a²+b²+P²)`; the cell integrals of `a²,b²,P²` are the
squared cell `L²` norms of `TrainPartICell`; `avgμ c = ofReal c⁻¹ • cellμ c` with `c ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Train UnforcedLeray.Cyl

/-- `V_c^p` is continuous on each slice (Schwartz profile `uc k a`, `Gaussian.contDiff_periodize`). -/
theorem vc_continuous {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 < s) :
    Continuous (UnforcedLeray.Train.Vc ν c s) := by
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs.le
  have hsm : ∀ k : Fin 2, Continuous (fun z =>
      UnforcedLeray.B0146.latticeSum c (UnforcedLeray.B0146.uc k
        (UnforcedLeray.B0113.heatWidth ν s)) z) := fun k => by
    have h := UnforcedLeray.Short.PartI.LatticeProfileDecay_of_SchFn
      (UnforcedLeray.Short.PartI.SchFn_uc ha k)
    exact (UnforcedLeray.Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc.ne' h.1
      (fun n _ => h.2 n)).continuous
  rw [UnforcedLeray.Train.Vc_slice_eq]
  have h1 : Continuous fun w => UnforcedLeray.B0146.periodicVelocity ν c s w := by
    have : (fun w => UnforcedLeray.B0146.periodicVelocity ν c s w) = fun w =>
        (UnforcedLeray.B0146.latticeSum c (UnforcedLeray.B0146.uc 0
          (UnforcedLeray.B0113.heatWidth ν s)) w,
         UnforcedLeray.B0146.latticeSum c (UnforcedLeray.B0146.uc 1
          (UnforcedLeray.B0113.heatWidth ν s)) w) :=
      funext (UnforcedLeray.B0146.periodicVelocity_eq hc.ne' ha)
    rw [this]
    exact (hsm 0).prodMk (hsm 1)
  exact toVecL.continuous.comp h1

/-- Classical partial in `q` of a differentiable function. -/
theorem partialQ_eq_fderiv {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    partialQ f z = fderiv ℝ f z (1, 0) := by
  unfold partialQ
  have h : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const _ _)
  exact ((hf (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h).deriv

/-- Classical partial in `η` of a differentiable function. -/
theorem partialEta_eq_fderiv {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    partialEta f z = fderiv ℝ f z (0, 1) := by
  unfold partialEta
  have h : HasDerivAt (fun q : ℝ => (z.1, q)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id z.2)
  exact ((hf (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h).deriv

theorem measurable_norm_gradS {f : Plane → ℝ} (hf : Differentiable ℝ f) :
    Measurable fun x => ‖UnforcedLeray.Train.gradS f x‖ := by
  have h1 : Measurable fun x => partialQ f x := by
    have := measurable_fderiv_apply_const ℝ f ((1 : ℝ), (0 : ℝ))
    simpa only [partialQ_eq_fderiv hf] using this
  have h2 : Measurable fun x => partialEta f x := by
    have := measurable_fderiv_apply_const ℝ f ((0 : ℝ), (1 : ℝ))
    simpa only [partialEta_eq_fderiv hf] using this
  exact (toVecL.continuous.measurable.comp (h1.prodMk h2)).norm

/-- `∫⁻ ofReal(f²) = ‖f‖₂²`. -/
theorem lintegral_ofReal_sq_eq {μ : Measure Plane} (f : Plane → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [ENNReal.rpow_natCast] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Target.** -/
theorem gaussCellFromPartI : GaussCellFromPartI := by
  intro hP hS hC
  obtain ⟨C, N, CS, bS, ν₀, hC0, hbS, hν0, hcell⟩ := hC
  refine ⟨7 * C * 3 ^ N, 2 * N, CS, bS, min ν₀ 1, by positivity, hbS, lt_min hν0 one_pos, ?_⟩
  intro L hL hν s hs hs'
  have hνpos : 0 < L.ν := L.ν_pos
  have hν1 : L.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνν : L.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hcell' := hcell L hL hνν s hs hs'
  have hcpos : 0 < cOf L.ν := cOf_pos hνpos
  have hc1 : 1 ≤ cOf L.ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  -- slices
  obtain ⟨hV2, hPd⟩ := hS L s hs.le
  set a : Plane → ℝ := fun x => ‖L.train.v s x - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s x‖ with ha
  set b : Plane → ℝ := fun x => ‖iteratedFDeriv ℝ 2
    (fun z => L.train.v s z - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s z) x‖ with hb
  set P : Plane → ℝ := fun x => ‖UnforcedLeray.Train.gradS
    (fun w => L.train.p s w - UnforcedLeray.Train.pc L.ν (cOf L.ν) s w) x‖ with hPdef
  have hvcont : Continuous (L.train.v s) := by
    have h : L.train.v s = fun x => toVecL (trainV L s x) := by
      funext x; ext i; fin_cases i <;> rfl
    rw [h]
    exact toVecL.continuous.comp hV2.continuous
  have ha_meas : Measurable a :=
    (hvcont.sub (vc_continuous hνpos hcpos hs)).norm.measurable
  have hP_meas : Measurable P := by
    refine measurable_norm_gradS ?_
    exact (show Differentiable ℝ (L.train.p s) from hPd).sub
      ((UnforcedLeray.Short.PartI.ErrPressureLapAux.pc_contDiff hνpos hcpos hs.le).differentiable
        (by simp))
  -- pointwise bound
  have hpt : ∀ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ≤
      48 * (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) + ENNReal.ofReal (P x ^ 2)) := by
    intro x
    have h0 := hP L s hs x
    have hj : 0 ≤ trainGaussJet L s x := by
      unfold trainGaussJet flatHessNorm
      have := norm_nonneg (trainDV L s x)
      have h2 : 0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
          ‖fderiv ℝ (fun y => fderiv ℝ (trainDV L s) y (ei b)) x (ei a)‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have := norm_nonneg (mgrad (trainDP L s) x)
      linarith
    have h1 : trainGaussJet L s x ^ 2 ≤ 48 * (a x ^ 2 + b x ^ 2 + P x ^ 2) := by
      have e := pow_le_pow_left₀ hj h0 2
      have := norm_nonneg (L.train.v s x - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s x)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - P x), sq_nonneg (b x - P x)]
    calc ENNReal.ofReal (trainGaussJet L s x ^ 2)
        ≤ ENNReal.ofReal (48 * (a x ^ 2 + b x ^ 2 + P x ^ 2)) := ENNReal.ofReal_le_ofReal h1
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  have hint : ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(cellμ (cOf L.ν)) ≤
      48 * (eLpNorm a 2 (cellμ (cOf L.ν)) ^ 2 + eLpNorm b 2 (cellμ (cOf L.ν)) ^ 2 +
        eLpNorm P 2 (cellμ (cOf L.ν)) ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(cellμ (cOf L.ν))
        ≤ ∫⁻ x, 48 * (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) +
            ENNReal.ofReal (P x ^ 2)) ∂(cellμ (cOf L.ν)) := lintegral_mono hpt
      _ = 48 * ∫⁻ x, (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) +
            ENNReal.ofReal (P x ^ 2)) ∂(cellμ (cOf L.ν)) :=
          lintegral_const_mul' _ _ (by simp)
      _ = _ := by
        rw [lintegral_add_right _ ((hP_meas.pow_const 2).ennreal_ofReal),
          lintegral_add_left ((ha_meas.pow_const 2).ennreal_ofReal),
          lintegral_ofReal_sq_eq, lintegral_ofReal_sq_eq, lintegral_ofReal_sq_eq]
  set Ea := eLpNorm a 2 (cellμ (cOf L.ν)) with hEa
  set Eb := eLpNorm b 2 (cellμ (cOf L.ν)) with hEb
  set Ep := eLpNorm P 2 (cellμ (cOf L.ν)) with hEp
  set M : ℝ := C * (1 + cOf L.ν + L.ν⁻¹) ^ N * Real.exp (CS / L.ν - bS * cOf L.ν ^ 2) with hM
  have hsq : Ea ^ 2 + Eb ^ 2 + Ep ^ 2 ≤ (ENNReal.ofReal M) ^ 2 := by
    calc Ea ^ 2 + Eb ^ 2 + Ep ^ 2 ≤ (Ea + Eb + Ep) ^ 2 := by
          have : (Ea + Eb + Ep) ^ 2 = (Ea ^ 2 + Eb ^ 2 + Ep ^ 2) +
              (2 * Ea * Eb + 2 * Ea * Ep + 2 * Eb * Ep) := by ring
          rw [this]; exact le_self_add
      _ ≤ (ENNReal.ofReal M) ^ 2 := by gcongr
  have hinv : 1 ≤ L.ν⁻¹ := one_le_inv₀ hνpos |>.2 hν1
  have hcsq : cOf L.ν = L.ν⁻¹ ^ 2 := by unfold cOf; rw [inv_pow]
  have hbase : (1 + cOf L.ν + L.ν⁻¹) ^ N ≤ 3 ^ N * L.ν⁻¹ ^ (2 * N) := by
    rw [pow_mul, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    rw [← hcsq]
    have : L.ν⁻¹ ≤ cOf L.ν := by rw [hcsq]; nlinarith
    linarith
  set E : ℝ := Real.exp (CS / L.ν - bS * cOf L.ν ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hM0 : 0 ≤ M := by positivity
  have hMle : M ≤ C * 3 ^ N * L.ν⁻¹ ^ (2 * N) * E := by
    calc M = C * (1 + cOf L.ν + L.ν⁻¹) ^ N * E := rfl
      _ ≤ C * (3 ^ N * L.ν⁻¹ ^ (2 * N)) * E := by gcongr
      _ = _ := by ring
  have hreal : 48 * M ^ 2 ≤ ((7 * C * 3 ^ N) * L.ν⁻¹ ^ (2 * N) * deltaBase CS bS L.ν) ^ 2 := by
    have hd : deltaBase CS bS L.ν = E := rfl
    rw [hd]
    have e : (7 * C * 3 ^ N) * L.ν⁻¹ ^ (2 * N) * E = 7 * (C * 3 ^ N * L.ν⁻¹ ^ (2 * N) * E) := by
      ring
    rw [e]
    have := pow_le_pow_left₀ hM0 hMle 2
    nlinarith [sq_nonneg (C * 3 ^ N * L.ν⁻¹ ^ (2 * N) * E)]
  have havg : ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(avgμ (cOf L.ν)) ≤
      ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(cellμ (cOf L.ν)) := by
    unfold avgμ
    rw [lintegral_smul_measure]
    calc ENNReal.ofReal (cOf L.ν)⁻¹ * _ ≤ 1 * _ := by
          gcongr
          exact ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ hc1)
      _ = _ := one_mul _
  calc ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(avgμ (cOf L.ν))
      ≤ 48 * (Ea ^ 2 + Eb ^ 2 + Ep ^ 2) := havg.trans hint
    _ ≤ 48 * (ENNReal.ofReal M) ^ 2 := by gcongr
    _ = ENNReal.ofReal (48 * M ^ 2) := by
        rw [← ENNReal.ofReal_pow hM0, show (48 : ℝ≥0∞) = ENNReal.ofReal 48 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end UnforcedLeray.Short.PartIIIb.Concrete

end
