import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H5
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/2`: `AmplMovingFTC` from the age-time amplitude identity

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918
(`(ΛW)' = H₀W` in moving time), 2991-3000 (normalised amplitudes `a_j = N⁻¹ α_j`,
`a_j' = N⁻¹ (H₀)_j W - β₀ a_j`).

Proved here: `amplMovingFTC_of : AmplAgeFTC κ → AmplMovingFTC κ`.  The leaf `AmplAgeFTC` is the
un-normalised amplitude identity in age time, `α_j(s) - α_j(t₁) = ∫_{t₁}^{s} a(r)⁻² (H₀)_j W(r) dr`
with the integrability of the integrand on the block.  The reduction:
* change of variables `r = s(σ)` (`ds/dσ = a(s)²`, `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
  for `r ↦ z(r) - z(t₁)`), giving `α_j(s(σ))` as a primitive of `(H₀)_j W(s(σ))` (`ampl_primitive`);
* the normaliser `N(t₁, s(σ))⁻¹` is `C¹` in `σ` with derivative `-β₀ N⁻¹` (`hasDerivAt_ageAt`,
  `hasDerivAt_clockN_movBeta0`);
* product rule for primitives (`mul_sub_mul_of_primitive`).

Regime remark: `AmplAgeFTC` quantifies over all `b ≥ 1`, `ν > 0` like `AmplMovingFTC`.  The proved
amplitude identity `AmplWeakFTC` (`amplWeakFTC`, `Sub/PartIII-a_T21_c5.lean`) is only available for
`b ≥ b₀`, `ν ≤ ν₀`, and does not export the integrability of the integrand.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

/-- **Leaf (`(ΛW)' = H₀W` in age time, SP 2898-2918)**: along a linearised flow from age `t₁`, the
un-normalised amplitude `α_j(s) = Λ_j W(s)` is the primitive of `a(r)⁻² (H₀)_j W(r)` on the block
`[t₁, t₂]`, and this integrand is integrable there. -/
def AmplAgeFTC (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K b : ℝ, 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ j : Fin 2,
            IntegrableOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
              movH0 κ tr r j (movingW ν w r)) (Ioc t₁ t₂) ∧
            ∀ s ∈ Icc t₁ t₂, ampl (periodizedFrame κ ν m b K hν hF) w s j =
              ampl (periodizedFrame κ ν m b K hν hF) w t₁ j +
                ∫ r in t₁..s, (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr r j (movingW ν w r)

namespace AmplMovingSub

theorem clockA_pos' {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 < clockA ν r := by
  unfold clockA; positivity

/-- Strict monotonicity of the moving time on `[0, ∞)`. -/
theorem movingZ_lt {ν r r' : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrr : r < r') :
    movingZ ν r < movingZ ν r' := by
  have hr' : 0 ≤ r' := hr.trans hrr.le
  unfold movingZ clockA
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem movingZ_le {ν r r' : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrr : r ≤ r') :
    movingZ ν r ≤ movingZ ν r' := by
  rcases hrr.lt_or_eq with h | h
  · exact (movingZ_lt hν hr h).le
  · rw [h]

/-- `z(s(σ)) = z(t₁) + σ` on the block. -/
theorem movingZ_ageAt {ν t₁ σ : ℝ} (hlt : ν * (movingZ ν t₁ + σ) < 1) :
    movingZ ν (ageAt ν t₁ σ) = movingZ ν t₁ + σ := by
  unfold ageAt
  exact FrameStableSub.movingZ_moveAgeOfZ hlt

/-- `ds/dσ = a(s)²`. -/
theorem hasDerivAt_ageAt {ν t₁ σ : ℝ} (hlt : ν * (movingZ ν t₁ + σ) < 1) :
    HasDerivAt (ageAt ν t₁) ((clockA ν (ageAt ν t₁ σ)) ^ 2) σ := by
  have hz : 0 < 1 - ν * (movingZ ν t₁ + σ) := by linarith
  have h1 : HasDerivAt (fun x : ℝ => movingZ ν t₁ + x) 1 σ := (hasDerivAt_id σ).const_add _
  have h2 : HasDerivAt (fun x : ℝ => 1 - ν * (movingZ ν t₁ + x)) (-(ν * 1)) σ := by
    simpa using (h1.const_mul ν).const_sub 1
  have h3 := h1.div h2 hz.ne'
  have heq : ageAt ν t₁ = fun x : ℝ => (movingZ ν t₁ + x) / (1 - ν * (movingZ ν t₁ + x)) := by
    funext x
    rfl
  rw [heq]
  refine h3.congr_deriv ?_
  unfold clockA
  field_simp
  ring

theorem clockN_pos (P : PlanarData) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < clockN P ν t s := by
  unfold clockN
  exact mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (div_pos (theta_pos hν ht) (theta_pos hν hs)) _)

theorem movBeta0_eq (P : PlanarData) (ν r : ℝ) :
    movBeta0 P ν r = P.eigenvalue.re + P.kappa.re * (ν * clockA ν r) := by
  unfold movBeta0 clockTheta
  rw [div_inv_eq_mul]

theorem continuous_movBeta0 (P : PlanarData) (ν : ℝ) : Continuous (movBeta0 P ν) := by
  have h : movBeta0 P ν = fun r => P.eigenvalue.re + P.kappa.re * (ν * clockA ν r) := by
    funext r
    exact movBeta0_eq P ν r
  rw [h]
  unfold clockA
  fun_prop

/-- **Change of variables `r = s(σ)`** on `[0, x]`: `∫₀ˣ G(s(σ)) dσ = ∫_{t₁}^{s(x)} a(r)⁻² G(r) dr`,
with the integrability transfer. -/
theorem cov {ν t₁ t₂ B : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hBe : movingZ ν t₂ - movingZ ν t₁ = B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) B) (G : ℝ → ℂ)
    (hG : IntegrableOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * G r)
      (Ioc t₁ (ageAt ν t₁ x))) :
    IntegrableOn (fun σ => G (ageAt ν t₁ σ)) (Ioc 0 x) ∧
      ∫ σ in Ioc 0 x, G (ageAt ν t₁ σ) =
        ∫ r in Ioc t₁ (ageAt ν t₁ x), (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * G r := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  set s := ageAt ν t₁ x with hs_def
  set fz : ℝ → ℝ := fun r => movingZ ν r - movingZ ν t₁ with hfz
  have hS : MeasurableSet (Ioc t₁ s) := measurableSet_Ioc
  have hderiv : ∀ r ∈ Ioc t₁ s, HasDerivWithinAt fz ((clockA ν r) ^ (-2 : ℝ)) (Ioc t₁ s) r :=
    fun r hr => (hasDerivAt_movingZ_sub t₁ hν (ht₁.trans hr.1.le)).hasDerivWithinAt
  have hinj : InjOn fz (Ioc t₁ s) := by
    intro r hr r' hr' h
    have e1 := ageAt_movingZ_sub (t₁ := t₁) hν (ht₁.trans hr.1.le)
    have e2 := ageAt_movingZ_sub (t₁ := t₁) hν (ht₁.trans hr'.1.le)
    simp only [hfz] at h
    rw [← e1, ← e2, h]
  have hltx : ν * (movingZ ν t₁ + x) < 1 := nu_mul_movingZ_add_lt_one hν ht₂ hBe hx.2
  have hzs : movingZ ν s = movingZ ν t₁ + x := movingZ_ageAt hltx
  have himg : fz '' Ioc t₁ s = Ioc 0 x := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr0 : 0 ≤ r := ht₁.trans hr.1.le
      refine ⟨?_, ?_⟩
      · simp only [hfz]
        linarith [movingZ_lt hν ht₁ hr.1]
      · simp only [hfz]
        linarith [movingZ_le hν hr0 hr.2]
    · intro hy
      have hlty : ν * (movingZ ν t₁ + y) < 1 :=
        nu_mul_movingZ_add_lt_one hν ht₂ hBe (hy.2.trans hx.2)
      have hzy : movingZ ν (ageAt ν t₁ y) = movingZ ν t₁ + y := movingZ_ageAt hlty
      have hy0 : 0 ≤ ageAt ν t₁ y :=
        ht₁.trans (ageAt_mem_Icc hν ht₁ h12 hBe ⟨hy.1.le, hy.2.trans hx.2⟩).1
      refine ⟨ageAt ν t₁ y, ⟨?_, ?_⟩, ?_⟩
      · by_contra hcon
        push_neg at hcon
        have := movingZ_le hν hy0 hcon
        linarith [hy.1]
      · exact ageAt_mono_on_block hν ht₁ ht₂ hBe hy.1.le hy.2 hx.2
      · simp only [hfz]
        rw [hzy]
        ring
  have key := integral_image_eq_integral_abs_deriv_smul hS hderiv hinj
    (fun σ => G (ageAt ν t₁ σ))
  have keyI := integrableOn_image_iff_integrableOn_abs_deriv_smul hS hderiv hinj
    (fun σ => G (ageAt ν t₁ σ))
  rw [himg] at key keyI
  have hcongr : EqOn (fun r => |(clockA ν r) ^ (-2 : ℝ)| • G (ageAt ν t₁ (fz r)))
      (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * G r) (Ioc t₁ s) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    simp only [hfz]
    rw [ageAt_movingZ_sub hν hr0,
      abs_of_pos (Real.rpow_pos_of_pos (clockA_pos' hν hr0) _), Complex.real_smul]
  refine ⟨keyI.2 (hG.congr_fun hcongr.symm hS), ?_⟩
  rw [key]
  exact setIntegral_congr_fun hS hcongr

end AmplMovingSub

open AmplMovingSub in
/-- **`AmplMovingFTC` from the age-time amplitude identity** (SP 2898-2918, 2991-3000). -/
theorem amplMovingFTC_of (κ : PlanarFrameKernels) (h : AmplAgeFTC κ) : AmplMovingFTC κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc j
  obtain ⟨hgI, hFTC⟩ :=
    h hκ P hP m hm K b hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt f w u hFlow hCirc j
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hage : ∀ x ∈ Icc (0 : ℝ) B, ageAt ν t₁ x ∈ Icc t₁ t₂ :=
    fun x hx => ageAt_mem_Icc hν ht₁ h12 hBe hx
  have hage0 : ∀ x ∈ Icc (0 : ℝ) B, 0 ≤ ageAt ν t₁ x := fun x hx => ht₁.trans (hage x hx).1
  have hlt : ∀ x ∈ Icc (0 : ℝ) B, ν * (movingZ ν t₁ + x) < 1 :=
    fun x hx => nu_mul_movingZ_add_lt_one hν ht₂ hBe hx.2
  set βh : ℝ → ℂ := fun σ => movH0 κ tr (ageAt ν t₁ σ) j (movingW ν w (ageAt ν t₁ σ))
    with hβh
  set qh : ℝ → ℂ := fun σ => ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j
    with hqh
  set ah : ℝ → ℂ := fun σ => (((clockN P ν t₁ (ageAt ν t₁ σ))⁻¹ : ℝ) : ℂ) with hah
  set αh : ℝ → ℂ := fun σ => -((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ) * ah σ with hαh
  -- primitive of `qh`
  have hq : ∀ x ∈ Icc (0 : ℝ) B,
      IntervalIntegrable βh volume 0 x ∧ qh x = qh 0 + ∫ y in (0 : ℝ)..x, βh y := by
    intro x hx
    obtain ⟨hI, hE⟩ := cov hν ht₁ h12 hBe hx (fun r => movH0 κ tr r j (movingW ν w r))
      (hgI.mono_set (Ioc_subset_Ioc le_rfl (hage x hx).2))
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2 hI, ?_⟩
    rw [intervalIntegral.integral_of_le hx.1, hE]
    simp only [hqh]
    rw [ageAt_zero hν ht₁, hFTC _ (hage x hx), intervalIntegral.integral_of_le (hage x hx).1]
  -- derivative of `ah`
  have hda : ∀ y ∈ Icc (0 : ℝ) B, HasDerivAt ah (αh y) y := by
    intro y hy
    have hs := hage0 y hy
    have hA := hasDerivAt_ageAt (hlt y hy)
    have hN := (hasDerivAt_clockN_movBeta0 P hν ht₁ hs).comp y hA
    have hNpos := AmplMovingSub.clockN_pos P hν ht₁ hs
    have hInv := hN.inv hNpos.ne'
    have hC := hInv.ofReal_comp
    have ha := clockA_pos' hν hs
    have hrp : (clockA ν (ageAt ν t₁ y)) ^ (-2 : ℝ) * (clockA ν (ageAt ν t₁ y)) ^ 2 = 1 := by
      rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (by positivity)]
    have hreal : -((clockA ν (ageAt ν t₁ y)) ^ (-2 : ℝ) * movBeta0 P ν (ageAt ν t₁ y) *
        clockN P ν t₁ (ageAt ν t₁ y) * (clockA ν (ageAt ν t₁ y)) ^ 2) /
          (clockN P ν t₁ (ageAt ν t₁ y)) ^ 2 =
        -movBeta0 P ν (ageAt ν t₁ y) * (clockN P ν t₁ (ageAt ν t₁ y))⁻¹ := by
      rw [show (clockA ν (ageAt ν t₁ y)) ^ (-2 : ℝ) * movBeta0 P ν (ageAt ν t₁ y) *
          clockN P ν t₁ (ageAt ν t₁ y) * (clockA ν (ageAt ν t₁ y)) ^ 2 =
          movBeta0 P ν (ageAt ν t₁ y) * clockN P ν t₁ (ageAt ν t₁ y) *
            ((clockA ν (ageAt ν t₁ y)) ^ (-2 : ℝ) * (clockA ν (ageAt ν t₁ y)) ^ 2) by ring, hrp]
      field_simp
    refine hC.congr_deriv ?_
    simp only [Function.comp_apply]
    rw [hreal]
    simp only [hαh, hah]
    push_cast
    ring
  have hαcont : ContinuousOn αh (Icc (0 : ℝ) B) := by
    intro y hy
    have hAc := (hasDerivAt_ageAt (hlt y hy)).continuousAt
    have hβc : ContinuousAt (fun σ => ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ)) y :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuous_movBeta0 P ν).continuousAt.comp hAc)
    exact ((hβc.neg).mul (hda y hy).continuousAt).continuousWithinAt
  have hαI : ∀ x ∈ Icc (0 : ℝ) B, IntervalIntegrable αh volume 0 x := by
    intro x hx
    refine (hαcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have ha : ∀ x ∈ Icc (0 : ℝ) B, ah x = ah 0 + ∫ y in (0 : ℝ)..x, αh y := by
    intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ Icc 0 B := by
      rw [uIcc_of_le hx.1]
      exact Icc_subset_Icc le_rfl hx.2
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hda y (hsub hy))
      (hαI x hx)
    rw [this]
    ring
  -- product rule on `[0, T]`
  have hprod : ∀ T ∈ Icc (0 : ℝ) B,
      IntervalIntegrable (fun x => αh x * qh x) volume 0 T ∧
      IntervalIntegrable (fun x => ah x * βh x) volume 0 T ∧
      ah T * qh T - ah 0 * qh 0 = ∫ x in (0 : ℝ)..T, (αh x * qh x + ah x * βh x) := by
    intro T hT
    have hsub : ∀ x ∈ Icc (0 : ℝ) T, x ∈ Icc (0 : ℝ) B := fun x hx => ⟨hx.1, hx.2.trans hT.2⟩
    exact mul_sub_mul_of_primitive hT.1 (hαI T hT) (hq T hT).1 (fun x hx => ha x (hsub x hx))
      (fun x hx => (hq x (hsub x hx)).2)
  have hnA : nAmpl κ P m b K ν hν hF t₁ w j = fun σ => ah σ * qh σ := by
    funext σ
    simp only [nAmpl, hah, hqh, Complex.ofReal_inv]
  have hnD : nAmplDz κ P m b K ν hν hF tr t₁ w j = fun σ => αh σ * qh σ + ah σ * βh σ := by
    funext σ
    simp only [nAmplDz, nAmpl, hαh, hah, hqh, hβh, Complex.ofReal_inv]
    ring
  refine ⟨?_, ?_⟩
  · obtain ⟨i1, i2, -⟩ := hprod B ⟨hB.le, le_rfl⟩
    rw [hnD]
    exact i1.add i2
  · intro σ₀ hσ₀
    obtain ⟨-, -, e⟩ := hprod σ₀ hσ₀
    rw [hnA, hnD]
    simp only
    linear_combination e

namespace AmplMovingRegimeSub

open AmplMovingSub

private theorem exp_phase_mul_clockNC_inv (P : PlanarData) (ν t₁ r : ℝ) (j : Fin 2) :
    Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I) * (clockNC P ν t₁ r j)⁻¹ =
      ((clockN P ν t₁ r : ℝ) : ℂ)⁻¹ := by
  unfold clockNC
  rw [mul_inv]
  have hne : Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I) ≠ 0 :=
    Complex.exp_ne_zero _
  calc Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I) *
        (((clockN P ν t₁ r : ℝ) : ℂ)⁻¹ *
          (Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I))⁻¹)
      = ((clockN P ν t₁ r : ℝ) : ℂ)⁻¹ *
          (Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I) *
            (Complex.exp ((clockPhaseIm P ν t₁ r j : ℂ) * Complex.I))⁻¹) := by ring
    _ = ((clockN P ν t₁ r : ℝ) : ℂ)⁻¹ := by rw [mul_inv_cancel₀ hne, mul_one]

private theorem movBeta0_add_im_eq_modeDiag (P : PlanarData) (ν r : ℝ) (j : Fin 2) :
    ((movBeta0 P ν r : ℝ) : ℂ) +
      ((((modeEigen P j).im + (modeKappa P j).im / clockTheta ν r : ℝ) : ℂ) * Complex.I) =
      modeDiag P ν r j := by
  have hre : (modeEigen P j).re = P.eigenvalue.re ∧ (modeKappa P j).re = P.kappa.re := by
    unfold modeEigen modeKappa
    fin_cases j <;> simp
  have h1 : ((modeEigen P j).re : ℂ) + ((modeEigen P j).im : ℂ) * Complex.I = modeEigen P j :=
    Complex.re_add_im (modeEigen P j)
  have h2 : ((modeKappa P j).re : ℂ) + ((modeKappa P j).im : ℂ) * Complex.I = modeKappa P j :=
    Complex.re_add_im (modeKappa P j)
  unfold movBeta0 modeDiag
  push_cast
  rw [← hre.1, ← hre.2]
  linear_combination h1 + h2 / (clockTheta ν r : ℂ)

private theorem integrableOn_age_amplResidual (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K C₁ C₂ t₁ t₂ : ℝ} (hm : 8 < m) (hν : 0 < ν) (hb : 1 ≤ b)
    (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt : b ≤ clockTheta ν t₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hmR : ∀ i : Fin 2,
      AEMeasurable (fun r => amplResidual κ P (periodizedFrame κ ν m b K hν hF) tr w r i)
        (volume.restrict (Ioc t₁ t₂)))
    (hDecomp : ∀ r ∈ Ioc t₁ t₂, ∀ i : Fin 2,
      let F := periodizedFrame κ ν m b K hν hF
      movH0 κ tr r i (movingW ν w r) =
        (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r))
    (hDir : ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r → ∀ j : Fin 2,
      (∑ i : Fin 2, ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν hF) tr r i j‖) ≤
        C₁ * ν ^ 3 / clockTheta ν r)
    (hCompl : ∀ r ∈ Ioc t₁ t₂,
      let F := periodizedFrame κ ν m b K hν hF
      (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) ≤
        ENNReal.ofReal (C₂ * (1 / clockTheta ν r)) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r))
    (j : Fin 2) :
    let F := periodizedFrame κ ν m b K hν hF
    IntegrableOn
      (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t₁ r j)⁻¹ * amplResidual κ P F tr w r j))
      (Ioc t₁ t₂) := by
  intro F
  set g : Fin 2 → ℝ → ℂ := fun i r =>
    (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
      ((clockNC P ν t₁ r i)⁻¹ * amplResidual κ P F tr w r i)
  have ha_cont : ContinuousOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)) (Ioc t₁ t₂) := by
    have hc1 : ContinuousOn (clockA ν) (Ioc t₁ t₂) := by
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    have hc2 : ContinuousOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Ioc t₁ t₂) :=
      hc1.rpow_const fun r hr => Or.inl (by
        have := one_le_clockA hν.le (ht₁.trans hr.1.le)
        linarith)
    exact Complex.continuous_ofReal.comp_continuousOn hc2
  have hNC_m : AEMeasurable (fun r => (clockNC P ν t₁ r j)⁻¹) (volume.restrict (Ioc t₁ t₂)) :=
    (FrameAmplSub.continuousOn_clockNC_inv P hν ht₁ j).aemeasurable measurableSet_Ioc
  have ha_m : AEMeasurable (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ))
      (volume.restrict (Ioc t₁ t₂)) :=
    ha_cont.aemeasurable measurableSet_Ioc
  have haesm : AEStronglyMeasurable (g j) (volume.restrict (Ioc t₁ t₂)) :=
    (ha_m.mul (hNC_m.mul (hmR j))).aestronglyMeasurable
  -- Uniform norm bounds on `[t₁, t₂]`
  let c := ν ^ (-2 : ℝ)
  have hm0 : 0 ≤ m := by linarith
  have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t₁) :=
    RateBoundAux.contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
  obtain ⟨A_w, hA_w0, hA_w⟩ :=
    RateBoundAux.bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t₁ t₂ ⊆ Ici t₁))
  obtain ⟨M_NC, _, hM_NC0, _, hNC_bd⟩ :=
    CutFTCDual.exists_clockNC_inv_and_modeDiag_bound P (s := t₂) hν ht₁
  have ht₂0 : 0 ≤ t₂ := ht₁.trans h12
  have ha_t₂0 : 0 ≤ (clockA ν t₂) ^ ((3 : ℝ) / 2) :=
    Real.rpow_nonneg (clockA_pos' hν ht₂0).le _
  set M_W : ℝ := (clockA ν t₂) ^ ((3 : ℝ) / 2) * A_w
  have hM_W0 : 0 ≤ M_W := mul_nonneg ha_t₂0 hA_w0
  set K_pos : ℝ := max K 0
  have hK_pos0 : 0 ≤ K_pos := le_max_right K 0
  set M_A : ℝ := 2 * (K_pos * M_W)
  have hM_A0 : 0 ≤ M_A := by unfold M_A; positivity
  set M_C : ℝ := M_W + K_pos * M_A
  have hM_C0 : 0 ≤ M_C := by unfold M_C; positivity
  set δ : ℝ := C₁ * ν ^ 3
  have hδ0 : 0 ≤ δ := by unfold δ; positivity
  set M_tot : ℝ := δ * (M_A * M_NC) + C₂ * (M_C * M_NC)
  have hM_tot0 : 0 ≤ M_tot := by unfold M_tot; positivity
  refine Integrable.mono' (integrableOn_const (C := M_tot) (hs := measure_Ioc_lt_top.ne)) haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hrI : r ∈ Icc t₁ t₂ := ⟨hr.1.le, hr.2⟩
  have hr0 : 0 ≤ r := ht₁.trans hr.1.le
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
  have ha_inv_le : (clockA ν r) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
  have hbr : b ≤ clockTheta ν r := hbt.trans (theta_anti hν hr0 hr.2)
  have hθ1 : 1 ≤ clockTheta ν r := hb.trans hbr
  have hdir_r : ∀ k : Fin 2, (∑ i : Fin 2, ‖amplDirectMat κ P F tr r i k‖) ≤ δ := fun k =>
    (hDir r hr0 hbr k).trans (div_le_self hδ0 hθ1)
  have hcompl_r : (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) ≤
      ENNReal.ofReal C₂ * xNorm (cellLen c (clockA ν r)) m (compl F w r) := by
    refine (hCompl r hr).trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have h1 : 1 / clockTheta ν r ≤ 1 := div_le_self zero_le_one hθ1
    nlinarith
  have hsum := FrameAmplSub.sum_norm_age_amplResidual_le κ P F tr w hν ht₁ hr0 hδ0
    (hDecomp r hr) hdir_r hcompl_r
  -- Bound `movingW`, `amplNorm`, `compl`, and `(clockN P ν t₁ r)⁻¹`
  have hwr : xNorm c m (w r) ≤ ENNReal.ofReal A_w :=
    RateBoundAux.ofReal_toReal_le (hw.memX r hr.1.le).eLpNorm_ne_top hA_w0 (hA_w r hrI)
  have har_le : clockA ν r ≤ clockA ν t₂ := by
    unfold clockA
    nlinarith [hr.2]
  have har_rpow : (clockA ν r) ^ ((3 : ℝ) / 2) ≤ (clockA ν t₂) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (clockA_pos' hν hr0).le har_le (by norm_num)
  have hMW_r : xNorm (cellLen c (clockA ν r)) m (movingW ν w r) ≤ ENNReal.ofReal M_W := by
    have hsc := xNorm_movingW_scale hν.le hr0 hm0 (hw.memX r hr.1.le)
    refine hsc.trans ?_
    rw [ENNReal.ofReal_mul ha_t₂0]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal har_rpow) hwr
  have hk_le : ENNReal.ofReal K ≤ ENNReal.ofReal K_pos :=
    ENNReal.ofReal_le_ofReal (le_max_left K 0)
  have hMA_r : amplNorm F w r ≤ ENNReal.ofReal M_A := by
    refine (amplNorm_le_of F w hr0 hbr (ENNReal.ofReal K_pos) hk_le).trans ?_
    have h1 : 2 * (ENNReal.ofReal K_pos * xNorm (cellLen c (clockA ν r)) m (movingW ν w r)) ≤
        2 * (ENNReal.ofReal K_pos * ENNReal.ofReal M_W) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMW_r zero_le) zero_le
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul hK_pos0,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
  have hMC_r : xNorm (cellLen c (clockA ν r)) m (compl F w r) ≤ ENNReal.ofReal M_C := by
    refine (xNorm_compl_le F w hν.le hr0 hbr (hw.memX r hr.1.le) (ENNReal.ofReal K_pos) hk_le).trans ?_
    refine (add_le_add hMW_r (mul_le_mul_of_nonneg_left hMA_r zero_le)).trans ?_
    rw [← ENNReal.ofReal_mul hK_pos0, ← ENNReal.ofReal_add hM_W0 (mul_nonneg hK_pos0 hM_A0)]
  have hNpos : 0 < clockN P ν t₁ r := AmplMovingSub.clockN_pos P hν ht₁ hr0
  have hNinv_le : (clockN P ν t₁ r)⁻¹ ≤ M_NC := by
    have hnc := (hNC_bd r hrI 0).1
    rwa [FrameAmplSub.norm_clockNC_inv P hν ht₁ hr0 0] at hnc
  have hdivA : amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r) ≤ ENNReal.ofReal (M_A * M_NC) := by
    refine (ENNReal.div_le_div_right hMA_r _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hNpos, div_eq_mul_inv]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hNinv_le hM_A0)
  have hdivC : xNorm (cellLen c (clockA ν r)) m (compl F w r) / ENNReal.ofReal (clockN P ν t₁ r) ≤
      ENNReal.ofReal (M_C * M_NC) := by
    refine (ENNReal.div_le_div_right hMC_r _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hNpos, div_eq_mul_inv]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hNinv_le hM_C0)
  have hmode_le : ENNReal.ofReal ‖g j r‖ ≤ ∑ i : Fin 2, ENNReal.ofReal ‖g i r‖ := by
    fin_cases j <;> simp [Fin.sum_univ_two]
  have htot_le : ENNReal.ofReal ‖g j r‖ ≤ ENNReal.ofReal M_tot := by
    refine hmode_le.trans (hsum.trans ?_)
    have ha_enn : ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ha_inv_le
    have hinner : ENNReal.ofReal δ * (amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) +
        ENNReal.ofReal C₂ *
          (xNorm (cellLen c (clockA ν r)) m (compl F w r) / ENNReal.ofReal (clockN P ν t₁ r)) ≤
        ENNReal.ofReal M_tot := by
      refine (add_le_add (mul_le_mul_of_nonneg_left hdivA zero_le)
        (mul_le_mul_of_nonneg_left hdivC zero_le)).trans ?_
      rw [← ENNReal.ofReal_mul hδ0, ← ENNReal.ofReal_mul hC₂,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (mul_le_mul' ha_enn hinner).trans (by rw [one_mul])
  exact (ENNReal.ofReal_le_ofReal_iff hM_tot0).1 htot_le

theorem amplMovingFTCRegime_proof (κ : PlanarFrameKernels) : Regime.AmplMovingFTCRegime κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, _hb₀, hFTCB⟩ := amplWeakFTC κ hκ P hP m hm K
  obtain ⟨C₁, b₁, hC₁, _hb₁, hDirB⟩ := amplDirectError κ hκ P hP m hm K
  obtain ⟨C₂, b₂, hC₂, _hb₂, hComplB⟩ := amplComplCoupling κ hκ m hm K
  refine ⟨max b₀ (max b₁ b₂), fun b hbb hb => ?_⟩
  have hb₀' : b₀ ≤ b := (le_max_left _ _).trans hbb
  have hb₁' : b₁ ≤ b := ((le_max_left _ _).trans (le_max_right _ _)).trans hbb
  have hb₂' : b₂ ≤ b := ((le_max_right _ _).trans (le_max_right _ _)).trans hbb
  obtain ⟨ν₀, hν₀, H0⟩ := hFTCB b hb₀'
  obtain ⟨ν₁, hν₁, H1⟩ := hDirB b hb₁'
  obtain ⟨ν₂, hν₂, H2⟩ := hComplB b hb₂'
  refine ⟨min ν₀ (min ν₁ ν₂), lt_min hν₀ (lt_min hν₁ hν₂), ?_⟩
  intro ν hν hνs hF tr htr t₁ t₂ ht₁ h12 hbt hBe f w u hFlow hCirc j
  have hν_0 : ν ∈ Ioc 0 ν₀ := ⟨hν, hνs.trans (min_le_left _ _)⟩
  have hν_1 : ν ∈ Ioc 0 ν₁ := ⟨hν, hνs.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν_2 : ν ∈ Ioc 0 ν₂ := ⟨hν, hνs.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  set F := periodizedFrame κ ν m b K hν hF
  obtain ⟨hmR, _, hDecomp⟩ := H0 ν hν_0 hF tr htr t₁ t₂ ht₁ h12 hbt f w u hFlow hCirc
  have hgI := integrableOn_age_amplResidual κ P hm hν hb ht₁ h12 hbt hC₁ hC₂ hF hFlow hmR hDecomp
    (H1 ν hν_1 hF tr htr) (H2 ν hν_2 hF tr htr t₁ t₂ ht₁ h12 hbt f w u hFlow hCirc) j
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hage : ∀ x ∈ Icc (0 : ℝ) B, ageAt ν t₁ x ∈ Icc t₁ t₂ :=
    fun x hx => ageAt_mem_Icc hν ht₁ h12 hBe hx
  have hage0 : ∀ x ∈ Icc (0 : ℝ) B, 0 ≤ ageAt ν t₁ x := fun x hx => ht₁.trans (hage x hx).1
  have hlt : ∀ x ∈ Icc (0 : ℝ) B, ν * (movingZ ν t₁ + x) < 1 :=
    fun x hx => nu_mul_movingZ_add_lt_one hν ht₂ hBe hx.2
  set βh : ℝ → ℂ := fun σ =>
    (clockNC P ν t₁ (ageAt ν t₁ σ) j)⁻¹ * amplResidual κ P F tr w (ageAt ν t₁ σ) j with hβh
  set qh : ℝ → ℂ := fun σ => normAmpl F P t₁ w (ageAt ν t₁ σ) j with hqh
  set ah : ℝ → ℂ := fun σ =>
    Complex.exp ((clockPhaseIm P ν t₁ (ageAt ν t₁ σ) j : ℂ) * Complex.I) with hah
  set ωh : ℝ → ℝ := fun σ =>
    (modeEigen P j).im + (modeKappa P j).im / clockTheta ν (ageAt ν t₁ σ) with hωh
  set αh : ℝ → ℂ := fun σ => ((ωh σ : ℝ) : ℂ) * Complex.I * ah σ with hαh
  -- primitive of `qh`
  have hq : ∀ x ∈ Icc (0 : ℝ) B,
      IntervalIntegrable βh volume 0 x ∧ qh x = qh 0 + ∫ y in (0 : ℝ)..x, βh y := by
    intro x hx
    obtain ⟨hI, hE⟩ := cov hν ht₁ h12 hBe hx
      (fun r => (clockNC P ν t₁ r j)⁻¹ * amplResidual κ P F tr w r j)
      (hgI.mono_set (Ioc_subset_Ioc le_rfl (hage x hx).2))
    have hbs_x : b ≤ clockTheta ν (ageAt ν t₁ x) :=
      hbt.trans (theta_anti hν (hage0 x hx) (hage x hx).2)
    have hFTC_x :=
      (H0 ν hν_0 hF tr htr t₁ (ageAt ν t₁ x) ht₁ (hage x hx).1 hbs_x f w u hFlow hCirc).2.1 j
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2 hI, ?_⟩
    rw [intervalIntegral.integral_of_le hx.1, hE, ← hFTC_x]
    simp only [hqh, ageAt_zero hν ht₁]
    ring
  -- derivative of `ah`
  have hda : ∀ y ∈ Icc (0 : ℝ) B, HasDerivAt ah (αh y) y := by
    intro y hy
    have hs := hage0 y hy
    have hA := hasDerivAt_ageAt (hlt y hy)
    have hPh := (FrameAmplSub.hasDerivAt_clockPhaseIm P hν ht₁ hs j).comp y hA
    have ha := clockA_pos' hν hs
    have hrp : (clockA ν (ageAt ν t₁ y)) ^ (-2 : ℝ) * (clockA ν (ageAt ν t₁ y)) ^ 2 = 1 := by
      rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (by positivity)]
    have hPh' : HasDerivAt (fun σ => clockPhaseIm P ν t₁ (ageAt ν t₁ σ) j) (ωh y) y := by
      refine hPh.congr_deriv ?_
      simp only [hωh]
      linear_combination ωh y * hrp
    have hdCx : HasDerivAt
        (fun σ => (clockPhaseIm P ν t₁ (ageAt ν t₁ σ) j : ℂ) * Complex.I)
        (((ωh y : ℝ) : ℂ) * Complex.I) y :=
      hPh'.ofReal_comp.mul_const Complex.I
    refine hdCx.cexp.congr_deriv ?_
    simp only [hαh, hah]
    ring
  have hαcont : ContinuousOn αh (Icc (0 : ℝ) B) := by
    intro y hy
    have hs := hage0 y hy
    have hAc := (hasDerivAt_ageAt (hlt y hy)).continuousAt
    have hθ_pos : 0 < clockTheta ν (ageAt ν t₁ y) := theta_pos hν hs
    have hθc : ContinuousAt (clockTheta ν) (ageAt ν t₁ y) := by
      have hνa : Continuous (fun r => ν * clockA ν r) := by unfold clockA; fun_prop
      have hne : ν * clockA ν (ageAt ν t₁ y) ≠ 0 :=
        (mul_pos hν (clockA_pos' hν hs)).ne'
      exact hνa.continuousAt.inv₀ hne
    have hωc : ContinuousAt ωh y := by
      simp only [hωh]
      exact continuousAt_const.add
        (continuousAt_const.div (hθc.comp hAc) hθ_pos.ne')
    have hωCx : ContinuousAt (fun σ => ((ωh σ : ℝ) : ℂ) * Complex.I) y :=
      (Complex.continuous_ofReal.continuousAt.comp hωc).mul continuousAt_const
    exact (hωCx.mul (hda y hy).continuousAt).continuousWithinAt
  have hαI : ∀ x ∈ Icc (0 : ℝ) B, IntervalIntegrable αh volume 0 x := by
    intro x hx
    refine (hαcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have ha : ∀ x ∈ Icc (0 : ℝ) B, ah x = ah 0 + ∫ y in (0 : ℝ)..x, αh y := by
    intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ Icc 0 B := by
      rw [uIcc_of_le hx.1]
      exact Icc_subset_Icc le_rfl hx.2
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hda y (hsub hy))
      (hαI x hx)
    rw [this]
    ring
  -- product rule on `[0, T]`
  have hprod : ∀ T ∈ Icc (0 : ℝ) B,
      IntervalIntegrable (fun x => αh x * qh x) volume 0 T ∧
      IntervalIntegrable (fun x => ah x * βh x) volume 0 T ∧
      ah T * qh T - ah 0 * qh 0 = ∫ x in (0 : ℝ)..T, (αh x * qh x + ah x * βh x) := by
    intro T hT
    have hsub : ∀ x ∈ Icc (0 : ℝ) T, x ∈ Icc (0 : ℝ) B := fun x hx => ⟨hx.1, hx.2.trans hT.2⟩
    exact mul_sub_mul_of_primitive hT.1 (hαI T hT) (hq T hT).1 (fun x hx => ha x (hsub x hx))
      (fun x hx => (hq x (hsub x hx)).2)
  have hnA : nAmpl κ P m b K ν hν hF t₁ w j = fun σ => ah σ * qh σ := by
    funext σ
    simp only [nAmpl, hah, hqh, normAmpl]
    rw [← mul_assoc, exp_phase_mul_clockNC_inv]
  have hnD : nAmplDz κ P m b K ν hν hF tr t₁ w j = fun σ => αh σ * qh σ + ah σ * βh σ := by
    funext σ
    have h1 : αh σ * qh σ =
        (((ωh σ : ℝ) : ℂ) * Complex.I) * nAmpl κ P m b K ν hν hF t₁ w j σ := by
      rw [congr_fun hnA σ]
      simp only [hαh]
      ring
    have h2 : ah σ * βh σ =
        ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
          amplResidual κ P F tr w (ageAt ν t₁ σ) j := by
      simp only [hah, hβh]
      rw [← mul_assoc, exp_phase_mul_clockNC_inv]
    have hdiag :
        ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ) + (((ωh σ : ℝ) : ℂ) * Complex.I) =
          modeDiag P ν (ageAt ν t₁ σ) j := by
      simpa only [hωh] using movBeta0_add_im_eq_modeDiag P ν (ageAt ν t₁ σ) j
    rw [h1, h2]
    unfold nAmplDz nAmpl amplResidual
    rw [← hdiag]
    ring
  refine ⟨?_, ?_⟩
  · obtain ⟨i1, i2, -⟩ := hprod B ⟨hB.le, le_rfl⟩
    rw [hnD]
    exact i1.add i2
  · intro σ₀ hσ₀
    obtain ⟨-, -, e⟩ := hprod σ₀ hσ₀
    rw [hnA, hnD]
    simp only
    linear_combination e

end AmplMovingRegimeSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa

theorem amplMovingFTCRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.AmplMovingFTCRegime κ :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.AmplMovingRegimeSub.amplMovingFTCRegime_proof κ
