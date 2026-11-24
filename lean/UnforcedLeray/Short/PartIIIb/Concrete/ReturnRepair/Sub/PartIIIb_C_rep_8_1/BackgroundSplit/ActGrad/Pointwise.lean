import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Source
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.SepDomFacts

/-!
# `ActGrad` helpers: pointwise majorants at meridional receivers (source 4161-4200, 5203-5217)

Source `the November 2 reference manuscript` 3604-3623 (pointwise domination of
the separated jets), 4178-4192 (the stream cutoff and its outward primitive), 5203-5217
(`repair:phase-gradient`), 5267-5268 (`D²X` has an additional curvature power).

At a meridional receiver `meridPt z = (ϱ z, 0, z₃)`:
* `ag_sepDom_merid`: the separated majorant `sepDom` of an axisymmetric source is rotation
  invariant, so it takes the same value at `meridPt z` and at `z`;
* `ag_x0_jet`, `ag_wre_jet`: `|D^j X₀|`, `|D^j Re W_μ| ≤ C sepDom(2μ+2, j)` (`j ≤ 2`);
* `ag_psi`: the outward primitives on the transition annulus are bounded by the vertical
  reduction `vertRed`;
* `ag_hess`: the Hessian of the stream cutoff `𝒞_y Z` by the jets of `Z` and `Ψ_Z`
  (`streamCutHess` on the annulus; `𝒞_y Z = 0` inside, `= Z` outside).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Rotation invariance of the separated majorant -/

theorem ag_sepDom_anti {a b : ℝ} (hab : a ≤ b) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞)
    (τ : ℝ) (y : Space) : IIIa.sepDom b j D g τ y ≤ IIIa.sepDom a j D g τ y := by
  unfold IIIa.sepDom
  refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hl.1 hl.2.le hab)) le_rfl

theorem ag_srcNorm_rot {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hAx : IsAxiSource S)
    (co si : ℝ) (hco : co ^ 2 + si ^ 2 = 1) (τ : ℝ) (z : Space) :
    IIIa.srcNorm S τ (actM (rotM co si) z) = IIIa.srcNorm S τ z := by
  unfold IIIa.srcNorm
  rw [hAx.1 co si hco τ z, sd_tensorNorm_conj _ _ (rotM_orth hco)]

theorem ag_meridPt_two (z : Space) : meridPt z 2 = z 2 := by simp [meridPt]

theorem ag_meridPt_rho (z : Space) : ϱ (meridPt z) = ϱ z := by
  have h0 : (meridPt z) 0 = ϱ z := rfl
  have h1 : (meridPt z) 1 = 0 := rfl
  show √((meridPt z) 0 ^ 2 + (meridPt z) 1 ^ 2) = ϱ z
  rw [h0, h1, zero_pow two_ne_zero, add_zero, sq]
  exact Real.sqrt_mul_self (Real.sqrt_nonneg _)

theorem ag_sepDom_merid {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hAx : IsAxiSource S)
    (a : ℝ) (j : ℕ) (D τ : ℝ) (z : Space) :
    IIIa.sepDom a j D (IIIa.srcNorm S) τ (meridPt z) = IIIa.sepDom a j D (IIIa.srcNorm S) τ z := by
  have h0 : (meridPt z) 0 = ϱ z := rfl
  have h1 : (meridPt z) 1 = 0 := rfl
  have h2 : z 2 = (meridPt z) 2 := (ag_meridPt_two z).symm
  have hsq : z 0 ^ 2 + z 1 ^ 2 = (meridPt z) 0 ^ 2 + (meridPt z) 1 ^ 2 := by
    rw [h0, h1]
    show z 0 ^ 2 + z 1 ^ 2 = (√(z 0 ^ 2 + z 1 ^ 2)) ^ 2 + 0 ^ 2
    rw [Real.sq_sqrt (by positivity)]
    ring
  obtain ⟨co, si, hco, hrot⟩ := sd_exists_rot (meridPt z) z h2 hsq
  have := sd_sepDom_rot a j D (IIIa.srcNorm S) co si hco
    (fun τ z => ag_srcNorm_rot hAx co si hco τ z) τ (meridPt z)
  rw [hrot] at this
  exact this.symm

/-! ## 2. Jets of `X₀` and `Re W_μ` -/

theorem ag_x0_jet (j : ℕ) (hj : j ≤ 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ rOut rIn P : ℝ), 0 < ν →
    -(1 / 4) < μ → 0 ≤ rOut → rOut < rIn → 0 < P →
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ →
        ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ ≤
          ENNReal.ofReal C * IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, hA⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  refine ⟨‖reL‖ * (2 * C0), by positivity, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP T hT hS τ y hy hfin
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hyU : y ∈ {y : Space | rOut < ϱ y} := lt_of_lt_of_le hrr hy
  have hm1re : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2re : -(1 / 4) < ((μ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hW1 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1re hrO hP hT hS τ i)
  have hW2 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T
      hν hm2re hrO hP hT hS τ i)
  have key := iteratedFDeriv_reL_le hU hW1 hW2 hj hyU
  have hy' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hy
  have e1 : (2 * ((μ : ℂ)).re + 2) = 2 * μ + 2 := by simp
  have e2 : (2 * ((μ : ℂ) + 1).re + 2) = 2 * μ + 4 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; ring
  have hfin1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ := by
    rw [e1]; exact hfin
  have hfin2 : IIIa.sepDom (2 * ((μ : ℂ) + 1).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ := by
    rw [e2]; exact lt_of_le_of_lt (ag_sepDom_anti (by linarith) 0 _ _ τ y) hfin
  have d1 := hA ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hy' hfin1
  have d2 := hA ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hy' hfin2
  rw [e1] at d1
  rw [e2] at d2
  have d2' := d2.trans (mul_le_mul' le_rfl
    (ag_sepDom_anti (by linarith : 2 * μ + 2 ≤ 2 * μ + 4) j (rIn - rOut) (IIIa.srcNorm T) τ y))
  unfold IIIa.wDerivNorm at d1 d2'
  rw [sepX0_eq_reL]
  calc ‖iteratedFDeriv ℝ j (fun z => reL (IIIa.sepW ν (μ : ℂ) T z τ -
        IIIa.sepW ν ((μ : ℂ) + 1) T z τ)) y‖ₑ
      ≤ ENNReal.ofReal ‖reL‖ * (‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y‖ₑ +
          ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ) y‖ₑ) := key
    _ ≤ ENNReal.ofReal ‖reL‖ *
          (ENNReal.ofReal C0 * IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y +
            ENNReal.ofReal C0 * IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y) := by
        gcongr
    _ = ENNReal.ofReal (‖reL‖ * (2 * C0)) *
          IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
        ring

theorem ag_wre_jet (j : ℕ) (hj : j ≤ 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ rOut rIn P : ℝ), 0 < ν →
    -(1 / 4) < μ → 0 ≤ rOut → rOut < rIn → 0 < P →
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ →
        ‖iteratedFDeriv ℝ j (sepWre ν μ T τ) y‖ₑ ≤
          ENNReal.ofReal C * IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, hA⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  refine ⟨‖reL‖ * C0, by positivity, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP T hT hS τ y hy hfin
  have hm1re : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hy' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hy
  have e1 : (2 * ((μ : ℂ)).re + 2) = 2 * μ + 2 := by simp
  have hfin1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ := by
    rw [e1]; exact hfin
  have d1 := hA ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hy' hfin1
  rw [e1] at d1
  unfold IIIa.wDerivNorm at d1
  calc ‖iteratedFDeriv ℝ j (sepWre ν μ T τ) y‖ₑ
      ≤ ENNReal.ofReal ‖reL‖ * ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) T z τ) y‖ₑ :=
        wgy_jet_le hν hμ hrO hP hT hS τ hj (lt_of_lt_of_le hrr hy)
    _ ≤ ENNReal.ofReal ‖reL‖ *
          (ENNReal.ofReal C0 * IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y) := by
        gcongr
    _ = ENNReal.ofReal (‖reL‖ * C0) *
          IIIa.sepDom (2 * μ + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]

/-! ## 3. The outward primitives on the annulus -/

theorem ag_srcNorm_supp {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) (z : Space) (hz : rOut < ϱ z) :
    IIIa.srcNorm T τ z = 0 := by
  unfold IIIa.srcNorm
  rw [hT.support τ z hz]
  simp [IIIa.tensorNorm]

theorem ag_psi (σ₁ σ₂ : ℝ) (hσ : -(1 / 4) < σ₁) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ R P : ℝ), 0 < ν →
    0 < R → 0 < P → μ ∈ Icc σ₁ σ₂ →
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → ∀ (τ : ℝ) (y : Space),
        wgxPsi ν μ R T τ y ≤ ENNReal.ofReal C * (streamAnn ν R).indicator (fun y =>
          vertRed (2 * μ + 2) (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
            (IIIa.srcNorm T) τ (y 2)) y ∧
        wgyWPsi ν μ R T τ y ≤ ENNReal.ofReal C * (streamAnn ν R).indicator (fun y =>
          vertRed (2 * μ + 2) (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
            (IIIa.srcNorm T) τ (y 2)) y := by
  obtain ⟨C0, hC0, hP⟩ := outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds σ₁ σ₂ hσ
  refine ⟨2 * C0, by positivity, ?_⟩
  intro ν μ R P hν hR hP0 hμ T hT τ y
  have hrO : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm T)) := IIIa.sepAE_measurable_srcNorm hT
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → IIIa.srcNorm T τ z = 0 :=
    fun τ z hz => ag_srcNorm_supp hT τ z hz
  by_cases hy : y ∈ streamAnn ν R
  · have hr : R * Real.sqrt ν ≤ ϱ y := hy.1
    have hb := hP ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO hrr hP0 T hT τ
      (ϱ y) (y 2) hr
    have hred := outMajReduce (2 * μ + 2) (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) hrO hrr
      (IIIa.srcNorm T) hgm hsupp τ (ϱ y) (y 2) hr
    unfold wgxPsi wgyWPsi
    rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy]
    constructor
    · calc ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal C0 * (2 * outMaj (2 * μ + 2) (R * Real.sqrt ν -
              R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (ϱ y) (y 2)) := hb.2
        _ ≤ ENNReal.ofReal C0 * (2 * vertRed (2 * μ + 2) (R * Real.sqrt ν)
              (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (y 2)) := by
            gcongr
        _ = ENNReal.ofReal (2 * C0) * vertRed (2 * μ + 2) (R * Real.sqrt ν)
              (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (y 2) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
            ring
    · calc ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal C0 * outMaj (2 * μ + 2) (R * Real.sqrt ν -
              R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (ϱ y) (y 2) := hb.1
        _ ≤ ENNReal.ofReal C0 * vertRed (2 * μ + 2) (R * Real.sqrt ν)
              (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (y 2) := by
            gcongr
        _ ≤ ENNReal.ofReal (2 * C0) * vertRed (2 * μ + 2) (R * Real.sqrt ν)
              (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ (y 2) := by
            gcongr
            linarith
  · unfold wgxPsi wgyWPsi
    simp only [Set.indicator_of_notMem hy, mul_zero, le_refl, and_self]

/-! ## 4. The Hessian of the stream cutoff -/

theorem ag_hessSize_congr {f g : Space → Space} {y : Space} (h : f =ᶠ[𝓝 y] g) :
    hessSize f y = hessSize g y := by
  have h1 : ∀ l : Fin 3, (fun y' => fderiv ℝ f y' (coordinateVector l)) =ᶠ[𝓝 y]
      (fun y' => fderiv ℝ g y' (coordinateVector l)) := by
    intro l
    filter_upwards [h.eventuallyEq_nhds] with y' hy'
    rw [hy'.fderiv_eq]
  unfold hessSize
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  show ‖fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) y (coordinateVector j)‖ =
    ‖fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector l)) y (coordinateVector j)‖
  rw [(h1 l).fderiv_eq]

theorem ag_hessSize_zero (y : Space) : hessSize (fun _ : Space => (0 : Space)) y = 0 := by
  simp [hessSize, physPd2, physPd]

theorem ag_cut_zero {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy0 : 0 < ϱ y) (hy : ϱ y < R * Real.sqrt ν) :
    wardStreamCut ν R χ Z τ =ᶠ[𝓝 y] fun _ => 0 := by
  have hU : IsOpen {y' : Space | 0 < ϱ y' ∧ ϱ y' < R * Real.sqrt ν} :=
    (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_ϱ continuous_const)
  filter_upwards [hU.mem_nhds ⟨hy0, hy⟩] with y' hy'
  obtain ⟨h0, h1⟩ := hy'
  have hsq : ϱ y' ^ 2 < R ^ 2 * ν := by
    have : ϱ y' ^ 2 < (R * Real.sqrt ν) ^ 2 := by
      exact pow_lt_pow_left₀ h1 h0.le two_ne_zero
    rwa [mul_pow, Real.sq_sqrt hν.le] at this
  have ht : 1 < ν * age R y' := by
    unfold age
    rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
    linarith
  have hχ0 : χ (ν * age R y') = 0 := hχ.zero _ ht.le
  have hd : deriv χ (ν * age R y') = 0 := by
    have hev : χ =ᶠ[𝓝 (ν * age R y')] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with t ht'
      exact hχ.zero t (le_of_lt ht')
    rw [hev.deriv_eq]
    simp
  simp only [wardStreamCut, hχ0, hd, zero_smul, zero_mul, zero_div, zero_add]

theorem ag_cut_id {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 4) < ϱ y) :
    wardStreamCut ν R χ Z τ =ᶠ[𝓝 y] Z τ := by
  have hU : IsOpen {y' : Space | R * Real.sqrt (5 * ν / 4) < ϱ y'} :=
    isOpen_lt continuous_const continuous_ϱ
  filter_upwards [hU.mem_nhds hy] with y' hy'
  have hy'' : R * Real.sqrt (5 * ν / 4) < ϱ y' := hy'
  have h0 : 0 < ϱ y' := lt_of_le_of_lt (by positivity) hy''
  have hsq : R ^ 2 * (5 * ν / 4) < ϱ y' ^ 2 := by
    have : (R * Real.sqrt (5 * ν / 4)) ^ 2 < ϱ y' ^ 2 :=
      pow_lt_pow_left₀ hy'' (by positivity) two_ne_zero
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at this
  have ht : ν * age R y' < 4 / 5 := by
    unfold age
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hχ1 : χ (ν * age R y') = 1 := hχ.one _ ht.le
  have hd : deriv χ (ν * age R y') = 0 := by
    have hev : χ =ᶠ[𝓝 (ν * age R y')] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with t ht'
      exact hχ.one t (le_of_lt ht')
    rw [hev.deriv_eq]
    simp
  simp only [wardStreamCut, hχ1, hd, one_smul, zero_mul, zero_div, zero_smul, add_zero]

theorem ag_meridPt_hpt (z : Space) : meridPt z = GeomXAsm.hpt (ϱ z) (z 2) := rfl

/-- **The Hessian of the stream cutoff at a meridional receiver** (source 4178-4186, 5267-5268). -/
theorem ag_hess (χ : ℝ → ℝ) (hχ : IsStreamCutoff χ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ), 0 < ν → 0 < R →
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) →
    (∀ r' z', R * Real.sqrt (5 * ν / 6) < r' →
      HasDerivAt (fun r'' => outPrim Z τ r'' z') (r' * Z τ !₂[r', 0, z'] 2) r' ∧
        HasDerivAt (fun z'' => outPrim Z τ r' z'') (-(r' * Z τ !₂[r', 0, z'] 0)) z') →
    ∀ z : Space, 0 < ϱ z →
      ENNReal.ofReal (hessSize (wardStreamCut ν R χ Z τ) (meridPt z)) ≤
        ENNReal.ofReal C *
          ((if R * Real.sqrt ν ≤ ϱ z then ‖iteratedFDeriv ℝ 2 (Z τ) (meridPt z)‖ₑ else 0) +
            ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
              (if R * Real.sqrt ν ≤ ϱ z then ‖iteratedFDeriv ℝ 1 (Z τ) (meridPt z)‖ₑ else 0) +
            ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 2) *
              (if R * Real.sqrt ν ≤ ϱ z then ‖iteratedFDeriv ℝ 0 (Z τ) (meridPt z)‖ₑ else 0) +
            ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 4) *
              (streamAnn ν R).indicator (fun y => ENNReal.ofReal |outPrim Z τ (ϱ y) (y 2)|) z) := by
  obtain ⟨C₀, hC₀, hH⟩ := streamCutHess χ hχ
  refine ⟨9 * (C₀ + 1), by positivity, ?_⟩
  intro ν R Z τ hν hR hZ hdr z hz0
  set Lr : ℝ := R * Real.sqrt ν with hLr
  have hLr0 : 0 < Lr := by rw [hLr]; positivity
  set y := meridPt z with hy
  have hyr : ϱ y = ϱ z := ag_meridPt_rho z
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hrO : R * Real.sqrt (5 * ν / 6) < Lr :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  -- the jets of `Z` at `y`, for `Lr ≤ ϱ z`
  set A2 : ℝ := ‖iteratedFDeriv ℝ 2 (Z τ) y‖ with hA2
  set A1 : ℝ := ‖iteratedFDeriv ℝ 1 (Z τ) y‖ with hA1
  set A0 : ℝ := ‖iteratedFDeriv ℝ 0 (Z τ) y‖ with hA0
  have hA2n : 0 ≤ A2 := norm_nonneg _
  have hA1n : 0 ≤ A1 := norm_nonneg _
  have hA0n : 0 ≤ A0 := norm_nonneg _
  have hRHS0 : 0 ≤ ENNReal.ofReal (9 * (C₀ + 1)) *
      ((if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 2 (Z τ) y‖ₑ else 0) +
        ENNReal.ofReal Lr⁻¹ * (if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 1 (Z τ) y‖ₑ else 0) +
        ENNReal.ofReal (Lr⁻¹ ^ 2) * (if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 0 (Z τ) y‖ₑ else 0) +
        ENNReal.ofReal (Lr⁻¹ ^ 4) *
          (streamAnn ν R).indicator (fun y => ENNReal.ofReal |outPrim Z τ (ϱ y) (y 2)|) z) :=
    zero_le
  by_cases hin : ϱ z < Lr
  · -- inside the stream cutoff: `𝒞_y Z = 0` near `y`
    have hev := ag_cut_zero hν hR hχ Z τ (y := y) (by rw [hyr]; exact hz0) (by rw [hyr]; exact hin)
    rw [ag_hessSize_congr hev, ag_hessSize_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hLz : Lr ≤ ϱ z := not_lt.1 hin
  have hyU : y ∈ youngOpen ν R := by
    show R * Real.sqrt (5 * ν / 6) < ϱ y
    rw [hyr]; exact lt_of_lt_of_le hrO hLz
  have hHZ : hessSize (Z τ) y ≤ 9 * A2 := ZActJetAux.hessSize_le_iteratedFDeriv hU hZ hyU
  have e2 : (if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 2 (Z τ) y‖ₑ else 0) = ENNReal.ofReal A2 := by
    rw [if_pos hLz, hA2, ofReal_norm]
  have e1 : (if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 1 (Z τ) y‖ₑ else 0) = ENNReal.ofReal A1 := by
    rw [if_pos hLz, hA1, ofReal_norm]
  have e0 : (if Lr ≤ ϱ z then ‖iteratedFDeriv ℝ 0 (Z τ) y‖ₑ else 0) = ENNReal.ofReal A0 := by
    rw [if_pos hLz, hA0, ofReal_norm]
  rw [e2, e1, e0]
  have hLi : 0 ≤ Lr⁻¹ := inv_nonneg.2 hLr0.le
  by_cases hout : R * Real.sqrt (5 * ν / 4) < ϱ z
  · -- outside the annulus: `𝒞_y Z = Z` near `y`
    have hev := ag_cut_id hν hR hχ Z τ (y := y) (by rw [hyr]; exact hout)
    rw [ag_hessSize_congr hev]
    calc ENNReal.ofReal (hessSize (Z τ) y) ≤ ENNReal.ofReal (9 * (C₀ + 1) * A2) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith
      _ = ENNReal.ofReal (9 * (C₀ + 1)) * ENNReal.ofReal A2 := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by
          gcongr
          calc ENNReal.ofReal A2 ≤ ENNReal.ofReal A2 + ENNReal.ofReal Lr⁻¹ * ENNReal.ofReal A1 :=
                le_self_add
            _ ≤ ENNReal.ofReal A2 + ENNReal.ofReal Lr⁻¹ * ENNReal.ofReal A1 +
                ENNReal.ofReal (Lr⁻¹ ^ 2) * ENNReal.ofReal A0 := le_self_add
            _ ≤ _ := le_self_add
  -- on the annulus: `streamCutHess`
  have hann : z ∈ streamAnn ν R := ⟨hLz, not_lt.1 hout⟩
  rw [indicator_of_mem hann]
  have hr0 : 0 < ϱ z := hz0
  have hyoung : ν * (R ^ 2 / ϱ z ^ 2) ≤ 1 := by
    have hsq : (R * Real.sqrt ν) ^ 2 ≤ ϱ z ^ 2 := pow_le_pow_left₀ hLr0.le hLz 2
    rw [mul_pow, Real.sq_sqrt hν.le] at hsq
    rw [mul_div_assoc', div_le_one (by positivity)]
    linarith
  have hS := hH ν R Z τ (ϱ z) (z 2) hν hR hr0 hyoung hZ hdr
  rw [← ag_meridPt_hpt] at hS
  have hG : gradSize (Z τ) y ≤ 3 * A1 := ZActJetAux.gradSize_le_iteratedFDeriv (Z τ) y
  have hZ0 : ‖Z τ y‖ = A0 := by rw [hA0, norm_iteratedFDeriv_zero]
  set Ψ : ℝ := |outPrim Z τ (ϱ z) (z 2)| with hΨ
  have hΨn : 0 ≤ Ψ := abs_nonneg _
  have hri : (ϱ z)⁻¹ ≤ Lr⁻¹ := inv_anti₀ hLr0 hLz
  have hri0 : 0 ≤ (ϱ z)⁻¹ := inv_nonneg.2 hr0.le
  have hreal : hessSize (wardStreamCut ν R χ Z τ) y ≤
      9 * (C₀ + 1) * (A2 + Lr⁻¹ * A1 + Lr⁻¹ ^ 2 * A0 + Lr⁻¹ ^ 4 * Ψ) := by
    refine hS.trans ?_
    have hgs : 0 ≤ gradSize (Z τ) y := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    have i1 : (ϱ z)⁻¹ * gradSize (Z τ) y ≤ 3 * (Lr⁻¹ * A1) := by
      have := mul_le_mul hri hG hgs hLi
      linarith
    have i2 : (ϱ z)⁻¹ ^ 2 * ‖Z τ y‖ ≤ Lr⁻¹ ^ 2 * A0 := by
      rw [hZ0]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hri0 hri 2) hA0n
    have i3 : (ϱ z)⁻¹ ^ 4 * Ψ ≤ Lr⁻¹ ^ 4 * Ψ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hri0 hri 4) hΨn
    have hsum : hessSize (Z τ) y + (ϱ z)⁻¹ * gradSize (Z τ) y + (ϱ z)⁻¹ ^ 2 * ‖Z τ y‖ +
        (ϱ z)⁻¹ ^ 4 * Ψ ≤ 9 * (A2 + Lr⁻¹ * A1 + Lr⁻¹ ^ 2 * A0 + Lr⁻¹ ^ 4 * Ψ) := by
      have n1 := mul_nonneg hLi hA1n
      have n2 := mul_nonneg (pow_nonneg hLi 2) hA0n
      have n3 := mul_nonneg (pow_nonneg hLi 4) hΨn
      linarith
    have hs0 : 0 ≤ hessSize (Z τ) y + (ϱ z)⁻¹ * gradSize (Z τ) y + (ϱ z)⁻¹ ^ 2 * ‖Z τ y‖ +
        (ϱ z)⁻¹ ^ 4 * Ψ := by
      have h1 : 0 ≤ hessSize (Z τ) y :=
        Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _))
      have h2 := mul_nonneg hri0 hgs
      have h3 := mul_nonneg (pow_nonneg hri0 2) (norm_nonneg (Z τ y))
      have h4 := mul_nonneg (pow_nonneg hri0 4) hΨn
      linarith
    calc C₀ * (hessSize (Z τ) y + (ϱ z)⁻¹ * gradSize (Z τ) y + (ϱ z)⁻¹ ^ 2 * ‖Z τ y‖ +
          (ϱ z)⁻¹ ^ 4 * Ψ)
        ≤ (C₀ + 1) * (9 * (A2 + Lr⁻¹ * A1 + Lr⁻¹ ^ 2 * A0 + Lr⁻¹ ^ 4 * Ψ)) :=
          mul_le_mul (by linarith) hsum hs0 (by positivity)
      _ = 9 * (C₀ + 1) * (A2 + Lr⁻¹ * A1 + Lr⁻¹ ^ 2 * A0 + Lr⁻¹ ^ 4 * Ψ) := by ring
  calc ENNReal.ofReal (hessSize (wardStreamCut ν R χ Z τ) y)
      ≤ ENNReal.ofReal (9 * (C₀ + 1) * (A2 + Lr⁻¹ * A1 + Lr⁻¹ ^ 2 * A0 + Lr⁻¹ ^ 4 * Ψ)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (9 * (C₀ + 1)) * (ENNReal.ofReal A2 + ENNReal.ofReal Lr⁻¹ *
          ENNReal.ofReal A1 + ENNReal.ofReal (Lr⁻¹ ^ 2) * ENNReal.ofReal A0 +
          ENNReal.ofReal (Lr⁻¹ ^ 4) * ENNReal.ofReal Ψ) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 * (C₀ + 1))]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hLi, ENNReal.ofReal_mul (pow_nonneg hLi 2),
          ENNReal.ofReal_mul (pow_nonneg hLi 4)]
    _ = _ := by rw [hΨ]

end UnforcedLeray.Short.PartIIIb.Concrete

end
