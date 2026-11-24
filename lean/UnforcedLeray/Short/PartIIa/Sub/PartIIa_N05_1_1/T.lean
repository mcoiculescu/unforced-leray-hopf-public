import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Weak
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftRecovery
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Bridge.Dict
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Basic

/-!
# `Sub/PartII-a_N05_1_1/T`: Generator transport (`PartII-a:N05/1/2`)

Source: `the November 2 reference manuscript`,
lines 1647–1654 and 1789–1791 (`near:local-smoothing`: "for a body source the graph controls `S b`").

Under the isometric phase lift `U ∘ B0223.liftVec : HSpace c MeridC → Yq P 2` (`P = 2 * ε * c`),
`U (liftVec w)` has pointwise representative `IIb.NvC ε⁻¹ b₀` where
`b₀ = (√(c / π) * ε) • periodize c w ∈ IIb.InHr c 2`. Applying `driftRecovery_proof` at `r = 2`
to `v ∈ D P ν 2` and `T0D v ∈ Yq P 2` yields a profile `Sb ∈ IIb.InHr c 2` with
`IIb.HasWeakVec IIb.vS IIb.dZero b₀ Sb` and `(π ε⁻²)^{1/2} ‖Sb‖_{H_2} ≤ ‖T0D v‖ + ‖v‖`.
Passing to a measurable everywhere-`c`-periodic representative (`IIb.periodicRepresentative`),
rescaling by `(√(c / π) * ε)⁻¹`, and unfolding against `qCut c` (`FBCLL.integral_qCut_mul`) gives
`Sw : HSpace c MeridC` satisfying `WeakS c w Sw` and `‖Sw‖ ≤ 1 * (‖(v : Yq P 2)‖ + ‖T0D v‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1T

/-! ### 1. Measure and norm dictionary between `HSpace c MeridC` and `IIb.InHr c 2` -/

private theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)

private theorem lintegral_Ico_eq_Ioc_periodic {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞}
    (hper : Function.Periodic h c) :
    ∫⁻ q in Ico (-c / 2) (c / 2), h q = ∫⁻ q in Ioc 0 c, h q := by
  have hlen : c / 2 = -c / 2 + c := by ring
  have hae : (Ico (-c / 2) (c / 2) : Set ℝ) =ᵐ[volume] Ioc (-c / 2) (-c / 2 + c) := by
    rw [hlen]
    exact Ico_ae_eq_Ioc
  rw [setLIntegral_congr hae]
  have : Fact (0 < c) := ⟨hc⟩
  have e1 := AddCircle.lintegral_preimage (T := c) (-c / 2) hper.lift
  have e2 := AddCircle.lintegral_preimage (T := c) 0 hper.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e2
  rw [e1, e2]

private theorem lintegral_qCell_eq_cell_periodic {c : ℝ} (hc : 0 < c) {g : Profile → ℝ≥0∞}
    (hgm : Measurable g) (hper : B0220.QPeriodic c g) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c, g p = ∫⁻ p in B0220.cell c, g p := by
  unfold UnforcedLeray.Axi.qCell B0220.cell
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), ← Measure.prod_restrict, ← Measure.prod_restrict,
    lintegral_prod _ hgm.aemeasurable, lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun s => ?_
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), ← Measure.prod_restrict, ← Measure.prod_restrict]
  have hgs : Measurable fun x : ℝ × ℝ => g (s, x) :=
    hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hgs.aemeasurable, lintegral_prod _ hgs.aemeasurable]
  have hswap1 := lintegral_lintegral_swap
    (μ := (volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2)))
    (ν := (volume : Measure ℝ).restrict univ)
    (f := fun q η => g (s, q, η)) hgs.aemeasurable
  have hswap2 := lintegral_lintegral_swap
    (μ := (volume : Measure ℝ).restrict (Ioc 0 c))
    (ν := (volume : Measure ℝ).restrict univ)
    (f := fun q η => g (s, q, η)) hgs.aemeasurable
  rw [hswap1, hswap2]
  refine lintegral_congr fun η => ?_
  exact lintegral_Ico_eq_Ioc_periodic hc (fun q => hper (s, q, η))

private theorem lintegral_hMeas_two_eq {c : ℝ} (hc : 0 < c) {f : Profile → MeridC}
    (hfm : Measurable f) (hper : B0220.QPeriodic c f) :
    ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Short.IIb.hMeas c 2) =
      ENNReal.ofReal c⁻¹ * ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
  have hexp : (2 : ℝ) / 2 - 5 / 2 = -(3 / 2 : ℝ) := by norm_num
  unfold UnforcedLeray.Short.IIb.hMeas
  rw [hexp, UnforcedLeray.Axi.lintegral_ageμ hc (-(3 / 2 : ℝ)) (hfm.enorm.pow_const _)]
  have hfactor : ∀ p : Profile,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) * ‖f p‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal c⁻¹ * (weightH p * ‖f p‖ₑ ^ (2 : ℝ)) := fun p => by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), weightH, mul_assoc]
  simp_rw [hfactor]
  have hgm : Measurable fun p : Profile => weightH p * ‖f p‖ₑ ^ (2 : ℝ) :=
    measurable_weightH.mul (hfm.enorm.pow_const _)
  have hgper : B0220.QPeriodic c (fun p : Profile => weightH p * ‖f p‖ₑ ^ (2 : ℝ)) := fun p => by
    show weightH (p.1, p.2.1 + c, p.2.2) * ‖f (p.1, p.2.1 + c, p.2.2)‖ₑ ^ (2 : ℝ) = _
    rw [hper p]
    rfl
  have hwd : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ p in B0220.cell c, weightH p * ‖f p‖ₑ ^ (2 : ℝ) :=
    lintegral_withDensity_eq_lintegral_mul _ measurable_weightH (hfm.enorm.pow_const _)
  rw [lintegral_const_mul _ hgm, lintegral_qCell_eq_cell_periodic hc hgm hgper, ← hwd]

private theorem hNorm_two_eq {c : ℝ} (hc : 0 < c) {f : Profile → MeridC}
    (hfm : Measurable f) (hper : B0220.QPeriodic c f) :
    UnforcedLeray.Short.IIb.hNorm c 2 f =
      ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm f 2 (measureH c) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  unfold UnforcedLeray.Short.IIb.hNorm
  rw [h2]
  have hc_sq : ENNReal.ofReal (Real.sqrt c⁻¹) ^ (2 : ℝ) = ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt (inv_nonneg.2 hc.le)]
  have hsq : eLpNorm f 2 (UnforcedLeray.Short.IIb.hMeas c 2) ^ (2 : ℝ) =
      (ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm f 2 (measureH c)) ^ (2 : ℝ) := by
    rw [eLpNorm_two_sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      eLpNorm_two_sq, hc_sq]
    exact lintegral_hMeas_two_eq hc hfm hper
  apply le_antisymm <;> rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2), hsq]

private theorem measurable_periodize_merid (c : ℝ) {f : Profile → MeridC} (hf : Measurable f) :
    Measurable (periodize c f) :=
  hf.comp (measurable_fst.prodMk
    (((measurable_reduceIoc c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

private theorem periodize_ae_measureH {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) :
    periodize c (W : Profile → MeridC) =ᵐ[measureH c] (W : Profile → MeridC) := by
  filter_upwards [ae_cell_measureH c] with p hp
  exact periodize_of_mem hc (W : Profile → MeridC) hp

private theorem inHr_smul_periodize {c : ℝ} (hc : 0 < c) (κ : ℝ) (w : HSpace c MeridC) :
    UnforcedLeray.Short.IIb.InHr c 2
      (fun p => ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) p) := by
  set f : Profile → MeridC := fun p => ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) p
  have hwm : Measurable (periodize c (w : Profile → MeridC)) :=
    measurable_periodize_merid c (Lp.stronglyMeasurable w).measurable
  have hfm : Measurable f := hwm.const_smul ((κ : ℝ) : ℂ)
  have hfper : B0220.QPeriodic c f := fun p => by
    show ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) (p.1, p.2.1 + c, p.2.2) = _
    rw [qPeriodic_periodize hc (w : Profile → MeridC) p]
  refine ⟨Eventually.of_forall fun p => hfper p, hfm.aestronglyMeasurable, ?_⟩
  rw [hNorm_two_eq hc hfm hfper]
  have heq : eLpNorm (periodize c (w : Profile → MeridC)) 2 (measureH c) =
      eLpNorm (w : Profile → MeridC) 2 (measureH c) :=
    eLpNorm_congr_ae (periodize_ae_measureH hc w)
  have hfin : eLpNorm f 2 (measureH c) < ⊤ := by
    rw [show f = ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) from rfl,
      eLpNorm_const_smul ((κ : ℝ) : ℂ) (periodize c (w : Profile → MeridC)) 2 (measureH c), heq]
    exact ENNReal.mul_lt_top enorm_lt_top (Lp.eLpNorm_lt_top w)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

private theorem ageμ_nonpos_null {c a : ℝ} (hc : 0 < c) :
    UnforcedLeray.Axi.ageμ c a {x : Profile | ¬ 0 < x.1} = 0 := by
  have hm : MeasurableSet {x : Profile | ¬ 0 < x.1} :=
    (measurableSet_Ioi.preimage measurable_fst).compl
  have h := UnforcedLeray.Axi.lintegral_ageμ hc a
    (f := ({x : Profile | ¬ 0 < x.1} : Set Profile).indicator 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm] at h
  rw [h]
  have h0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
        ({x : Profile | ¬ 0 < x.1} : Set Profile).indicator (1 : Profile → ℝ≥0∞) p = 0 := by
    intro p hp
    have hnot : p ∉ ({x : Profile | ¬ 0 < x.1} : Set Profile) := not_not.2 hp.1
    rw [Set.indicator_of_notMem hnot, mul_zero]
  have hms : MeasurableSet (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  rw [setLIntegral_congr_fun hms h0]
  simp

private theorem ae_hMeas_of_periodicRep {c r : ℝ} (hc : 0 < c) {b b' : UnforcedLeray.Short.IIb.CProf}
    {M : Set UnforcedLeray.Short.IIb.Coord} (hMm : MeasurableSet M) (hM0 : volume M = 0)
    (hbb' : ∀ x : UnforcedLeray.Short.IIb.Coord, 0 < x.1 → x ∉ M → b x = b' x) :
    b' =ᵐ[UnforcedLeray.Short.IIb.hMeas c r] b := by
  have h1 : ∀ᵐ x ∂(UnforcedLeray.Short.IIb.hMeas c r), x ∉ M :=
    measure_eq_zero_iff_ae_notMem.1
      (UnforcedLeray.Short.IIb.ageμ_null_of_volume_null hc hMm hM0)
  have h2 : ∀ᵐ x ∂(UnforcedLeray.Short.IIb.hMeas c r), 0 < x.1 := by
    rw [ae_iff]
    exact ageμ_nonpos_null hc
  filter_upwards [h1, h2] with x hxM hxpos
  exact (hbb' x hxpos hxM).symm

/-! ### 2. Pointwise and `HasRepY` bridge between `U (liftVec w)` and `IIb.NvC` -/

private theorem radius_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    radius (ε • y) = ε * radius y := by
  unfold radius
  simp only [PiLp.smul_apply, smul_eq_mul]
  have h : (ε * y 0) ^ 2 + (ε * y 1) ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

private theorem ageS_smul_eq_age {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    ageS (ε • y) = UnforcedLeray.Axi.age ε⁻¹ y := by
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  unfold ageS UnforcedLeray.Axi.age
  rw [radius_smul_pos hε, hr]
  by_cases hy : UnforcedLeray.Axi.ϱ y = 0
  · simp [hy]
  · have hε0 : ε ≠ 0 := hε.ne'
    field_simp

private theorem liftA_smul_eq_sqrt_age {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    liftA (ε • y) = Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) := by
  rw [← ageS_smul_eq_age hε y]
  have hrad : 0 ≤ radius (ε • y) := by unfold radius; exact Real.sqrt_nonneg _
  unfold ageS liftA
  rw [Real.sqrt_inv, Real.sqrt_sq hrad]

private theorem chart_smul_eq_axiChart {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) (τ : ℝ) :
    B0220.chart ε (ε • y, τ) = UnforcedLeray.Axi.chart ε⁻¹ τ y := by
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  have hε0 : ε ≠ 0 := hε.ne'
  unfold B0220.chart UnforcedLeray.Axi.chart
  refine Prod.ext (ageS_smul_eq_age hε y) (Prod.ext ?_ ?_)
  · unfold cellQ UnforcedLeray.Axi.phase
    rw [← ageS_smul_eq_age hε y]
    unfold ageS
    rw [Real.log_inv, Real.log_pow]
    push_cast
    field_simp
    ring
  · unfold etaCoord UnforcedLeray.Axi.trans
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [radius_smul_pos hε, hr]
    by_cases hy : UnforcedLeray.Axi.ϱ y = 0
    · simp [hy]
    · field_simp

private theorem unitRC_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    unitRC (ε • y) = unitRC y := by
  have hε0 : ε ≠ 0 := hε.ne'
  unfold unitRC
  simp only [PiLp.smul_apply, smul_eq_mul, radius_smul_pos hε, mul_div_mul_left _ _ hε0]

private theorem frameC_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) (v : MeridC) :
    frameC (ε • y) v = frameC y v := by
  simp only [frameC_apply, unitRC_smul_pos hε]

private theorem nvC_pointwise_eq {ε c : ℝ} (hε : 0 < ε) {b : Profile → MeridC}
    (hper : B0220.QPeriodic c b) (κ : ℝ) (τ : ℝ) (y : UnforcedLeray.Space) (n : ℤ) :
    UnforcedLeray.Short.IIb.NvC ε⁻¹ (fun p => ((κ : ℝ) : ℂ) • b p) (τ, y) =
      (((κ * liftA (ε • y) : ℝ) : ℂ)) •
        frameC (ε • y) (b (B0220.chart ε (ε • y, τ + (n : ℝ) * (2 * ε * c)))) := by
  have hR0 : (ε⁻¹ : ℝ) ≠ 0 := inv_ne_zero hε.ne'
  have hPdiv : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hper_q : ∀ x : UnforcedLeray.Short.IIb.Coord,
      b (x + FBCLL.qv c) = b x := fun x => by
    rw [FBCLL.add_qv_eq]
    exact hper x
  have hchart_shift :
      b (B0220.chart ε (ε • y, τ + (n : ℝ) * (2 * ε * c))) = b (UnforcedLeray.Axi.chart ε⁻¹ τ y) := by
    rw [chart_smul_eq_axiChart hε]
    have hstep_qv : ∀ τ' : ℝ,
        UnforcedLeray.Axi.chart ε⁻¹ (τ' + 2 * ε * c) y =
          UnforcedLeray.Axi.chart ε⁻¹ τ' y + FBCLL.qv c := fun τ' => by
      rw [UnforcedLeray.Axi.chart_add_period hR0 hPdiv, FBCLL.add_qv_eq]
      rfl
    have h1 : ∀ m : ℤ, UnforcedLeray.Axi.chart ε⁻¹ (τ + (m : ℝ) * (2 * ε * c)) y =
        UnforcedLeray.Axi.chart ε⁻¹ τ y + FBCLL.qv ((m : ℝ) * c) := by
      intro m
      induction m using Int.induction_on with
      | zero => simp [FBCLL.qv]
      | succ k ih =>
        have e1 : τ + ((k + 1 : ℤ) : ℝ) * (2 * ε * c) =
            (τ + ((k : ℤ) : ℝ) * (2 * ε * c)) + 2 * ε * c := by push_cast; ring
        rw [e1, hstep_qv, ih, FBCLL.add_qv_add_qv]
        congr 2; push_cast; ring
      | pred k ih =>
        have e1 : τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c) + 2 * ε * c =
            τ + ((-(k : ℤ) : ℤ) : ℝ) * (2 * ε * c) := by push_cast; ring
        have hstep := hstep_qv (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c))
        rw [e1] at hstep
        have hsub : UnforcedLeray.Axi.chart ε⁻¹ (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c)) y =
            UnforcedLeray.Axi.chart ε⁻¹ (τ + ((-(k : ℤ) : ℤ) : ℝ) * (2 * ε * c)) y +
              FBCLL.qv (-c) := by
          calc UnforcedLeray.Axi.chart ε⁻¹ (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c)) y
              = UnforcedLeray.Axi.chart ε⁻¹ (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c)) y +
                  FBCLL.qv c + FBCLL.qv (-c) := by
                rw [FBCLL.add_qv_add_qv, add_neg_cancel]; simp [FBCLL.qv]
            _ = _ := by rw [← hstep]
        rw [hsub, ih, FBCLL.add_qv_add_qv]
        congr 2; push_cast; ring
    rw [h1 n]
    exact FBCLL.periodic_int hper_q n _
  rw [hchart_shift, frameC_smul_pos hε, liftA_smul_eq_sqrt_age hε]
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  have hv0 := Complex.re_add_im (b (UnforcedLeray.Axi.chart ε⁻¹ τ y) 0)
  have hv1 := Complex.re_add_im (b (UnforcedLeray.Axi.chart ε⁻¹ τ y) 1)
  ext i
  simp only [UnforcedLeray.Short.IIb.NvC, UnforcedLeray.Axi.Nv,
    UnforcedLeray.Axi.frameL_apply, UnforcedLeray.Short.IIb.reM,
    UnforcedLeray.Short.IIb.imM, frameC_apply, unitRC, unitZC,
    UnforcedLeray.Axi.eR, UnforcedLeray.Axi.hor, UnforcedLeray.Axi.e3,
    UnforcedLeray.coordinateVector, UnforcedLeray.B0412.realC_apply,
    PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hr]
  fin_cases i
  · simp [div_eq_inv_mul]
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ *
      ((UnforcedLeray.Axi.ϱ y : ℂ)⁻¹ * y 0)) * hv0
  · simp [div_eq_inv_mul]
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ *
      ((UnforcedLeray.Axi.ϱ y : ℂ)⁻¹ * y 1)) * hv0
  · simp
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ) * hv1

private theorem lift_prefactor_eq {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    Real.sqrt (2 * ε * c) * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ =
      Real.sqrt (c / Real.pi) * ε := by
  have h1 : 0 ≤ Real.sqrt (2 * ε * c) * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ := by
    positivity
  have h2 : 0 ≤ Real.sqrt (c / Real.pi) * ε := by positivity
  rw [← sq_eq_sq₀ h1 h2]
  have hrpow : (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [mul_pow, mul_pow, inv_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hrpow]
  field_simp

private theorem toCell_snd_shift {P : ℝ} [Fact (0 < P)] (τ : ℝ) :
    ∃ n : ℤ, ((AddCircle.measurableEquivIoc P 0 (τ : AddCircle P) : Ioc (0 : ℝ) (0 + P)) : ℝ) =
      τ + (n : ℝ) * P := by
  set t' : ℝ := ((AddCircle.measurableEquivIoc P 0 (τ : AddCircle P) : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have h0 : ((t' - τ : ℝ) : AddCircle P) = 0 := by
    rw [QuotientAddGroup.mk_sub]
    have heq : (t' : AddCircle P) = (τ : AddCircle P) := AddCircle.coe_equivIoc
    rw [heq, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).mp h0
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

private theorem hasRepY_phaseLift_liftVec {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    [hPpos : Fact (0 < 2 * ε * c)]
    (U : B0223.X SpaceC (2 * ε * c) →ₗᵢ[ℂ] Yq (2 * ε * c) 2)
    (hU : N01.IsPhaseLift ε (2 * ε * c) U) (w : HSpace c MeridC) :
    UnforcedLeray.Short.IIb.HasRepY
      (U (B0223.liftVec hε hc rfl w))
      (UnforcedLeray.Short.IIb.NvC ε⁻¹
        (fun p => ((Real.sqrt (c / Real.pi) * ε : ℝ) : ℂ) •
          periodize c (w : Profile → MeridC) p)) := by
  set P : ℝ := 2 * ε * c
  set κ : ℝ := Real.sqrt (c / Real.pi) * ε
  set b_w : Profile → MeridC := periodize c (w : Profile → MeridC)
  set b₀ : UnforcedLeray.Short.IIb.CProf := fun p => ((κ : ℝ) : ℂ) • b_w p
  set F : B0223.X SpaceC P := B0223.liftVec hε hc rfl w
  have hb₀_meas : Measurable b₀ :=
    (measurable_periodize_merid c (Lp.stronglyMeasurable w).measurable).const_smul ((κ : ℝ) : ℂ)
  refine ⟨(UnforcedLeray.Short.IIb.NvCInYrHelp.measurable_NvC' ε⁻¹ hb₀_meas).aestronglyMeasurable,
    ?_⟩
  have hF : ∀ᵐ z ∂(volume : Measure (B0223.PSpace P)),
      (F : B0223.PSpace P → SpaceC) z =
        (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA z.1 •
          frameC z.1 (b_w (B0220.chart ε (B0223.toCell P z))) :=
    B0223.coeFn_liftVec hε hc rfl w
  have hdil : Measure.QuasiMeasurePreserving
      (fun z : B0223.PSpace P => (ε • z.1, z.2)) volume volume := by
    refine ⟨((measurable_const_smul ε).comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hF2 := hdil.ae hF
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × UnforcedLeray.Space → B0223.PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure UnforcedLeray.Space))
      (volume : Measure (B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae hF2)
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) := by
    have h' : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))),
        ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
          (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
            (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
              frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) := by
      rw [← AddCircle.volume_eq_smul_haarAddCircle]
      exact hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hPpos.out).ne').1 h'
  have hslice_circle : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((U F θ : Lp CVec3 2 (volume : Measure UnforcedLeray.Space)) :
          UnforcedLeray.Space → CVec3) =ᵐ[volume]
        fun y => (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) •
          ((Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ))))) := by
    filter_upwards [hU F, hall] with θ h1 h2
    filter_upwards [h1, h2] with y e1 e2
    rw [e1, e2]
  filter_upwards [UnforcedLeray.PhaseTrace.ae_comp_mk hslice_circle] with τ hτ
  obtain ⟨n, hn⟩ := toCell_snd_shift (P := P) τ
  filter_upwards [hτ] with y hy
  rw [hy]
  have htoCell : B0223.toCell P (ε • y, (τ : AddCircle P)) = (ε • y, τ + (n : ℝ) * P) :=
    Prod.ext rfl hn
  rw [htoCell, nvC_pointwise_eq hε (qPeriodic_periodize hc (w : Profile → MeridC)) κ τ y n]
  have hpref : Real.sqrt P * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ = κ :=
    lift_prefactor_eq hc hε
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  rw [← hpref]
  push_cast
  ring

/-! ### 3. Unfolding `IIb.HasWeakVec IIb.vS IIb.dZero` to `N05_1_1Org.WeakS` -/

private theorem hasWeakVec_congr_rescaled {κ : ℝ} (hκ : 0 < κ)
    {b_w Sb Sb' : UnforcedLeray.Short.IIb.CProf} {M : Set UnforcedLeray.Short.IIb.Coord}
    (hM0 : volume M = 0)
    (hSb_eq : ∀ x : UnforcedLeray.Short.IIb.Coord, 0 < x.1 → x ∉ M → Sb x = Sb' x)
    (hw : UnforcedLeray.Short.IIb.HasWeakVec UnforcedLeray.Short.IIb.vS
      UnforcedLeray.Short.IIb.dZero (fun p => ((κ : ℝ) : ℂ) • b_w p) Sb) :
    UnforcedLeray.Short.IIb.HasWeakVec UnforcedLeray.Short.IIb.vS
      UnforcedLeray.Short.IIb.dZero b_w (fun p => ((κ⁻¹ : ℝ) : ℂ) • Sb' p) := by
  intro i
  obtain ⟨hint, heq⟩ := hw i
  have hM_ae : ∀ᵐ x : UnforcedLeray.Short.IIb.Coord, x ∉ M :=
    measure_eq_zero_iff_ae_notMem.1 hM0
  have hae_g : ∀ φ : UnforcedLeray.Short.IIb.Coord → ℝ,
      UnforcedLeray.Short.IIb.IsCoordTest φ →
      (fun x => (((κ⁻¹ : ℝ) : ℂ) • Sb' x) i * (φ x : ℂ)) =ᵐ[volume]
        fun x => ((κ⁻¹ : ℝ) : ℂ) * (Sb x i * (φ x : ℂ)) := by
    intro φ hφ
    filter_upwards [hM_ae] with x hxM
    by_cases hx : 0 < x.1
    · simp only [PiLp.smul_apply, smul_eq_mul, hSb_eq x hx hxM, mul_assoc]
    · have hnot : x ∉ tsupport φ := fun h => hx (Set.mem_prod.1 (hφ.supp h)).1
      have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [hφ0]
  have h_u : ∀ φ : UnforcedLeray.Short.IIb.Coord → ℝ, ∀ x : UnforcedLeray.Short.IIb.Coord,
      b_w x i * (UnforcedLeray.Short.IIb.coordTranspose UnforcedLeray.Short.IIb.vS
          UnforcedLeray.Short.IIb.dZero φ x : ℂ) =
        ((κ⁻¹ : ℝ) : ℂ) * ((((κ : ℝ) : ℂ) • b_w x) i *
          (UnforcedLeray.Short.IIb.coordTranspose UnforcedLeray.Short.IIb.vS
            UnforcedLeray.Short.IIb.dZero φ x : ℂ)) := by
    intro φ x
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hκ.ne',
      Complex.ofReal_one, one_mul]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp_rw [h_u φ]
    exact (hint φ hφ).1.const_mul _
  · exact ((hint φ hφ).2.const_mul ((κ⁻¹ : ℝ) : ℂ)).congr (hae_g φ hφ).symm
  · rw [integral_congr_ae (hae_g φ hφ)]
    simp_rw [h_u φ]
    rw [integral_const_mul, integral_const_mul, heq φ hφ]

private def testCut (c : ℝ) (θ : Profile → ℝ) (p : UnforcedLeray.Short.IIb.Coord) : ℝ :=
  p.1⁻¹ * FBCLL.qCut c p.2.1 * θ p

private theorem isCoordTest_testCut {c s0 s1 L : ℝ} (hc : 0 < c) (hs0 : 0 < s0)
    {θ : Profile → ℝ} (hθs : ContDiff ℝ ∞ θ)
    (hband : ∀ p : Profile, θ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    UnforcedLeray.Short.IIb.IsCoordTest (testCut c θ) := by
  have hsmooth : ContDiff ℝ ∞ (testCut c θ) := by
    rw [contDiff_iff_contDiffAt]
    intro x0
    by_cases hx : 0 < x0.1
    · have h1 : ContDiffAt ℝ ∞ (fun p : UnforcedLeray.Short.IIb.Coord => p.1⁻¹) x0 :=
        contDiffAt_fst.inv hx.ne'
      have h2 : ContDiffAt ℝ ∞
          (fun p : UnforcedLeray.Short.IIb.Coord => FBCLL.qCut c p.2.1) x0 :=
        ((FBCLL.qCut_contDiff c).comp (contDiff_fst.comp contDiff_snd)).contDiffAt
      exact (h1.mul h2).mul hθs.contDiffAt
    · have hlt : x0.1 < s0 := lt_of_le_of_lt (not_lt.1 hx) hs0
      have hev : testCut c θ =ᶠ[𝓝 x0] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with p hp
        have hθ0 : θ p = 0 := by
          by_contra hne
          exact absurd (hband p hne).1.1 (not_le.2 hp)
        simp [testCut, hθ0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  let K : Set UnforcedLeray.Short.IIb.Coord :=
    Icc s0 s1 ×ˢ (Icc (-c) c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsupp_sub : Function.support (testCut c θ) ⊆ K := by
    intro p hp
    rw [Function.mem_support] at hp
    have hq0 : FBCLL.qCut c p.2.1 ≠ 0 := fun h => hp (by simp [testCut, h])
    have hθ0 : θ p ≠ 0 := fun h => hp (by simp [testCut, h])
    have hq_mem : p.2.1 ∈ Ioc (-c) c := by
      by_contra h
      exact hq0 (FBCLL.qCut_eq_zero_of_not_mem hc h)
    obtain ⟨hs_mem, hη_mem⟩ := hband p hθ0
    exact ⟨hs_mem, Ioc_subset_Icc_self hq_mem, abs_le.1 hη_mem⟩
  have hts : tsupport (testCut c θ) ⊆ K := closure_minimal hsupp_sub hK.isClosed
  refine ⟨hsmooth, HasCompactSupport.intro hK fun p hp => ?_, fun p hp => ?_⟩
  · by_contra hne
    exact hp (hsupp_sub (Function.mem_support.2 hne))
  · have hpK := hts hp
    exact ⟨lt_of_lt_of_le hs0 hpK.1.1, trivial⟩

private theorem coordTranspose_vS_testCut {c s0 s1 L : ℝ} (hs0 : 0 < s0)
    {θ : Profile → ℝ} (hθs : ContDiff ℝ ∞ θ)
    (hband : ∀ p : Profile, θ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (x : UnforcedLeray.Short.IIb.Coord) :
    UnforcedLeray.Short.IIb.coordTranspose UnforcedLeray.Short.IIb.vS
        UnforcedLeray.Short.IIb.dZero (testCut c θ) x =
      -(FBCLL.qCut c x.2.1 * pdS θ x) := by
  have hmul : (fun y : UnforcedLeray.Short.IIb.Coord => y.1 * testCut c θ y) =
      fun y => FBCLL.qCut c y.2.1 * θ y := by
    funext y
    by_cases hy : y.1 = 0
    · have hθ0 : θ y = 0 := by
        by_contra hne
        have := (hband y hne).1.1
        linarith
      simp [testCut, hy, hθ0]
    · simp only [testCut]
      field_simp
  unfold UnforcedLeray.Short.IIb.coordTranspose UnforcedLeray.Short.IIb.dZero
  rw [Fin.sum_univ_three]
  have hv0 : (fun y : UnforcedLeray.Short.IIb.Coord =>
      UnforcedLeray.Short.IIb.vS y 0 * testCut c θ y) =
      fun y => FBCLL.qCut c y.2.1 * θ y := hmul
  have hv1 : (fun y : UnforcedLeray.Short.IIb.Coord =>
      UnforcedLeray.Short.IIb.vS y 1 * testCut c θ y) = fun _ => 0 := by
    funext y; simp [UnforcedLeray.Short.IIb.vS]
  have hv2 : (fun y : UnforcedLeray.Short.IIb.Coord =>
      UnforcedLeray.Short.IIb.vS y 2 * testCut c θ y) = fun _ => 0 := by
    funext y; simp [UnforcedLeray.Short.IIb.vS]
  unfold UnforcedLeray.Short.IIb.cpd
  rw [hv0, hv1, hv2]
  simp only [fderiv_const_apply, zero_apply, add_zero, zero_mul]
  have hq_diff :=
    (((FBCLL.qCut_contDiff c).differentiable (by simp) x.2.1).hasFDerivAt).comp x
      ((hasFDerivAt_fst (𝕜 := ℝ)).comp x (hasFDerivAt_snd (𝕜 := ℝ)))
  have hθ_diff : HasFDerivAt θ (fderiv ℝ θ x) x :=
    (hθs.differentiable (by simp) x).hasFDerivAt
  have hprod_eq : fderiv ℝ (fun y : UnforcedLeray.Short.IIb.Coord => FBCLL.qCut c y.2.1 * θ y) x =
      _ := (hq_diff.mul hθ_diff).fderiv
  rw [hprod_eq]
  simp [UnforcedLeray.Short.IIb.cdir, pdS]

private theorem integrableOn_two_cells_of_cell {c : ℝ} (hc : 0 < c)
    {G : UnforcedLeray.Short.IIb.Coord → ℂ}
    (hper : ∀ x, G (x + FBCLL.qv c) = G x)
    (hcell : IntegrableOn G (B0220.cell c)) :
    IntegrableOn G (Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ)) := by
  set A : Set UnforcedLeray.Short.IIb.Coord := Ioi 0 ×ˢ (Ioc (-c) 0 ×ˢ univ)
  set B : Set UnforcedLeray.Short.IIb.Coord := B0220.cell c
  have hA_pre : A = (fun x : UnforcedLeray.Short.IIb.Coord => x + FBCLL.qv c) ⁻¹' B := by
    ext x
    simp only [A, B, B0220.cell, mem_preimage, mem_prod, mem_Ioi, mem_Ioc, mem_univ, and_true,
      FBCLL.add_qv_fst, FBCLL.add_qv_snd_fst]
    constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩)
  have hA_int : IntegrableOn G A := by
    have hmp := measurePreserving_add_right (volume : Measure UnforcedLeray.Short.IIb.Coord)
      (FBCLL.qv c)
    have hme : MeasurableEmbedding
        (fun x : UnforcedLeray.Short.IIb.Coord => x + FBCLL.qv c) :=
      (MeasurableEquiv.addRight (FBCLL.qv c)).measurableEmbedding
    have hcomp : (G ∘ fun x : UnforcedLeray.Short.IIb.Coord => x + FBCLL.qv c) = G :=
      funext hper
    have h1 := (hmp.integrableOn_comp_preimage hme (f := G) (s := B)).2 hcell
    rwa [hcomp, ← hA_pre] at h1
  have hunion : Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ) = A ∪ B := by
    ext x
    simp only [A, B, B0220.cell, mem_union, mem_prod, mem_Ioi, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hx0 : x.2.1 ≤ 0
      · exact Or.inl ⟨h1, h2, hx0⟩
      · exact Or.inr ⟨h1, not_le.1 hx0, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, by linarith⟩
      · exact ⟨h1, by linarith, h3⟩
  rw [hunion]
  exact hA_int.union hcell

private theorem periodize_ae_cellMeasure {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC)
    {W_raw : Profile → MeridC}
    (hae : (W : Profile → MeridC) =ᵐ[measureH c] W_raw) :
    periodize c (W : Profile → MeridC) =ᵐ[cellMeasure c] W_raw := by
  have hae_cell : ∀ᵐ p ∂(cellMeasure c), weightH p ≠ 0 → (W : Profile → MeridC) p = W_raw p :=
    (ae_withDensity_iff measurable_weightH).1 hae
  filter_upwards [ae_restrict_mem (measurableSet_cell c), hae_cell] with p hp hpw
  have hw0 : weightH p ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hp.1 _)).ne'
  rw [periodize_of_mem hc (W : Profile → MeridC) hp, hpw hw0]

private theorem inner_merid_single (x : MeridC) (a : ℂ) (i : Fin 2) :
    inner ℂ x (a • EuclideanSpace.single i (1 : ℂ)) = starRingEnd ℂ (x i) * a := by
  rw [inner_smul_right, EuclideanSpace.inner_single_right, one_mul, mul_comm]

private theorem inner_merid_sinv_single (x : MeridC) (s : ℝ) (a : ℂ) (i : Fin 2) :
    inner ℂ x (s⁻¹ • (a • EuclideanSpace.single i (1 : ℂ))) =
      starRingEnd ℂ (x i) * ((s⁻¹ : ℝ) : ℂ) * a := by
  rw [← Complex.coe_smul, smul_smul, inner_merid_single, ← mul_assoc]

private theorem nice_real_single (c : ℝ) {s0 s1 L : ℝ} (hs0 : 0 < s0)
    {θ : Profile → ℝ} (hθc : Continuous θ)
    (hband : ∀ p : Profile, θ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (i : Fin 2) :
    N05_1_1P.Nice c (fun p => ((θ p : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)) := by
  let ψ : Profile → MeridC := fun p => ((θ p : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)
  have hm : Measurable ψ :=
    (Complex.continuous_ofReal.comp hθc).measurable.smul_const _
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hθc.continuousOn
  refine ⟨hm, s0, s1, L, max C0 0, hs0, fun p hp => ?_, fun p hp => ?_⟩
  · exact hband p fun h0 => hp (by simp [h0])
  · by_cases h0 : θ p = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hband p h0
      have hpK : p ∈ K := ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩
      have hsingle : ‖(EuclideanSpace.single i (1 : ℂ) : MeridC)‖ = 1 := by simp
      calc ‖ψ p‖ = ‖((θ p : ℝ) : ℂ)‖ * ‖(EuclideanSpace.single i (1 : ℂ) : MeridC)‖ :=
            norm_smul _ _
        _ = ‖θ p‖ := by rw [hsingle, mul_one, Complex.norm_real]
        _ ≤ C0 := hC0 p hpK
        _ ≤ max C0 0 := le_max_left _ _

private theorem cell_scalar_ibp {c s0 s1 L : ℝ} (hc : 0 < c) (hs0 : 0 < s0)
    (w Sw : HSpace c MeridC) {Sw_raw : Profile → MeridC}
    (hSw_per : B0220.QPeriodic c Sw_raw)
    (hSw_cell : periodize c (Sw : Profile → MeridC) =ᵐ[cellMeasure c] Sw_raw)
    (hw_weak : UnforcedLeray.Short.IIb.HasWeakVec UnforcedLeray.Short.IIb.vS
      UnforcedLeray.Short.IIb.dZero (periodize c (w : Profile → MeridC)) Sw_raw)
    {θ : Profile → ℝ} (hθs : ContDiff ℝ ∞ θ) (hθper : B0220.QPeriodic c θ)
    (hband : ∀ p : Profile, θ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (i : Fin 2) :
    ∫ p, starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θ p : ℝ) : ℂ) ∂(cellMeasure c) =
      -∫ p, starRingEnd ℂ (periodize c (w : Profile → MeridC) p i) *
        ((pdS θ p : ℝ) : ℂ) ∂(cellMeasure c) := by
  have htest := isCoordTest_testCut hc hs0 hθs hband
  have hweak_i := (hw_weak i).2 (testCut c θ) htest
  set b_w : Profile → MeridC := periodize c (w : Profile → MeridC)
  have hbw_per : B0220.QPeriodic c b_w := qPeriodic_periodize hc (w : Profile → MeridC)
  set G₁ : UnforcedLeray.Short.IIb.Coord → ℂ :=
    fun x => Sw_raw x i * ((x.1⁻¹ * θ x : ℝ) : ℂ)
  set G₂ : UnforcedLeray.Short.IIb.Coord → ℂ :=
    fun x => b_w x i * ((pdS θ x : ℝ) : ℂ)
  have hLHS_rew : ∀ x : UnforcedLeray.Short.IIb.Coord,
      Sw_raw x i * (testCut c θ x : ℂ) = (FBCLL.qCut c x.2.1 : ℂ) * G₁ x := fun x => by
    simp only [testCut, G₁]; push_cast; ring
  have hRHS_rew : ∀ x : UnforcedLeray.Short.IIb.Coord,
      b_w x i * (UnforcedLeray.Short.IIb.coordTranspose UnforcedLeray.Short.IIb.vS
          UnforcedLeray.Short.IIb.dZero (testCut c θ) x : ℂ) =
        -((FBCLL.qCut c x.2.1 : ℂ) * G₂ x) := fun x => by
    rw [coordTranspose_vS_testCut hs0 hθs hband x]
    simp only [G₂]; push_cast; ring
  simp_rw [hLHS_rew, hRHS_rew] at hweak_i
  rw [integral_neg] at hweak_i
  have hG₁_per : ∀ x, G₁ (x + FBCLL.qv c) = G₁ x := fun x => by
    rw [FBCLL.add_qv_eq]
    simp only [G₁, hSw_per x, hθper x]
  have hG₁_pos : ∀ x : UnforcedLeray.Short.IIb.Coord, x.1 ≤ 0 → G₁ x = 0 := fun x hx => by
    have hθ0 : θ x = 0 := by
      by_contra hne
      linarith [(hband x hne).1.1]
    simp [G₁, hθ0]
  have hG₁_cell : IntegrableOn G₁ (B0220.cell c) := by
    have hnice1 := N05_1_1P.nice_sinv hc (nice_real_single c hs0 hθs.continuous hband i)
    have hint1 := N05_1_1P.integrable_inner_periodize hc Sw hnice1
    have hint1_conj : Integrable
        (fun p => starRingEnd ℂ
          (inner ℂ (periodize c (Sw : Profile → MeridC) p)
            (p.1⁻¹ • (((θ p : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ)))))
        (cellMeasure c) :=
      RCLike.conjCLE.integrable_comp_iff.2 hint1
    refine hint1_conj.congr ?_
    filter_upwards [hSw_cell] with p hp
    rw [hp, inner_merid_sinv_single]
    simp [G₁, mul_assoc]
  have hpdS_sp : N05_1_1P.SP c (pdS θ) := (N05_1_1P.SP.pdS ⟨hθs, hθper⟩)
  have hpdS_band : ∀ p : Profile, pdS θ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := fun p hp =>
    N05_1_1P.fderiv_band hband (fun h0 => hp (by simp [pdS, h0]))
  have hG₂_per : ∀ x, G₂ (x + FBCLL.qv c) = G₂ x := fun x => by
    rw [FBCLL.add_qv_eq]
    simp only [G₂, hbw_per x, hpdS_sp.2 x]
  have hG₂_pos : ∀ x : UnforcedLeray.Short.IIb.Coord, x.1 ≤ 0 → G₂ x = 0 := fun x hx => by
    have h0 : pdS θ x = 0 := by
      by_contra hne
      linarith [(hpdS_band x hne).1.1]
    simp [G₂, h0]
  have hG₂_cell : IntegrableOn G₂ (B0220.cell c) := by
    have hnice2 := nice_real_single c hs0 hpdS_sp.1.continuous hpdS_band i
    have hint2 := N05_1_1P.integrable_inner_periodize hc w hnice2
    have hint2_conj : Integrable
        (fun p => starRingEnd ℂ
          (inner ℂ (b_w p) (((pdS θ p : ℝ) : ℂ) • EuclideanSpace.single i (1 : ℂ))))
        (cellMeasure c) :=
      RCLike.conjCLE.integrable_comp_iff.2 hint2
    refine hint2_conj.congr (Eventually.of_forall fun p => ?_)
    dsimp only
    rw [inner_merid_single]
    simp [G₂]
  rw [FBCLL.integral_qCut_mul hc (Eventually.of_forall hG₁_per) hG₁_pos
      (integrableOn_two_cells_of_cell hc hG₁_per hG₁_cell),
    FBCLL.integral_qCut_mul hc (Eventually.of_forall hG₂_per) hG₂_pos
      (integrableOn_two_cells_of_cell hc hG₂_per hG₂_cell)] at hweak_i
  have hconj := congrArg (starRingEnd ℂ) hweak_i
  rw [← integral_conj, map_neg, ← integral_conj] at hconj
  have hL : (fun p : Profile => starRingEnd ℂ (G₁ p)) =
      fun p => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θ p : ℝ) : ℂ) := by
    funext p; simp [G₁]
  have hR : (fun p : Profile => starRingEnd ℂ (G₂ p)) =
      fun p => starRingEnd ℂ (b_w p i) * ((pdS θ p : ℝ) : ℂ) := by
    funext p; simp [G₂]
  unfold cellMeasure
  rwa [hL, hR] at hconj

private theorem weakS_of_hasWeakVec {c : ℝ} (hc : 0 < c) (w Sw : HSpace c MeridC)
    {Sw_raw : Profile → MeridC} (hSw_per : B0220.QPeriodic c Sw_raw)
    (hSw_cell : periodize c (Sw : Profile → MeridC) =ᵐ[cellMeasure c] Sw_raw)
    (hw_weak : UnforcedLeray.Short.IIb.HasWeakVec UnforcedLeray.Short.IIb.vS
      UnforcedLeray.Short.IIb.dZero (periodize c (w : Profile → MeridC)) Sw_raw) :
    N05_1_1Org.WeakS c w Sw := by
  intro φ hφ
  obtain ⟨s0, s1, L, hs0, hband⟩ := hφ.band
  set b_w : Profile → MeridC := periodize c (w : Profile → MeridC)
  have hcomp_ibp : ∀ i : Fin 2,
      ∫ p, starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ : ℝ) : ℂ) * φ p i ∂(cellMeasure c) =
        -∫ p, starRingEnd ℂ (b_w p i) * pdS φ p i ∂(cellMeasure c) := by
    intro i
    let projR : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
    let Lre : MeridC →L[ℝ] ℝ := Complex.reCLM.comp projR
    let Lim : MeridC →L[ℝ] ℝ := Complex.imCLM.comp projR
    set θre : Profile → ℝ := fun p => Lre (φ p)
    set θim : Profile → ℝ := fun p => Lim (φ p)
    have hre_s : ContDiff ℝ ∞ θre := Lre.contDiff.comp hφ.smooth
    have him_s : ContDiff ℝ ∞ θim := Lim.contDiff.comp hφ.smooth
    have hre_p : B0220.QPeriodic c θre := fun p => congrArg Lre (hφ.periodic p)
    have him_p : B0220.QPeriodic c θim := fun p => congrArg Lim (hφ.periodic p)
    have hre_b : ∀ p : Profile, θre p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
      fun p hp => hband p (fun h0 => hp (by simp [θre, h0]))
    have him_b : ∀ p : Profile, θim p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
      fun p hp => hband p (fun h0 => hp (by simp [θim, h0]))
    have hpdS_re : ∀ p : Profile, pdS θre p = (pdS φ p i).re := fun p => by
      have hd := (Lre.hasFDerivAt.comp p (hφ.smooth.differentiable (by simp) p).hasFDerivAt).fderiv
      change fderiv ℝ (Lre ∘ φ) p (1, 0, 0) = _
      rw [hd]
      rfl
    have hpdS_im : ∀ p : Profile, pdS θim p = (pdS φ p i).im := fun p => by
      have hd := (Lim.hasFDerivAt.comp p (hφ.smooth.differentiable (by simp) p).hasFDerivAt).fderiv
      change fderiv ℝ (Lim ∘ φ) p (1, 0, 0) = _
      rw [hd]
      rfl
    have e_re := cell_scalar_ibp hc hs0 w Sw hSw_per hSw_cell hw_weak hre_s hre_p hre_b i
    have e_im := cell_scalar_ibp hc hs0 w Sw hSw_per hSw_cell hw_weak him_s him_p him_b i
    have hint_L_re : Integrable
        (fun p => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θre p : ℝ) : ℂ)) (cellMeasure c) := by
      have hnice := N05_1_1P.nice_sinv hc (nice_real_single c hs0 hre_s.continuous hre_b i)
      refine (N05_1_1P.integrable_inner_periodize hc Sw hnice).congr ?_
      filter_upwards [hSw_cell] with p hp
      rw [hp, inner_merid_sinv_single]
      push_cast; ring
    have hint_L_im : Integrable
        (fun p => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θim p : ℝ) : ℂ)) (cellMeasure c) := by
      have hnice := N05_1_1P.nice_sinv hc (nice_real_single c hs0 him_s.continuous him_b i)
      refine (N05_1_1P.integrable_inner_periodize hc Sw hnice).congr ?_
      filter_upwards [hSw_cell] with p hp
      rw [hp, inner_merid_sinv_single]
      push_cast; ring
    have hpdS_re_b : ∀ p : Profile, pdS θre p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
      fun p hp => N05_1_1P.fderiv_band hre_b (fun h0 => hp (by simp [pdS, h0]))
    have hpdS_im_b : ∀ p : Profile, pdS θim p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
      fun p hp => N05_1_1P.fderiv_band him_b (fun h0 => hp (by simp [pdS, h0]))
    have hint_R_re : Integrable
        (fun p => starRingEnd ℂ (b_w p i) * ((pdS θre p : ℝ) : ℂ)) (cellMeasure c) := by
      have hnice := nice_real_single c hs0
        (N05_1_1P.SP.pdS ⟨hre_s, hre_p⟩).1.continuous hpdS_re_b i
      refine (N05_1_1P.integrable_inner_periodize hc w hnice).congr (Eventually.of_forall fun p => ?_)
      change inner ℂ (b_w p) _ = _
      rw [inner_merid_single]
    have hint_R_im : Integrable
        (fun p => starRingEnd ℂ (b_w p i) * ((pdS θim p : ℝ) : ℂ)) (cellMeasure c) := by
      have hnice := nice_real_single c hs0
        (N05_1_1P.SP.pdS ⟨him_s, him_p⟩).1.continuous hpdS_im_b i
      refine (N05_1_1P.integrable_inner_periodize hc w hnice).congr (Eventually.of_forall fun p => ?_)
      change inner ℂ (b_w p) _ = _
      rw [inner_merid_single]
    have hL_eq : (fun p : Profile => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ : ℝ) : ℂ) * φ p i) =
        fun p => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θre p : ℝ) : ℂ) +
          Complex.I * (starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ * θim p : ℝ) : ℂ)) := by
      funext p
      have hφi : ((θre p : ℝ) : ℂ) + ((θim p : ℝ) : ℂ) * Complex.I = φ p i :=
        Complex.re_add_im (φ p i)
      push_cast
      linear_combination (starRingEnd ℂ (Sw_raw p i) * (p.1⁻¹ : ℂ)) * hφi.symm
    have hR_eq : (fun p : Profile => starRingEnd ℂ (b_w p i) * pdS φ p i) =
        fun p => starRingEnd ℂ (b_w p i) * ((pdS θre p : ℝ) : ℂ) +
          Complex.I * (starRingEnd ℂ (b_w p i) * ((pdS θim p : ℝ) : ℂ)) := by
      funext p
      rw [hpdS_re p, hpdS_im p]
      have hdi : (((pdS φ p i).re : ℝ) : ℂ) + (((pdS φ p i).im : ℝ) : ℂ) * Complex.I = pdS φ p i :=
        Complex.re_add_im (pdS φ p i)
      linear_combination (starRingEnd ℂ (b_w p i)) * hdi.symm
    rw [hL_eq, hR_eq, integral_add hint_L_re (hint_L_im.const_mul Complex.I),
      integral_add hint_R_re (hint_R_im.const_mul Complex.I), integral_const_mul,
      integral_const_mul, e_re, e_im]
    ring
  have hLHS_ae : (fun p : Profile => inner ℂ (dsFromS (periodize c (Sw : Profile → MeridC)) p) (φ p))
      =ᵐ[cellMeasure c]
      fun p => (starRingEnd ℂ (Sw_raw p 0) * ((p.1⁻¹ : ℝ) : ℂ) * φ p 0) +
        (starRingEnd ℂ (Sw_raw p 1) * ((p.1⁻¹ : ℝ) : ℂ) * φ p 1) := by
    filter_upwards [hSw_cell] with p hp
    simp only [dsFromS, hp, PiLp.inner_apply, Fin.sum_univ_two, PiLp.smul_apply,
      Complex.real_smul, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  have hRHS_eq : (fun p : Profile => inner ℂ (b_w p) (pdS φ p)) =
      fun p => (starRingEnd ℂ (b_w p 0) * pdS φ p 0) +
        (starRingEnd ℂ (b_w p 1) * pdS φ p 1) := by
    funext p
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    ring
  have hint_compL : ∀ i : Fin 2, Integrable
      (fun p => starRingEnd ℂ (Sw_raw p i) * ((p.1⁻¹ : ℝ) : ℂ) * φ p i) (cellMeasure c) := by
    intro i
    let projC : MeridC →L[ℂ] MeridC :=
      (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))
    have hψ : IsMeridTest c (fun p => projC (φ p)) :=
      ⟨(projC.restrictScalars ℝ).contDiff.comp hφ.smooth,
        fun p => congrArg projC (hφ.periodic p),
        s0, s1, L, hs0, fun p hp => hband p (fun h0 => hp (by simp [h0]))⟩
    have hint := N05_1_1P.integrable_inner_periodize hc Sw
      (N05_1_1P.nice_sinv hc (N05_1_1P.nice_of_mt hc hψ))
    refine hint.congr ?_
    filter_upwards [hSw_cell] with p hp
    change inner ℂ (periodize c (Sw : Profile → MeridC) p)
        (p.1⁻¹ • ((φ p i) • EuclideanSpace.single i (1 : ℂ))) = _
    rw [hp, inner_merid_sinv_single]
  have hint_compR : ∀ i : Fin 2, Integrable
      (fun p => starRingEnd ℂ (b_w p i) * pdS φ p i) (cellMeasure c) := by
    intro i
    let projC : MeridC →L[ℂ] MeridC :=
      (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))
    have hψ : IsMeridTest c (fun p => projC (pdS φ p)) :=
      ⟨(projC.restrictScalars ℝ).contDiff.comp (N05_1_1P.mt_pdS hφ).smooth,
        fun p => congrArg projC ((N05_1_1P.mt_pdS hφ).periodic p),
        let ⟨a0, a1, aL, ha0, ha⟩ := (N05_1_1P.mt_pdS hφ).band
        ⟨a0, a1, aL, ha0, fun p hp => ha p (fun h0 => hp (by simp [h0]))⟩⟩
    have hint := N05_1_1P.integrable_inner_periodize hc w (N05_1_1P.nice_of_mt hc hψ)
    refine hint.congr (Eventually.of_forall fun p => ?_)
    change inner ℂ (b_w p) ((pdS φ p i) • EuclideanSpace.single i (1 : ℂ)) = _
    rw [inner_merid_single]
  rw [integral_congr_ae hLHS_ae, hRHS_eq,
    integral_add (hint_compL 0) (hint_compL 1),
    integral_add (hint_compR 0) (hint_compR 1),
    hcomp_ibp 0, hcomp_ibp 1]
  ring

/-! ### 4. Norm scaling factor identity and main theorem -/

private theorem scale_factor_one {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    (Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ)) * Real.sqrt c⁻¹ *
      (Real.sqrt (c / Real.pi) * ε) = 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 ≤ (Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ)) * Real.sqrt c⁻¹ *
      (Real.sqrt (c / Real.pi) * ε) := by positivity
  rw [← sq_eq_sq₀ hpos zero_le_one, one_pow, mul_pow, mul_pow, mul_pow,
    ← Real.rpow_natCast ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ))) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ Real.pi * (ε⁻¹) ^ 2)]
  norm_num
  rw [Real.sq_sqrt hc.le, Real.sq_sqrt (by positivity)]
  have hc0 : c ≠ 0 := hc.ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  field_simp

theorem phaseGeneratorTransport_aux : N05_1_1Org.PhaseGeneratorTransport := by
  refine ⟨1, zero_le_one, ?_⟩
  intro ν c ε _ hc hε _ P hPpos hP _ U hU w v hv
  subst hP
  set κ : ℝ := Real.sqrt (c / Real.pi) * ε
  have hκ : 0 < κ := by positivity
  set b_w : Profile → MeridC := periodize c (w : Profile → MeridC)
  set b₀ : UnforcedLeray.Short.IIb.CProf := fun p => ((κ : ℝ) : ℂ) • b_w p
  have hb₀_hr : UnforcedLeray.Short.IIb.InHr c 2 b₀ := inHr_smul_periodize hc κ w
  have hv_rep : UnforcedLeray.Short.IIb.HasRepY (v : Yq (2 * ε * c) 2)
      (UnforcedLeray.Short.IIb.NvC ε⁻¹ b₀) := by
    rw [hv]
    exact hasRepY_phaseLift_liftVec hc hε U hU w
  obtain ⟨d₀, hd₀_yr, hd₀_rep, hd₀_norm⟩ :=
    UnforcedLeray.Short.IIb.exists_isInYr_hasRepY_q (2 * ε * c) 2 two_pos ENNReal.ofNat_ne_top
      (by norm_num) (T0D v)
  have hptw : UnforcedLeray.Short.IIb.HasPtwOp (2 * ε * c) driftT
      (UnforcedLeray.Short.IIb.NvC ε⁻¹ b₀) d₀ :=
    (UnforcedLeray.Short.IIb.hasPtwOp_iff_hasPhaseOp (fun _ hΦ => hΦ.driftT)
      hv_rep hd₀_rep).2 (hasPhaseOp_T0D v)
  obtain ⟨Sb, hSb_weak, hSb_hr, hSb_bound⟩ :=
    driftRecovery_proof c ε 2 b₀ d₀ hc hε one_lt_two hb₀_hr hd₀_yr hptw
  obtain ⟨Sb', M, hSb'm, hSb'per_raw, hMm, hM0, _, hSb_eq⟩ :=
    UnforcedLeray.Short.IIb.periodicRepresentative c 2 hc Sb hSb_hr.periodic hSb_hr.meas
  have hSb'per : B0220.QPeriodic c Sb' := fun p => hSb'per_raw p.1 p.2.1 p.2.2
  have hSb_ae : Sb' =ᵐ[UnforcedLeray.Short.IIb.hMeas c 2] Sb :=
    ae_hMeas_of_periodicRep hc hMm hM0 hSb_eq
  have hSb'_hNorm : UnforcedLeray.Short.IIb.hNorm c 2 Sb' =
      UnforcedLeray.Short.IIb.hNorm c 2 Sb :=
    eLpNorm_congr_ae hSb_ae
  set Sw_raw : Profile → MeridC := fun p => ((κ⁻¹ : ℝ) : ℂ) • Sb' p
  have hSw_raw_m : Measurable Sw_raw := hSb'm.const_smul ((κ⁻¹ : ℝ) : ℂ)
  have hSw_raw_per : B0220.QPeriodic c Sw_raw := fun p => by
    show ((κ⁻¹ : ℝ) : ℂ) • Sb' (p.1, p.2.1 + c, p.2.2) = _
    rw [hSb'per p]
  have hSb'_eq_smul : Sb' = fun p => ((κ : ℝ) : ℂ) • Sw_raw p := by
    funext p
    simp only [Sw_raw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hκ.ne',
      Complex.ofReal_one, one_smul]
  have hSw_eLp_mul :
      ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm Sb' 2 (measureH c) =
        UnforcedLeray.Short.IIb.hNorm c 2 Sb := by
    rw [← hSb'_hNorm, hNorm_two_eq hc hSb'm hSb'per]
  have hSb'_eLp_lt : eLpNorm Sb' 2 (measureH c) < ⊤ := by
    have hlt : ENNReal.ofReal (Real.sqrt c⁻¹) * eLpNorm Sb' 2 (measureH c) < ⊤ := by
      rw [hSw_eLp_mul]
      exact hSb_hr.finite
    have hne0 : ENNReal.ofReal (Real.sqrt c⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (inv_pos.2 hc))).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne hne0
  have heLp_smul : ∀ (a : ℝ) (ha : 0 ≤ a) (g : Profile → MeridC),
      eLpNorm (fun p => ((a : ℝ) : ℂ) • g p) 2 (measureH c) =
        ENNReal.ofReal a * eLpNorm g 2 (measureH c) := by
    intro a ha g
    rw [show (fun p => ((a : ℝ) : ℂ) • g p) = ((a : ℝ) : ℂ) • g from rfl,
      eLpNorm_const_smul ((a : ℝ) : ℂ) g 2 (measureH c)]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ha]
  have hSw_mem : MemLp Sw_raw 2 (measureH c) := by
    refine ⟨hSw_raw_m.aestronglyMeasurable, ?_⟩
    rw [heLp_smul κ⁻¹ (inv_nonneg.2 hκ.le) Sb']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSb'_eLp_lt
  let Sw : HSpace c MeridC := hSw_mem.toLp Sw_raw
  have hSw_cell : periodize c (Sw : Profile → MeridC) =ᵐ[cellMeasure c] Sw_raw :=
    periodize_ae_cellMeasure hc Sw hSw_mem.coeFn_toLp
  have hw_weak : UnforcedLeray.Short.IIb.HasWeakVec UnforcedLeray.Short.IIb.vS
      UnforcedLeray.Short.IIb.dZero b_w Sw_raw :=
    hasWeakVec_congr_rescaled hκ hM0 hSb_eq hSb_weak
  have hWeakS : N05_1_1Org.WeakS c w Sw :=
    weakS_of_hasWeakVec hc w Sw hSw_raw_per hSw_cell hw_weak
  refine ⟨Sw, hWeakS, ?_⟩
  rw [one_mul]
  -- Evaluate LHS and RHS of `hSb_bound` in terms of `‖Sw‖`, `‖T0D v‖`, `‖v‖`.
  have hLHS_eq :
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ))) *
          UnforcedLeray.Short.IIb.hNorm c 2 Sb =
        ENNReal.ofReal ‖Sw‖ := by
    rw [← hSw_eLp_mul, hSb'_eq_smul, heLp_smul κ hκ.le Sw_raw,
      ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      scale_factor_one hc hε, ENNReal.ofReal_one, one_mul]
    have hSw_norm : eLpNorm Sw_raw 2 (measureH c) = eLpNorm (Sw : Profile → MeridC) 2 (measureH c) :=
      (eLpNorm_congr_ae hSw_mem.coeFn_toLp).symm
    rw [hSw_norm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Sw)]
  have hd₀_eq : UnforcedLeray.Short.IIb.phaseLpNorm (2 * ε * c) 2 d₀ =
      ENNReal.ofReal ‖T0D v‖ := by
    rw [← hd₀_norm, ENNReal.ofReal_toReal hd₀_yr.finite.ne]
  have hb₀_norm_eq :
      UnforcedLeray.Short.IIb.phaseLpNorm (2 * ε * c) 2
          (UnforcedLeray.Short.IIb.NvC ε⁻¹ b₀) =
        ENNReal.ofReal ‖(v : Yq (2 * ε * c) 2)‖ := by
    have hb₀_m : Measurable b₀ :=
      (measurable_periodize_merid c (Lp.stronglyMeasurable w).measurable).const_smul ((κ : ℝ) : ℂ)
    have hb₀_per : B0220.QPeriodic c b₀ := fun p => by
      show ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) (p.1, p.2.1 + c, p.2.2) =
        ((κ : ℝ) : ℂ) • periodize c (w : Profile → MeridC) p
      rw [qPeriodic_periodize hc (w : Profile → MeridC) p]
    rw [UnforcedLeray.Short.IIb.phaseLpNorm_NvC hc two_pos hε b₀ hb₀_hr.periodic hb₀_hr.meas,
      hNorm_two_eq hc hb₀_m hb₀_per, heLp_smul κ hκ.le b_w,
      ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      scale_factor_one hc hε, ENNReal.ofReal_one, one_mul,
      eLpNorm_congr_ae (periodize_ae_measureH hc w),
      ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w), ← Lp.norm_def,
      hv, U.norm_map, (B0223.liftVec hε hc rfl).norm_map]
  rw [hLHS_eq, hd₀_eq, hb₀_norm_eq, add_comm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] at hSb_bound
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (norm_nonneg _) (norm_nonneg _))).1 hSb_bound

end N05_1_1T

theorem phaseGeneratorTransport : N05_1_1Org.PhaseGeneratorTransport :=
  N05_1_1T.phaseGeneratorTransport_aux

end UnforcedLeray.Short.PartIIa
