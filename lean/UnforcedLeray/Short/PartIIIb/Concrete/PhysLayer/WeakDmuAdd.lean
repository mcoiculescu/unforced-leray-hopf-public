import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_B
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection

/-!
# `WeakDmuAdd`: the weak formulation is additive along the lift of `VelG`

Source of record: `the November 2 reference manuscript`, lines 1580-1583
(subtracting/adding two solutions of the free equation in the weak formulation).

Linearity of the lift `velPhys` along the `Lp` sum on the body measure (transferred to
`ageμ c (-3/2)`, whose density is positive), integrability of the pairings of compactly
supported continuous tests with an `L²` field on the phase cell, and additivity of `pairF`
in its field slot.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_eq_restrictedProductIntegral pairF_add_right_of_integrable)

/-- The normalised phase measure is a positive multiple of the restricted volume. -/
theorem wda_phaseμ_eq (P : ℝ) :
    phaseμ P = (ENNReal.ofReal P)⁻¹ • (volume : Measure (ℝ × Space)).restrict (phaseCell P) := by
  unfold phaseμ
  rw [Measure.prod_smul_left]
  congr 1
  have := Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)
  simpa [phaseCell, Measure.volume_eq_prod] using this

theorem wda_ae_phaseμ (P : ℝ) :
    ae (phaseμ P) = ae ((volume : Measure (ℝ × Space)).restrict (phaseCell P)) := by
  rw [wda_phaseμ_eq]
  have hc : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  exact le_antisymm (Measure.smul_absolutelyContinuous.ae_le)
    ((Measure.absolutelyContinuous_smul hc).ae_le)

theorem wda_realC_add (x y : Space) : B0412.realC (x + y) = B0412.realC x + B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem wda_realC_smul (k : ℝ) (x : Space) : B0412.realC (k • x) = (k : ℂ) • B0412.realC x := by
  ext i
  simp [B0412.realC_apply]

theorem wda_norm_realC (x : Space) : ‖B0412.realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [B0412.realC_apply, Complex.norm_real]

theorem wda_velPhys_eq (R c : ℝ) (hR : R ≠ 0) (b : Chart → Merid) :
    velPhys R c b = fun x => B0412.realC ((√Real.pi * R) • liftFun R c b x) := by
  funext x
  have h : (√Real.pi * R) ≠ 0 := mul_ne_zero (Real.sqrt_pos.2 Real.pi_pos).ne' hR
  simp only [velPhys, liftFun, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem wda_velPhys_congr {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {b b' : Chart → Merid}
    (hb : Measurable b) (hb' : Measurable b') (h : b =ᵐ[ageμ c (-3 / 2)] b') :
    velPhys ε⁻¹ c b =ᵐ[volume.restrict (phaseCell (2 * ε * c))] velPhys ε⁻¹ c b' := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have h1 := liftFun_congr_ae hR hc hP hb hb' h
  rw [wda_ae_phaseμ] at h1
  rw [wda_velPhys_eq _ _ hR.ne', wda_velPhys_eq _ _ hR.ne']
  filter_upwards [h1] with x hx
  simp only [hx]

theorem wda_velPhys_add_ae {c γ ν ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (b b' : VelG c γ ν) :
    velPhys ε⁻¹ c ((b + b' : VelG c γ ν) : Chart → Merid) =ᵐ[volume.restrict
      (phaseCell (2 * ε * c))] fun x => velPhys ε⁻¹ c (b : Chart → Merid) x +
        velPhys ε⁻¹ c (b' : Chart → Merid) x := by
  have hbm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hbm' : Measurable (b' : Chart → Merid) := (Lp.stronglyMeasurable b').measurable
  have hsm : Measurable ((b + b' : VelG c γ ν) : Chart → Merid) :=
    (Lp.stronglyMeasurable _).measurable
  have h0 : ((b + b' : VelG c γ ν) : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      (b : Chart → Merid) + (b' : Chart → Merid) := Lp.coeFn_add b b'
  have h1 : ((b + b' : VelG c γ ν) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (b : Chart → Merid) + (b' : Chart → Merid) := by
    unfold bodyMeasure at h0
    have hmeas : Measurable fun p : Chart =>
        ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul ((NearInst.gainFun_measurable γ ν).inv.pow_const 2))
    have h2 := (ae_withDensity_iff hmeas).1 h0
    filter_upwards [h2] with p hp
    refine hp ?_
    have : 0 < ginv γ ν p := by
      have : 0 < NearInst.gainFun γ ν p := NearInst.gainFun_pos γ ν p
      exact inv_pos.2 this
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have h3 := wda_velPhys_congr hc hε hsm (hbm.add hbm') h1
  refine h3.trans (Eventually.of_forall fun x => ?_)
  have e : perExt c ((b : Chart → Merid) + (b' : Chart → Merid)) =
      perExt c (b : Chart → Merid) + perExt c (b' : Chart → Merid) := rfl
  simp only [velPhys, Pi.add_apply, e, Nv_add, wda_realC_add]

/-- A continuous test with bounded spatial support pairs integrably with an `L²` field on the
phase cell. -/
theorem wda_integrable_dotL {P : ℝ} [Fact (0 < P)] {H w : ℝ × Space → CVec3}
    (hH : Continuous H) (hsupp : ∃ R, ∀ τ y, R < ‖y‖ → H (τ, y) = 0)
    (hw : MemLp w 2 (volume.restrict (phaseCell P))) :
    Integrable (fun x => dotL (H x) (w x)) (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hR⟩ := hsupp
  set μ : Measure (ℝ × Space) := volume.restrict (phaseCell P) with hμ
  set K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hKc.measurableSet
  have hKfin : μ K ≠ ∞ := by
    have hlt : μ K < ∞ := by
      rw [hμ, Measure.restrict_apply hKm]
      exact lt_of_le_of_lt (measure_mono inter_subset_left) hKc.measure_lt_top
    exact hlt.ne
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hH.continuousOn
  have hwK : MemLp (K.indicator w) 2 μ := hw.indicator hKm
  have hwK1 : MemLp (K.indicator w) 1 μ :=
    hwK.mono_exponent_of_measure_support_ne_top
      (fun x hx => Set.indicator_of_notMem hx _) hKfin (by norm_num)
  have hint : Integrable (fun x => ‖K.indicator w x‖) μ :=
    (memLp_one_iff_integrable.1 hwK1).norm
  have hmeas : AEStronglyMeasurable (fun x => dotL (H x) (w x)) μ :=
    dotL.aestronglyMeasurable_comp₂ hH.aestronglyMeasurable hw.aestronglyMeasurable
  have hdom : MeasurableSet (phaseCell P) := by
    unfold phaseCell
    exact measurableSet_Ioc.prod MeasurableSet.univ
  refine Integrable.mono' (hint.const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C)) hmeas ?_
  refine (ae_restrict_iff' hdom).2 (Eventually.of_forall fun x hx => ?_)
  by_cases hxK : x ∈ K
  · have h1 := hC x hxK
    have h2 : K.indicator w x = w x := Set.indicator_of_mem hxK _
    rw [h2]
    calc ‖dotL (H x) (w x)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖H x‖ * ‖w x‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C * ‖w x‖ := by gcongr
  · have hx0 : H x = 0 := by
      obtain ⟨τ, y⟩ := x
      refine hR τ y ?_
      by_contra hcon
      push Not at hcon
      exact hxK ⟨⟨hx.1.1.le, hx.1.2⟩, by simpa using hcon⟩
    rw [hx0, Set.indicator_of_notMem hxK]
    simp

/-- A body-measure `L²` function is `L²` for `ageμ` (the density is bounded below). -/
theorem wda_memLp_age {c γ ν : ℝ} (hν : 0 < ν) (b : VelG c γ ν) :
    MemLp (b : Chart → Merid) 2 (ageμ c (-3 / 2)) := by
  set m : ℝ≥0∞ := ENNReal.ofReal (Real.pi * Real.exp (-(|γ| / ν)) ^ 2) with hmdef
  have hm0 : m ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hmtop : m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : ∀ p : Chart, m ≤ ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
    intro p
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (-(|γ| / ν)) ^ 2 ≤ ginv γ ν p ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (ginv_lower_B hν p) 2
    exact mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
  have hmono : m • ageμ c (-3 / 2) ≤ bodyMeasure c γ ν := by
    unfold bodyMeasure
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall hle)
  have hage : ageμ c (-3 / 2) ≤ m⁻¹ • bodyMeasure c γ ν := by
    refine Measure.le_iff'.2 fun s => ?_
    have h := hmono s
    simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
    calc ageμ c (-3 / 2) s = m⁻¹ * (m * ageμ c (-3 / 2) s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
      _ ≤ m⁻¹ * bodyMeasure c γ ν s := by gcongr
  exact (Lp.memLp b).of_measure_le_smul (ENNReal.inv_ne_top.2 hm0) hage

/-- The velocity lift is `L²` on the phase cell. -/
theorem wda_memLp_velPhys {c γ ν ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (b : VelG c γ ν) :
    MemLp (velPhys ε⁻¹ c (b : Chart → Merid)) 2
      (volume.restrict (phaseCell (2 * ε * c))) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hbm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hlp := wda_memLp_age (c := c) (γ := γ) hν b
  have hl : MemLp (liftFun ε⁻¹ c (b : Chart → Merid)) 2 (phaseμ (2 * ε * c)) :=
    ⟨(measurable_liftFun ε⁻¹ c hbm).aestronglyMeasurable, by
      rw [hP, eLpNorm_liftFun hR hc rfl hbm]
      exact hlp.2⟩
  rw [wda_phaseμ_eq] at hl
  have hl' : MemLp (liftFun ε⁻¹ c (b : Chart → Merid)) 2
      (volume.restrict (phaseCell (2 * ε * c))) := by
    have := hl.smul_measure (c := ENNReal.ofReal (2 * ε * c)) ENNReal.ofReal_ne_top
    rwa [smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top, one_smul] at this
  have hg := hl'.const_smul (√Real.pi * ε⁻¹)
  have hmeasv : Measurable (velPhys ε⁻¹ c (b : Chart → Merid)) := by
    rw [wda_velPhys_eq _ _ hR.ne']
    have hh : Measurable fun x => (√Real.pi * ε⁻¹) • liftFun ε⁻¹ c (b : Chart → Merid) x :=
      (measurable_liftFun ε⁻¹ c hbm).const_smul (√Real.pi * ε⁻¹)
    exact realC_continuous_B.measurable.comp hh
  refine hg.mono hmeasv.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [wda_velPhys_eq _ _ hR.ne', wda_norm_realC]
  simp

/-- Additivity of the pairing of a phase test against the lift of an `Lp` sum. -/
theorem wda_pair_add {c γ ν ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (b b' : VelG c γ ν)
    {H : ℝ × Space → CVec3} (hH : IsPhaseTest (2 * ε * c) H) :
    pairF (2 * ε * c) H (velPhys ε⁻¹ c ((b + b' : VelG c γ ν) : Chart → Merid)) =
      pairF (2 * ε * c) H (velPhys ε⁻¹ c (b : Chart → Merid)) +
        pairF (2 * ε * c) H (velPhys ε⁻¹ c (b' : Chart → Merid)) := by
  haveI : Fact (0 < 2 * ε * c) := ⟨by positivity⟩
  have hI : ∀ d : VelG c γ ν, Integrable (fun x => dotL (H x) (velPhys ε⁻¹ c (d : Chart → Merid) x))
      (volume.restrict (phaseCell (2 * ε * c))) := fun d =>
    wda_integrable_dotL hH.smooth.continuous hH.bounded_support (wda_memLp_velPhys hc hν hε d)
  have hae := wda_velPhys_add_ae (γ := γ) (ν := ν) hc hε b b'
  have hFG : Integrable (fun x => dotL (H x) (velPhys ε⁻¹ c (b : Chart → Merid) x +
      velPhys ε⁻¹ c (b' : Chart → Merid) x)) (volume.restrict (phaseCell (2 * ε * c))) :=
    ((hI b).add (hI b')).congr (Eventually.of_forall fun x => by simp [dotL_apply, mul_add, Finset.sum_add_distrib])
  have h1 := pairF_add_right_of_integrable (P := 2 * ε * c) (hI b) (hI b') hFG
  rw [← h1]
  rw [pairF_eq_restrictedProductIntegral (hI (b + b')), pairF_eq_restrictedProductIntegral hFG]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem weakDmuAdd {c γ ν ε μ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) :
    WeakDmuAdd c γ ν ε μ := by
  intro b b' rhs rhs' h1 h2
  refine ⟨fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · rw [wda_pair_add hc hν hε b b' hφ.gradT, h1.solenoidal φ hφ, h2.solenoidal φ hφ, add_zero]
  · have hT : IsPhaseTest (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul (μ : ℂ))
    rw [wda_pair_add hc hν hε b b' hT, h1.equation Φ hΦ, h2.equation Φ hΦ]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
