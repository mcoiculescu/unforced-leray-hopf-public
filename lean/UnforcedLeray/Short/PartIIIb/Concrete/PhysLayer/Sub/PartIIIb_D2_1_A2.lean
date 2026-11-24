import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_1

/-!
# `fwuSubInt`: integrability of the pairings of the lift with the test fields (source 2666-2700)

For `b : VelG`, the lift `velPhys ε⁻¹ c b` is `L²` on the phase cell: the body measure has a density
`π g⁻²` bounded below by a positive constant, so `b ∈ L²(ageμ c (-3/2))` and `memLp_liftFun`-type
bounds apply. Both test fields are phase tests (`gradT φ`, and `L0T ν Φ + μ Φ` by
`isPhaseTest_L0T`), hence continuous with bounded spatial support, and the pairing is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_eq_restrictedProductIntegral)

theorem fwuB_realC_norm (x : Space) : ‖B0412.realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [B0412.realC_apply, Complex.norm_real]

theorem fwuB_velPhys_eq (R c : ℝ) (hR : R ≠ 0) (b : Chart → Merid) (x : ℝ × Space) :
    velPhys R c b x = B0412.realC ((Real.sqrt Real.pi * R) • liftFun R c b x) := by
  have h : (Real.sqrt Real.pi * R) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 Real.pi_pos).ne' hR
  simp only [velPhys, liftFun, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem fwuB_norm_velPhys {R c : ℝ} (hR : 0 < R) (b : Chart → Merid) (x : ℝ × Space) :
    ‖velPhys R c b x‖ = Real.sqrt Real.pi * R * ‖liftFun R c b x‖ := by
  rw [fwuB_velPhys_eq R c hR.ne' b x, fwuB_realC_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos) hR)]

theorem fwuB_measurable_velPhys (R c : ℝ) {b : Chart → Merid} (hb : Measurable b) :
    Measurable (velPhys R c b) := by
  have hc : Continuous (B0412.realC : Space → CVec3) := by
    unfold B0412.realC
    exact continuous_finsetSum _ fun i _ =>
      (Complex.continuous_ofReal.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).smul
        continuous_const
  exact hc.measurable.comp (measurable_Nv R (measurable_perExt c hb))

/-- The body measure density `π g⁻²` is bounded below, so `L²(bodyMeasure)` embeds in
`L²(ageμ c (-3/2))`. -/
theorem fwuB_memLp_ageμ {c γ ν : ℝ} (hν : 0 < ν) (f : Chart → Merid)
    (hf : MemLp f 2 (bodyMeasure c γ ν)) : MemLp f 2 (ageμ c (-3 / 2)) := by
  set e : ℝ := Real.exp (-(|γ| / ν)) with he
  have he0 : 0 < e := Real.exp_pos _
  set δ : ℝ≥0∞ := ENNReal.ofReal (Real.pi * e ^ 2) with hδdef
  have hδ0 : δ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hδtop : δ ≠ ∞ := ENNReal.ofReal_ne_top
  have hlow : δ • ageμ c (-3 / 2) ≤ bodyMeasure c γ ν := by
    unfold bodyMeasure
    rw [← withDensity_const]
    refine withDensity_mono ?_
    filter_upwards with p
    refine ENNReal.ofReal_le_ofReal ?_
    have hg : |NearInst.gainFun γ ν p| ≤ Real.exp (|γ| / ν) := NearInst.gainFun_le hν p
    have hpos : 0 < NearInst.gainFun γ ν p := NearInst.gainFun_pos γ ν p
    have hgle : NearInst.gainFun γ ν p ≤ Real.exp (|γ| / ν) := by
      rwa [abs_of_pos hpos] at hg
    have hinv : e ≤ ginv γ ν p := by
      have h1 : (Real.exp (|γ| / ν))⁻¹ ≤ (NearInst.gainFun γ ν p)⁻¹ :=
        inv_anti₀ hpos hgle
      have h2 : ginv γ ν p = (NearInst.gainFun γ ν p)⁻¹ := rfl
      rw [h2, he, Real.exp_neg]
      exact h1
    have hsq : e ^ 2 ≤ ginv γ ν p ^ 2 := pow_le_pow_left₀ he0.le hinv 2
    exact mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
  have hle : ageμ c (-3 / 2) ≤ δ⁻¹ • bodyMeasure c γ ν := by
    rw [Measure.le_iff]
    intro s hs
    have h1 := Measure.le_iff.1 hlow s hs
    rw [Measure.smul_apply, smul_eq_mul] at h1
    rw [Measure.smul_apply, smul_eq_mul]
    calc ageμ c (-3 / 2) s = δ⁻¹ * (δ * ageμ c (-3 / 2) s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδtop, one_mul]
      _ ≤ δ⁻¹ * bodyMeasure c γ ν s := by gcongr
  exact MemLp.of_measure_le_smul (ENNReal.inv_ne_top.2 hδ0) hle hf

theorem fwuB_memLp_liftFun {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {f : Chart → Merid} (hfm : Measurable f) (hf : MemLp f 2 (ageμ c (-3 / 2))) :
    MemLp (liftFun R c f) 2 (phaseμ P) :=
  ⟨(measurable_liftFun R c hfm).aestronglyMeasurable, by
    rw [eLpNorm_liftFun hR hc hP hfm]
    exact hf.eLpNorm_lt_top⟩

theorem fwuB_memLp_velPhys {R c P : ℝ} (hR : 0 < R)
    {f : Chart → Merid} (hfm : Measurable f) (hlift : MemLp (liftFun R c f) 2 (phaseμ P)) :
    MemLp (velPhys R c f) 2 (phaseμ P) := by
  have hg : MemLp (fun x => Real.sqrt Real.pi * R * ‖liftFun R c f x‖) 2 (phaseμ P) :=
    hlift.norm.const_mul (Real.sqrt Real.pi * R)
  refine MemLp.of_le hg (fwuB_measurable_velPhys R c hfm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [fwuB_norm_velPhys hR f x, Real.norm_of_nonneg (by positivity)]

theorem fwuB_phaseμ_eq (P : ℝ) :
    phaseμ P = (ENNReal.ofReal P)⁻¹ • (volume : Measure (ℝ × Space)).restrict (phaseCell P) := by
  unfold phaseμ
  rw [Measure.prod_smul_left]
  congr 1
  have := Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)
  simpa [phaseCell, Measure.volume_eq_prod] using this

/-- A continuous test with bounded spatial support pairs integrably with an `L²` field on the
phase cell. -/
theorem fwuB_integrable_dotL {P : ℝ} [Fact (0 < P)] {H w : ℝ × Space → CVec3}
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
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hH.continuousOn
  obtain ⟨C, hC'0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖H x‖ ≤ C :=
    ⟨max C0 0, le_max_right _ _, fun x hx => (hC0 x hx).trans (le_max_left _ _)⟩
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
      push_neg at hcon
      exact hxK ⟨⟨hx.1.1.le, hx.1.2⟩, by simpa using hcon⟩
    rw [hx0, map_zero, ContinuousLinearMap.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)) hC'0)
      (norm_nonneg _)

theorem fwuSubInt (c γ ν ε μ : ℝ) : FWUSubInt c γ ν ε μ := by
  intro hc hν hε b H hH
  have hP0 : 0 < 2 * ε * c := by positivity
  have : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  -- the test field is a phase test, hence continuous with bounded spatial support
  have hHp : IsPhaseTest (2 * ε * c) H := by
    rcases hH with ⟨φ, hφ, rfl⟩ | ⟨Φ, hΦ, rfl⟩
    · exact hφ.gradT
    · exact (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul (μ : ℂ))
  -- the lift of `b` is `L²` on the phase cell
  have hbm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hfa : MemLp (b : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    fwuB_memLp_ageμ hν _ (Lp.memLp b)
  have hlift := fwuB_memLp_liftFun hR hc hP hbm hfa
  have hvel := fwuB_memLp_velPhys hR hbm hlift
  have hμeq : (volume : Measure (ℝ × Space)).restrict (phaseCell (2 * ε * c)) =
      ENNReal.ofReal (2 * ε * c) • phaseμ (2 * ε * c) := by
    rw [fwuB_phaseμ_eq, smul_smul, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_pos.2 hP0).ne' ENNReal.ofReal_ne_top, one_smul]
  have hw : MemLp (velPhys ε⁻¹ c (b : Chart → Merid)) 2
      (volume.restrict (phaseCell (2 * ε * c))) := by
    rw [hμeq]
    exact hvel.smul_measure ENNReal.ofReal_ne_top
  obtain ⟨R0, hR0⟩ := hHp.bounded_support
  exact fwuB_integrable_dotL hHp.continuous ⟨R0, hR0⟩ hw

end UnforcedLeray.Short.PartIIIb.Concrete
