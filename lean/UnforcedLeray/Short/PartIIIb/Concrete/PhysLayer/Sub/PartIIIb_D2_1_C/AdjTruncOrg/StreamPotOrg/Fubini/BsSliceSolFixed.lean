import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import UnforcedLeray.Cons.L2.BackgroundConcrete.PeriodizedCellPair
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fixed spatial test: a.e. slice orthogonal to `∇χ`

Source `the November 2 reference manuscript` lines 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt gradT_perT_eq_self_on_Ioo)

/-- The phase gradient of a product test `η(t) χ(y)`. -/
theorem bsGradT_prod (η : ℝ → ℝ) (χ : Space → ℂ) (hη : ContDiff ℝ ∞ η) (hχ : ContDiff ℝ ∞ χ)
    (t : ℝ) (y : Space) :
    PhaseSpace.gradT (fun p : ℝ × Space => ((η p.1 : ℝ) : ℂ) * χ p.2) (t, y)
      = ((η t : ℝ) : ℂ) • bsGradS χ y := by
  have hdη : DifferentiableAt ℝ η t := (hη.differentiable (by simp)) t
  have hdχ : DifferentiableAt ℝ χ y := (hχ.differentiable (by simp)) y
  have hA : HasFDerivAt (fun p : ℝ × Space => ((η p.1 : ℝ) : ℂ))
      ((Complex.ofRealCLM.comp (fderiv ℝ η t)).comp (ContinuousLinearMap.fst ℝ ℝ Space)) (t, y) := by
    have h1 : HasFDerivAt (fun s : ℝ => ((η s : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ η t)) t :=
      Complex.ofRealCLM.hasFDerivAt.comp t hdη.hasFDerivAt
    exact h1.comp (t, y) (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × Space → ℝ) (ContinuousLinearMap.fst ℝ ℝ Space) (t, y))
  have hB : HasFDerivAt (fun p : ℝ × Space => χ p.2)
      ((fderiv ℝ χ y).comp (ContinuousLinearMap.snd ℝ ℝ Space)) (t, y) :=
    hdχ.hasFDerivAt.comp (t, y) (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × Space → Space) (ContinuousLinearMap.snd ℝ ℝ Space) (t, y))
  have hM := hA.mul hB
  have hGeq : (fun p : ℝ × Space => ((η p.1 : ℝ) : ℂ) * χ p.2)
      = (fun p : ℝ × Space => ((η p.1 : ℝ) : ℂ)) * (fun p : ℝ × Space => χ p.2) := rfl
  have hcv : ∀ x : Fin 3, (coordinateVector x : Space) = EuclideanSpace.single x (1 : ℝ) := fun x => rfl
  unfold PhaseSpace.gradT bsGradS PhaseSpace.dy
  apply PiLp.ext
  intro i
  rw [hGeq]
  simp only [hM.fderiv, hcv]
  simp [Finset.sum_apply, Pi.single_apply]

/-- The slice pairing `t ↦ ∫ ∇χ · Φ(t,y) dy` is integrable on one period. -/
theorem bsSlice_integrable (P : ℝ) (hP : 0 < P) (Φ : ℝ × Space → CVec3)
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) (χ : Space → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    Integrable (fun t : ℝ => ∫ y : Space, dotL (bsGradS χ y) (Φ (t, y)))
      (volume.restrict (Ioc 0 P)) := by
  have hK : IsCompact (tsupport χ) := hχc
  set F : ℝ × Space → ℂ := fun p => dotL (bsGradS χ p.2) (Φ p) with hF
  set S : Set (ℝ × Space) := Ioc 0 P ×ˢ tsupport χ with hS
  set T : Set (ℝ × Space) := Ioc 0 P ×ˢ (univ : Set Space) with hT
  have hSmeas : MeasurableSet S := measurableSet_Ioc.prod hK.isClosed.measurableSet
  have hTmeas : MeasurableSet T := measurableSet_Ioc.prod MeasurableSet.univ
  have hST : S ⊆ T := prod_mono (subset_refl _) (subset_univ _)
  have hfm : AEMeasurable (fun p : ℝ × Space => ‖Φ p‖ₑ ^ (2 : ℝ)) volume :=
    ((hΦ.meas.aemeasurable).enorm).pow_const (2 : ℝ)
  have hprod : (volume.restrict (Ioc 0 P)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict T := by
    rw [Measure.volume_eq_prod, hT, ← Measure.prod_restrict, Measure.restrict_univ]
  have hI0 : ∫⁻ t in Ioc 0 P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    intro htop
    apply hΦ.finite.ne
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne',
      ENNReal.top_rpow_of_pos (by norm_num)]
  have hI : ∫⁻ p in T, ‖Φ p‖ₑ ^ (2 : ℝ) ∂(volume : Measure (ℝ × Space)) ≠ ⊤ := by
    have : ∫⁻ p, ‖Φ p‖ₑ ^ (2 : ℝ) ∂((volume.restrict (Ioc 0 P)).prod (volume : Measure Space))
        = ∫⁻ t in Ioc 0 P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_prod]
      rw [hprod]
      exact hfm.restrict
    rw [hprod] at this
    rw [this]
    exact hI0
  have hfin : IsFiniteMeasure ((volume : Measure (ℝ × Space)).restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, hS, Measure.prod_prod]
    exact ENNReal.mul_lt_top (by simp) hK.measure_lt_top
  have hmemΦ : MemLp Φ 2 ((volume : Measure (ℝ × Space)).restrict S) := by
    refine ⟨hΦ.meas.mono_measure Measure.restrict_le_self, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact lt_of_le_of_lt (lintegral_mono_set hST) (lt_top_iff_ne_top.2 hI)
  have hintΦ : Integrable Φ ((volume : Measure (ℝ × Space)).restrict S) :=
    hmemΦ.integrable (by norm_num)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (bsGradS_continuous hχ).continuousOn
  have hFmeas : AEStronglyMeasurable F ((volume : Measure (ℝ × Space)).restrict S) := by
    have ha : Continuous (fun p : ℝ × Space => bsGradS χ p.2) :=
      (bsGradS_continuous hχ).comp continuous_snd
    have hΦm : AEStronglyMeasurable Φ ((volume : Measure (ℝ × Space)).restrict S) :=
      hΦ.meas.mono_measure Measure.restrict_le_self
    exact (ContinuousLinearMap.continuous₂ (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)).comp_aestronglyMeasurable₂
      ha.aestronglyMeasurable hΦm
  have hFS : Integrable F ((volume : Measure (ℝ × Space)).restrict S) := by
    refine Integrable.mono' (hintΦ.norm.const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * M)) hFmeas ?_
    filter_upwards [ae_restrict_mem hSmeas] with p hp
    have h1 := bsDotL_bound (bsGradS χ p.2) (Φ p)
    have h2 := hM p.2 hp.2
    have h3 : 0 ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ := ContinuousLinearMap.opNorm_nonneg _
    calc ‖F p‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖bsGradS χ p.2‖ * ‖Φ p‖ := h1
      _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * M * ‖Φ p‖ := by
          gcongr
  have hFT : IntegrableOn F T volume := by
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := S) hFS hTmeas ?_
    intro p hp
    have hp2 : p.2 ∉ tsupport χ := fun h => hp.2 ⟨hp.1.1, h⟩
    have hev : χ =ᶠ[𝓝 p.2] fun _ => (0 : ℂ) := by
      exact notMem_tsupport_iff_eventuallyEq.1 hp2
    simp [hF, bsGradS_eq_zero_of_eventually hev]
  have hFint : Integrable F ((volume.restrict (Ioc 0 P)).prod (volume : Measure Space)) := by
    rw [hprod]; exact hFT
  exact hFint.integral_prod_left

/-- Testing weak solenoidality with the product test `η(t) χ(y)`, `supp η ⊂ (0,P)`. -/
theorem bsSlice_test (P : ℝ) (hP : 0 < P) (Φ : ℝ × Space → CVec3)
    (hsol : IsWeakSolenoidal P Φ) (χ : Space → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ioo 0 P) :
    ∫ t : ℝ, η t • (∫ y : Space, dotL (bsGradS χ y) (Φ (t, y))) = 0 := by
  by_cases hne : (tsupport η).Nonempty
  swap
  · have h0 : tsupport η = ∅ := not_nonempty_iff_eq_empty.1 hne
    have : η = 0 := by
      funext t
      by_contra h
      exact (Set.eq_empty_iff_forall_notMem.1 h0) t (subset_tsupport η (by simpa using h))
    subst this
    simp
  have hK : IsCompact (tsupport η) := hηc
  obtain ⟨A, hA, hAmin⟩ := hK.exists_isMinOn hne continuousOn_id
  obtain ⟨B, hB, hBmax⟩ := hK.exists_isMaxOn hne continuousOn_id
  have hA0 : 0 < A := (hηs hA).1
  have hBP : B < P := (hηs hB).2
  set G : ℝ × Space → ℂ := fun p => ((η p.1 : ℝ) : ℂ) * χ p.2 with hG
  have hηout : ∀ τ : ℝ, τ ∉ Icc A B → η τ = 0 := by
    intro τ hτ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hτ ⟨hAmin hmem, hBmax hmem⟩
  have hTS : TimeSupp A B G := by
    intro τ y hτ
    simp [hG, hηout τ hτ]
  have hG0 : IsPhaseTest 0 G := by
    refine ⟨?_, ?_, ?_⟩
    · exact (Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_fst)).mul (hχ.comp contDiff_snd)
    · intro τ y; simp
    · obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.exists_norm_le
      refine ⟨R, fun τ y hy => ?_⟩
      have : y ∉ tsupport χ := fun h => by have := hR y h; linarith
      have hev : χ y = 0 := image_eq_zero_of_notMem_tsupport this
      simp [hG, hev]
  have hz := hsol (perT P G) (isPhaseTest_perT hP hTS hG0)
  unfold pairF phaseInt at hz
  have hz2 : ∫ t in Ioc (0 : ℝ) P, ∫ y : Space,
      dotL (PhaseSpace.gradT (perT P G) (t, y)) (Φ (t, y)) = 0 := by
    rcases smul_eq_zero.1 hz with h | h
    · exact absurd h (inv_ne_zero hP.ne')
    · exact h
  have hIoo : ∫ t in Ioc (0 : ℝ) P, ∫ y : Space,
      dotL (PhaseSpace.gradT (perT P G) (t, y)) (Φ (t, y))
      = ∫ t in Ioo (0 : ℝ) P, ∫ y : Space,
      dotL (PhaseSpace.gradT (perT P G) (t, y)) (Φ (t, y)) :=
    (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
  have hfun : ∀ t ∈ Ioo (0 : ℝ) P, (∫ y : Space,
      dotL (PhaseSpace.gradT (perT P G) (t, y)) (Φ (t, y)))
      = ((η t : ℝ) : ℂ) * ∫ y : Space, dotL (bsGradS χ y) (Φ (t, y)) := by
    intro t ht
    have : ∀ y : Space, dotL (PhaseSpace.gradT (perT P G) (t, y)) (Φ (t, y))
        = ((η t : ℝ) : ℂ) * dotL (bsGradS χ y) (Φ (t, y)) := by
      intro y
      rw [gradT_perT_eq_self_on_Ioo hP hA0 hBP hTS ht.1 ht.2 y, hG, bsGradT_prod η χ hη hχ t y]
      simp
    simp_rw [this]
    exact integral_const_mul _ _
  rw [hIoo, setIntegral_congr_fun measurableSet_Ioo hfun] at hz2
  have hout : ∀ x ∉ Ioo (0 : ℝ) P, ((η x : ℝ) : ℂ) * ∫ y : Space, dotL (bsGradS χ y) (Φ (x, y)) = 0 := by
    intro x hx
    have : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h))
    simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hz2
  simpa [Complex.real_smul] using hz2

/-- Fixed spatial test: a weakly solenoidal `Φ ∈ Y_2` has a.e. slice orthogonal to `∇χ`. -/
theorem bsSliceSolFixed : BSSliceSolFixed := by
  intro P hP Φ hΦ hsol χ hχ hχc
  set g : ℝ → ℂ := fun t => ∫ y : Space, dotL (bsGradS χ y) (Φ (t, y)) with hg
  have hint : IntegrableOn g (Ioc 0 P) := bsSlice_integrable P hP Φ hΦ χ hχ hχc
  have hfund : ∀ᵐ t : ℝ, t ∈ Ioo 0 P → g t = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo
      (IntegrableOn.locallyIntegrableOn (hint.mono_set Ioo_subset_Ioc_self)) ?_
    intro η hη hηc hηs
    exact bsSlice_test P hP Φ hsol χ hχ hχc η hη hηc hηs
  have hneP : ∀ᵐ t : ℝ, t ≠ P := by
    rw [ae_iff]; simp
  have hone : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), g t = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hfund, hneP] with t h1 h2 ht
    exact h1 ⟨ht.1, lt_of_le_of_ne ht.2 h2⟩
  have hpp : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      Φ (z.1 + P, z.2) = Φ z := hΦ.periodic
  have hper : ∀ᵐ t : ℝ, g (t + P) = g t := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpp] with t ht
    exact integral_congr_ae (ht.mono fun y hy => by dsimp only; rw [hy])
  set H : ℝ → ℝ≥0∞ := fun t => if ‖g t‖ₑ = 0 then 0 else ⊤ with hH
  have hHper : ∀ᵐ t : ℝ, H (t + P) = H t := hper.mono fun t h => by simp [hH, h]
  have hHfin : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), H t < ⊤ :=
    hone.mono fun t h => by simp [hH, h]
  have hall := bsSliceL2_aeFin hP (bsSliceL2_aeShift hHper) hHfin
  filter_upwards [hall] with t ht
  by_contra hne
  have hg0 : g t ≠ 0 := hne
  simp [hH, hg0] at ht

end UnforcedLeray.Short.PartIIIb.Concrete
