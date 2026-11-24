import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16

/-!


`(e^{tB} Φ)(τ, y) = e^{-3t/4} Φ(τ + t, e^{-t/2} y)` (source 1548-1552) sends the test element of a
phase test `Φ` to the test element of the phase test `dilT t Φ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F16b

open UnforcedLeray.PhaseSpace UnforcedLeray.FreeStress

/-- `(dilT t Φ)(τ, y) = e^{-3t/4} Φ(τ + t, e^{-t/2} y)`. -/
def dilT (t : ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => (Real.exp (-(3 / 4) * t) : ℂ) • Φ (p.1 + t, Real.exp (-(t / 2)) • p.2)

theorem isPhaseTest_dilT {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    IsPhaseTest P (dilT t Φ) where
  smooth := by
    have h : ContDiff ℝ ∞ (fun p : ℝ × Space => (p.1 + t, Real.exp (-(t / 2)) • p.2)) := by
      fun_prop
    exact (hΦ.smooth.comp h).const_smul _
  periodic τ y := by
    simp only [dilT]
    rw [show τ + P + t = (τ + t) + P by ring, hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    refine ⟨R * Real.exp (t / 2), fun τ y hy => ?_⟩
    simp only [dilT]
    rw [hR _ _ ?_, smul_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc R = R * Real.exp (t / 2) * Real.exp (-(t / 2)) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ < ‖y‖ * Real.exp (-(t / 2)) := mul_lt_mul_of_pos_right hy (Real.exp_pos _)
      _ = Real.exp (-(t / 2)) * ‖y‖ := mul_comm _ _

variable (P : ℝ) [Fact (0 < P)]

/-- The descent of a function of `(τ, y) ∈ ℝ × ℝ³` to the phase circle (via the representative). -/
def desc (Φ : ℝ × Space → CVec3) : AddCircle P × Space → CVec3 :=
  fun q => Φ (phaseRep P q.1, q.2)

variable {P}

theorem desc_coe {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (s : ℝ) (y : Space) :
    desc P Φ ((s : AddCircle P), y) = Φ (s, y) := by
  simp only [desc]
  have h1 : ((phaseRep P (s : AddCircle P) : ℝ) : AddCircle P) = (s : AddCircle P) :=
    coe_phaseRep P _
  have h2 : (((s - phaseRep P (s : AddCircle P) : ℝ)) : AddCircle P) = 0 := by
    rw [AddCircle.coe_sub, h1, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).1 h2
  have hp : Function.Periodic (fun τ : ℝ => Φ (τ, y)) P := fun τ => hΦ.periodic τ y
  have : phaseRep P (s : AddCircle P) = s - n • P := by rw [hn]; ring
  rw [this]
  exact hp.sub_zsmul_eq n

theorem prodSymm_testElem_ae {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    (prodLpEquiv.symm (testElem P 2 Φ) : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
      desc P Φ := by
  have hs := hΦ.isSliceTest 2
  have hmeas : AEStronglyMeasurable (desc P Φ) (phaseVol P) := by
    have h1 : Continuous (fun q : ℝ × Space => Φ q) := hΦ.continuous
    have h2 : Measurable (fun q : AddCircle P × Space => (phaseRep P q.1, q.2)) :=
      ((measurable_phaseRep P).comp measurable_fst).prodMk measurable_snd
    exact (h1.measurable.comp h2).aestronglyMeasurable
  rw [ae_eq_prod_iff (Lp.aestronglyMeasurable _) hmeas]
  have e1 := prodLpEquiv_symm_ae (ν := AddCircle.haarAddCircle (T := P)) (testElem P 2 Φ)
  have e2 : ⇑(testElem P 2 Φ) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hs) := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space)) (p := 2)
      (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  filter_upwards [e1, e2] with τ h1 h2
  have h3 : circleSlice hs τ = sliceMap hs.2 (phaseRep P τ) := by
    conv_lhs => rw [← coe_phaseRep P τ]
    exact circleSlice_coe hs _
  refine h1.trans ?_
  rw [h2, h3]
  exact MemLp.coeFn_toLp _

theorem qmp_dilation (t : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun q : AddCircle P × Space => (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2))
      (phaseVol P) (phaseVol P) := by
  have hA : Measure.QuasiMeasurePreserving (fun τ : AddCircle P => τ + (t : AddCircle P))
      (AddCircle.haarAddCircle (T := P)) AddCircle.haarAddCircle :=
    (measurePreserving_add_right _ _).quasiMeasurePreserving
  have hB : Measure.QuasiMeasurePreserving (fun y : Space => Real.exp (-(t / 2)) • y)
      (volume : Measure Space) volume :=
    Measure.quasiMeasurePreserving_smul (volume : Measure Space) (Real.exp_pos _).ne'
  exact MeasureTheory.QuasiMeasurePreserving.prodMap hA hB

/-- **The group on tests**: `e^{tB} (testElem Φ) = testElem (dilT t Φ)`. -/
theorem phaseDilation_testElem {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    phaseDilation P t (testElem P 2 Φ) = testElem P 2 (dilT t Φ) := by
  apply prodLpEquiv.symm.injective
  apply Lp.ext
  have hΨ := isPhaseTest_dilT hΦ t
  have e1 := phaseDilation_ae P t (testElem P 2 Φ)
  have e2 := prodSymm_testElem_ae hΦ
  have e3 := prodSymm_testElem_ae hΨ
  have e4 := (qmp_dilation (P := P) t).ae_eq_comp e2
  filter_upwards [e1, e4, e3] with q h1 h4 h3
  rw [h1, h3]
  have h4' : (prodLpEquiv.symm (testElem P 2 Φ) : AddCircle P × Space → CVec3)
      (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2) =
      desc P Φ (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2) := h4
  rw [h4']
  have hq : q.1 + (t : AddCircle P) = ((phaseRep P q.1 + t : ℝ) : AddCircle P) := by
    rw [AddCircle.coe_add, coe_phaseRep]
  rw [hq, desc_coe hΦ]
  rfl

end UnforcedLeray.Short.PartIIa.F16b
