import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Unfold
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.IBP
import UnforcedLeray.Lib.BochnerTime.Basic
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_2

/-!
# The projected equation along comoving rays, tested against spatial solenoidal fields
(helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 ("The projected equation is $A_0U+\mathbb P(U\cdot\nabla U)=0$").

* `pairF_driftT_eq_of_weak`: the compact-solenoidal weak equation
  `⟪L₀ᵗΦ, U⟫ = ⟪(U·∇)Φ, U⟫` becomes `⟪T₀ᵗΦ, U⟫ = ⟪Φ, N⟫`, `N = νΔU + ½U - 𝔓(U·∇U)`, on every
  solenoidal phase test (spatial integration by parts slice by slice; the Leray projection drops out
  against solenoidal tests).
* `comoving_sub_eq_integral`: for every compactly supported smooth spatial solenoidal `Ψ`,
  `f(s) = ∫ Ψ(x)·U(s, e^{-s/2}x) dx` satisfies `f(s₂) - f(s₁) = ∫_{s₁}^{s₂} ∫ Ψ(x)·N(r, e^{-r/2}x)`:
  test the drift form with the periodized chart lift of `φ ⊗ Ψ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.BochnerTime UnforcedLeray.RieszLp
  BaseRepIBP

/-! ## 1. Linear algebra of slice integrals -/

theorem continuous_realC : Continuous realC := by
  have h : (realC : Space → CVec3) = ⇑ofReV := funext PointwiseDerivSub.realC_eq_ofReV
  rw [h]
  exact ofReV.continuous

theorem realC_add' (a b : Space) : realC (a + b) = realC a + realC b := by
  simp only [PointwiseDerivSub.realC_eq_ofReV, map_add]

theorem realC_sub' (a b : Space) : realC (a - b) = realC a - realC b := by
  simp only [PointwiseDerivSub.realC_eq_ofReV, map_sub]

theorem realC_smul' (c : ℝ) (a : Space) : realC (c • a) = (c : ℂ) • realC a := by
  simp only [PointwiseDerivSub.realC_eq_ofReV, map_smul]
  rw [Complex.coe_smul]

/-- The slice pairing `∫ Φ(t, y) · F(y) dy`. -/
def sI (Φ : ℝ × Space → CVec3) (t : ℝ) (F : SpatialField) : ℂ :=
  ∫ y, dotL (Φ (t, y)) (realC (F y))

variable {P : ℝ}

theorem sI_add {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) {F G : SpatialField}
    (hF : Continuous F) (hG : Continuous G) : sI Φ t (F + G) = sI Φ t F + sI Φ t G := by
  unfold sI
  simp only [Pi.add_apply, realC_add', map_add]
  exact integral_add (integrable_slice_dotL_realC hΦ t hF) (integrable_slice_dotL_realC hΦ t hG)

theorem sI_sub {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) {F G : SpatialField}
    (hF : Continuous F) (hG : Continuous G) : sI Φ t (F - G) = sI Φ t F - sI Φ t G := by
  unfold sI
  simp only [Pi.sub_apply, realC_sub', map_sub]
  exact integral_sub (integrable_slice_dotL_realC hΦ t hF) (integrable_slice_dotL_realC hΦ t hG)

theorem sI_smul (Φ : ℝ × Space → CVec3) (t : ℝ) (c : ℝ) (F : SpatialField) :
    sI Φ t (c • F) = (c : ℂ) * sI Φ t F := by
  unfold sI
  simp only [Pi.smul_apply, realC_smul', map_smul, smul_eq_mul]
  exact integral_const_mul _ _

theorem sI_add_left {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (hΨ : IsPhaseTest P Ψ)
    (t : ℝ) {F : SpatialField} (hF : Continuous F) :
    sI (fun p => Φ p + Ψ p) t F = sI Φ t F + sI Ψ t F := by
  unfold sI
  simp only [map_add, ContinuousLinearMap.add_apply]
  exact integral_add (integrable_slice_dotL_realC hΦ t hF) (integrable_slice_dotL_realC hΨ t hF)

theorem sI_smul_left (Φ : ℝ × Space → CVec3) (t : ℝ) (c : ℝ) (F : SpatialField) :
    sI (fun p => c • Φ p) t F = (c : ℂ) * sI Φ t F := by
  unfold sI
  simp only [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply,
    Complex.real_smul]
  exact integral_const_mul _ _

/-! ## 2. The slice identity in drift form -/

/-- **Slice identity.** `∫ T₀ᵗΦ·U - ∫ Φ·N = ∫ L₀ᵗΦ·U - ∫ (U·∇)Φ·U` on each slice. -/
theorem slice_drift_identity (ν : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest P Φ)
    {U : ℝ → SpatialField} (hU : IsUniformSmoothL4SliceFamily U)
    (hSol : ∀ τ, IsSolenoidal (U τ)) (t : ℝ) :
    sI (driftT Φ) t (U t) - sI Φ t (comovingEvolRHS ν U t) =
      sI (L0T ν Φ) t (U t) -
        ∫ y, dotL (advT (fun x => realC (U x.1 x.2)) Φ (t, y)) (realC (U t y)) := by
  have hUs : ∀ τ, ContDiff ℝ ∞ (U τ) := HigherPhaseSub.sliceFamily_contDiff_infty hU
  have hLer : IsUniformSmoothL4SliceFamily (smoothConvectiveLeray U U) :=
    HigherPhaseSub.sliceFamily_smoothConvectiveLeray smoothLeraySliceRegularity_proof _ _ hU hU
  have hLc : Continuous (smoothConvectiveLeray U U t) :=
    (HigherPhaseSub.sliceFamily_contDiff_infty hLer t).continuous
  have hLapc : Continuous (spatialLaplacian (U t)) :=
    (CoordDerivSub.contDiff_infty_spatialLaplacian (hUs t)).continuous
  have S3 := slice_integral_advT_eq_neg_spatialConvect hΦ.1 hUs hSol t
  have S4 := slice_integral_smoothConvectiveLeray_eq hΦ hU t
  have SL := slice_integral_lapT_eq hΦ.1 (hUs t) t
  have hL : sI (L0T ν Φ) t (U t) = sI (driftT Φ) t (U t) - (ν : ℂ) * sI (lapT Φ) t (U t) -
      ((1 / 2 : ℝ) : ℂ) * sI Φ t (U t) := by
    unfold sI
    have h : ∀ y, dotL (L0T ν Φ (t, y)) (realC (U t y)) =
        dotL (driftT Φ (t, y)) (realC (U t y)) - (ν : ℂ) * dotL (lapT Φ (t, y)) (realC (U t y)) -
          ((1 / 2 : ℝ) : ℂ) * dotL (Φ (t, y)) (realC (U t y)) := by
      intro y
      simp only [L0T, nuLapT, Pi.sub_apply, Pi.smul_apply, map_sub,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.map_smul_of_tower,
        ContinuousLinearMap.smul_apply, Complex.real_smul]
    simp_rw [h]
    have iA := integrable_slice_dotL_realC hΦ.1.driftT t (hUs t).continuous
    have iB := (integrable_slice_dotL_realC hΦ.1.lapT t (hUs t).continuous).const_mul (ν : ℂ)
    have iC := (integrable_slice_dotL_realC hΦ.1 t (hUs t).continuous).const_mul
      ((1 / 2 : ℝ) : ℂ)
    have iAB : Integrable (fun y : Space => dotL (driftT Φ (t, y)) (realC (U t y)) -
        (ν : ℂ) * dotL (lapT Φ (t, y)) (realC (U t y))) := iA.sub iB
    rw [integral_sub iAB iC, integral_sub iA iB, integral_const_mul, integral_const_mul]
  have P2 : sI Φ t (comovingEvolRHS ν U t) =
      (ν : ℂ) * sI Φ t (spatialLaplacian (U t)) + ((1 / 2 : ℝ) : ℂ) * sI Φ t (U t) -
        sI Φ t (smoothConvectiveLeray U U t) := by
    have e : comovingEvolRHS ν U t =
        (ν • spatialLaplacian (U t) + (1 / 2 : ℝ) • U t) - smoothConvectiveLeray U U t := rfl
    rw [e, sI_sub hΦ.1 t ((hLapc.const_smul ν).add ((hUs t).continuous.const_smul _)) hLc,
      sI_add hΦ.1 t (hLapc.const_smul ν) ((hUs t).continuous.const_smul _), sI_smul, sI_smul]
  rw [hL, P2, S3]
  unfold sI
  rw [SL, ← S4]
  ring

/-! ## 3. The drift form of the weak equation -/

variable [hP : Fact (0 < P)]

theorem integrableOn_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn f (Ioc (0 : ℝ) P) :=
  (hf.integrableOn_Icc (a := 0) (b := P)).mono_set Ioc_subset_Icc_self

theorem continuous_sI_slice {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {F : ℝ → SpatialField} (hFc : Continuous fun x : ℝ × Space => F x.1 x.2) :
    Continuous fun t => sI Φ t (F t) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  exact continuous_slice_dotL hΦ.smooth.continuous hR (continuous_realC.comp hFc)

/-- **Drift form.** On solenoidal phase tests, `⟪T₀ᵗΦ, U⟫ = ⟪Φ, νΔU + ½U - 𝔓(U·∇U)⟫`. -/
theorem pairF_driftT_eq_of_weak (ν : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest P Φ)
    {U : ℝ → SpatialField} (hU : IsUniformSmoothL4SliceFamily U)
    (hSol : ∀ τ, IsSolenoidal (U τ)) (hUc : Continuous fun x : ℝ × Space => U x.1 x.2)
    (hNc : Continuous fun x : ℝ × Space => comovingEvolRHS ν U x.1 x.2)
    (hCc : Continuous fun x : ℝ × Space => spatialConvect (U x.1) (U x.1) x.2)
    (hweak : pairF P (L0T ν Φ) (fun x => realC (U x.1 x.2)) =
      pairF P (advT (fun x => realC (U x.1 x.2)) Φ) (fun x => realC (U x.1 x.2))) :
    pairF P (driftT Φ) (fun x => realC (U x.1 x.2)) =
      pairF P Φ (fun x => realC (comovingEvolRHS ν U x.1 x.2)) := by
  have hUs : ∀ τ, ContDiff ℝ ∞ (U τ) := HigherPhaseSub.sliceFamily_contDiff_infty hU
  set sD : ℝ → ℂ := fun t => sI (driftT Φ) t (U t) with hsD
  set sN : ℝ → ℂ := fun t => sI Φ t (comovingEvolRHS ν U t) with hsN
  set sL : ℝ → ℂ := fun t => sI (L0T ν Φ) t (U t) with hsL
  set sA : ℝ → ℂ := fun t =>
    ∫ y, dotL (advT (fun x => realC (U x.1 x.2)) Φ (t, y)) (realC (U t y)) with hsA
  have hsA' : sA = fun t => -sI Φ t (spatialConvect (U t) (U t)) := by
    funext t
    exact slice_integral_advT_eq_neg_spatialConvect hΦ.1 hUs hSol t
  have cD : Continuous sD := continuous_sI_slice hΦ.1.driftT hUc
  have cN : Continuous sN := continuous_sI_slice hΦ.1 hNc
  have cL : Continuous sL := continuous_sI_slice (isPhaseTest_L0T hΦ.1 ν) hUc
  have cA : Continuous sA := by
    rw [hsA']
    exact (continuous_sI_slice hΦ.1 hCc).neg
  have hw : ∫ t in Ioc (0 : ℝ) P, sL t = ∫ t in Ioc (0 : ℝ) P, sA t := by
    have h := hweak
    unfold pairF phaseInt at h
    have hP0 : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero hP.out.ne'
    exact smul_right_injective ℂ hP0 h
  have hid : ∀ t, sD t - sN t = sL t - sA t := fun t =>
    slice_drift_identity ν hΦ hU hSol t
  unfold pairF phaseInt
  congr 1
  change ∫ t in Ioc (0 : ℝ) P, sD t = ∫ t in Ioc (0 : ℝ) P, sN t
  have h1 : ∫ t in Ioc (0 : ℝ) P, (sD t - sN t) = ∫ t in Ioc (0 : ℝ) P, (sL t - sA t) :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ => hid t
  rw [integral_sub (integrableOn_Ioc_of_continuous cD) (integrableOn_Ioc_of_continuous cN),
    integral_sub (integrableOn_Ioc_of_continuous cL) (integrableOn_Ioc_of_continuous cA), hw,
    sub_self] at h1
  exact sub_eq_zero.1 h1

/-! ## 4. Periodization commutes with the spatial derivatives -/

theorem timeSupp_dy {A B : ℝ} {G : ℝ × Space → CVec3} (hG : TimeSupp A B G) (j : Fin 3) :
    TimeSupp A B (dy j G) := by
  intro τ y hτ
  have hev : G =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    have hopen : IsOpen {p : ℝ × Space | p.1 ∉ Icc A B} :=
      isClosed_Icc.isOpen_compl.preimage continuous_fst
    filter_upwards [hopen.mem_nhds (show ((τ, y) : ℝ × Space) ∈ {p : ℝ × Space | p.1 ∉ Icc A B}
      from hτ)] with p hp
    exact hG p.1 p.2 hp
  simp [dy, hev.fderiv_eq]

theorem dy_perT_eq_sum {A B : ℝ} {G : ℝ × Space → CVec3} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) (j : Fin 3) (p₀ : ℝ × Space) :
    dy j (perT P G) p₀ = ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), dy j G (p₀.1 + k * P, p₀.2) := by
  have hdiff : ∀ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1),
      DifferentiableAt ℝ (fun p : ℝ × Space => G (p.1 + k * P, p.2)) p₀ :=
    fun k _ => ((contDiff_shift hGs _).differentiable (by simp)).differentiableAt
  simp only [dy, (perT_eventuallyEq hP.out hG p₀).fderiv_eq]
  rw [fderiv_fun_sum hdiff, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_shift]

/-- The periodized chart lift of `φ ⊗ Ψ` is a solenoidal phase test. -/
theorem isSolTest_perT_chartLift {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) {A B : ℝ}
    (hT : TimeSupp A B (chartLift (prodTestV φ Ψ))) :
    IsSolTest P (perT P (chartLift (prodTestV φ Ψ))) := by
  have hk := contDiff_prodTestV hφ hΨ.1
  have hG := contDiff_chartLift hk
  have hG0 : IsPhaseTest 0 (chartLift (prodTestV φ Ψ)) :=
    isPhaseTest_zero_of_compact hG
      (hasCompactSupport_chartLift (hasCompactSupport_prodTestV hφc hΨ.2.1))
  refine ⟨isPhaseTest_perT hP.out hT hG0, fun x => ?_⟩
  simp only [dy_perT_eq_sum hT hG, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun k _ => sum_dy_chartLift_prodTestV hφ hΨ _

end UnforcedLeray.Short.IIb.BaseRepSub

end
