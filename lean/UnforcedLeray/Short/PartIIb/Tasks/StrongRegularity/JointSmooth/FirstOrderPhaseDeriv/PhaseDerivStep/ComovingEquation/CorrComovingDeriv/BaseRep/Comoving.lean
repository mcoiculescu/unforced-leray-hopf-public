import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Weak

/-!
# Comoving tested values of a solution of the projected equation
(helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

For a compactly supported smooth spatial solenoidal `Ψ`, the comoving tested value
`cT Ψ U s = ∫ Ψ(x) · U(s, e^{-s/2} x) dx` of a solution `U` of the compact-solenoidal weak equation
has weak (hence, being continuous, classical integrated) derivative `cT Ψ N`,
`N = νΔU + ½U - 𝔓(U·∇U)` (`cT_sub_eq_integral`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.BochnerTime UnforcedLeray.RieszLp

/-- The comoving tested value `s ↦ ∫ Ψ(x) · V(s, e^{-s/2} x) dx`. -/
def cT (Ψ : Space → CVec3) (V : ℝ → SpatialField) (s : ℝ) : ℂ :=
  ∫ x, dotL (Ψ x) (realC (V s (dilScale s • x)))

theorem continuous_ray : Continuous fun p : ℝ × Space => ((p.1, dilScale p.1 • p.2) : ℝ × Space) :=
  continuous_fst.prodMk ((continuous_dilScale.comp continuous_fst).smul continuous_snd)

theorem continuous_cT {Ψ : Space → CVec3} (hΨc : Continuous Ψ) (hΨcs : HasCompactSupport Ψ)
    {V : ℝ → SpatialField} (hVc : Continuous fun x : ℝ × Space => V x.1 x.2) :
    Continuous (cT Ψ V) := by
  have heq : cT Ψ V = fun s => ∫ x in tsupport Ψ, dotL (Ψ x) (realC (V s (dilScale s • x))) := by
    funext s
    unfold cT
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, map_zero, ContinuousLinearMap.zero_apply]
  rw [heq]
  have hc : Continuous (Function.uncurry fun (s : ℝ) (x : Space) =>
      dotL (Ψ x) (realC (V s (dilScale s • x)))) :=
    (dotL.continuous.comp (hΨc.comp continuous_snd)).clm_apply
      (continuous_realC.comp (hVc.comp continuous_ray))
  exact continuous_parametric_integral_of_continuous hc hΨcs

theorem integral_chartLift_prodTestV (φ : ℝ → ℝ) (Ψ : Space → CVec3) (V : ℝ → SpatialField)
    (t : ℝ) :
    ∫ y, dotL (chartLift (prodTestV φ Ψ) (t, y)) (realC (V t y)) = φ t • cT Ψ V t := by
  rw [integral_chartLift (prodTestV φ Ψ) t (fun y => realC (V t y))]
  unfold cT
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [prodTestV, ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply]

/-- The hypotheses on `U` used in the comoving argument. -/
structure WeakHyp (P ν : ℝ) (U : ℝ → SpatialField) : Prop where
  slice : IsUniformSmoothL4SliceFamily U
  sol : ∀ τ, IsSolenoidal (U τ)
  cont : Continuous fun x : ℝ × Space => U x.1 x.2
  contN : Continuous fun x : ℝ × Space => comovingEvolRHS ν U x.1 x.2
  contC : Continuous fun x : ℝ × Space => spatialConvect (U x.1) (U x.1) x.2
  per : Function.Periodic U P
  weak : ∀ Φ, IsSolTest P Φ →
    pairF P (L0T ν Φ) (fun x => realC (U x.1 x.2)) =
      pairF P (advT (fun x => realC (U x.1 x.2)) Φ) (fun x => realC (U x.1 x.2))

variable {P : ℝ} [hP : Fact (0 < P)]

theorem comovingEvolRHS_periodic {ν : ℝ} {U : ℝ → SpatialField} (hper : Function.Periodic U P) :
    Function.Periodic (comovingEvolRHS ν U) P := by
  intro τ
  simp only [comovingEvolRHS, smoothConvectiveLeray, smoothLeraySlice, hper τ]

/-- **Weak identity.** `∫ φ' cT Ψ U = -∫ φ cT Ψ N` for every time test `φ`. -/
theorem weak_identity_cT {ν : ℝ} {U : ℝ → SpatialField} (h : WeakHyp P ν U)
    {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∫ s, deriv φ s • cT Ψ U s = -∫ s, φ s • cT Ψ (comovingEvolRHS ν U) s := by
  have hk := contDiff_prodTestV hφ hΨ.1
  have hkc := hasCompactSupport_prodTestV hφc hΨ.2.1
  have hG := contDiff_chartLift hk
  have hGc := hasCompactSupport_chartLift hkc
  have hG0 := isPhaseTest_zero_of_compact hG hGc
  obtain ⟨R, hR0, hT⟩ := exists_timeSupp_of_compact hGc
  have hΦ : IsSolTest P (perT P (chartLift (prodTestV φ Ψ))) :=
    isSolTest_perT_chartLift hφ hφc hΨ hT
  have hdrift := pairF_driftT_eq_of_weak ν hΦ h.slice h.sol h.cont h.contN h.contC (h.weak _ hΦ)
  rw [driftT_perT hP.out hT hG] at hdrift
  set φ' : ℝ → ℝ := fun s => -deriv φ s with hφ'
  have hφ'1 : ContDiff ℝ ∞ φ' := (contDiff_infty_iff_deriv.mp hφ).2.neg
  have hφ'c : HasCompactSupport φ' := hφc.deriv.comp_left neg_zero
  have hdG : driftT (chartLift (prodTestV φ Ψ)) = chartLift (prodTestV φ' Ψ) := by
    rw [driftT_chartLift hk]
    congr 1
    funext q
    rw [dτ_prodTestV hφ hΨ.1 q]
    simp [prodTestV, hφ', neg_smul]
  rw [hdG] at hdrift
  have hk' := contDiff_prodTestV hφ'1 hΨ.1
  have hk'c := hasCompactSupport_prodTestV hφ'c hΨ.2.1
  have hG'0 := isPhaseTest_zero_of_compact (contDiff_chartLift hk') (hasCompactSupport_chartLift hk'c)
  obtain ⟨R', hR'0, hT'⟩ := exists_timeSupp_of_compact (hasCompactSupport_chartLift hk'c)
  have hUper : ∀ τ y, (fun x : ℝ × Space => realC (U x.1 x.2)) (τ + P, y) =
      (fun x : ℝ × Space => realC (U x.1 x.2)) (τ, y) := fun τ y => by
    simp only [h.per τ]
  have hNper : ∀ τ y, (fun x : ℝ × Space => realC (comovingEvolRHS ν U x.1 x.2)) (τ + P, y) =
      (fun x : ℝ × Space => realC (comovingEvolRHS ν U x.1 x.2)) (τ, y) := fun τ y => by
    simp only [comovingEvolRHS_periodic h.per τ]
  rw [pairF_perT (u := fun x : ℝ × Space => realC (U x.1 x.2)) hP.out hG'0 (by linarith) hT'
      (continuous_realC.comp h.cont) hUper,
    pairF_perT (u := fun x : ℝ × Space => realC (comovingEvolRHS ν U x.1 x.2)) hP.out hG0
      (by linarith) hT (continuous_realC.comp h.contN) hNper] at hdrift
  have hP0 : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero hP.out.ne'
  have h2 := smul_right_injective ℂ hP0 hdrift
  simp only [integral_chartLift_prodTestV] at h2
  have h3 : ∫ s, φ' s • cT Ψ U s = -∫ s, deriv φ s • cT Ψ U s := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [hφ', neg_smul]
  rw [h3] at h2
  rw [← h2, neg_neg]

theorem hasWeakDerivTime_cT {ν : ℝ} {U : ℝ → SpatialField} (h : WeakHyp P ν U)
    {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) (a b : ℝ) :
    HasWeakDerivTime a b (cT Ψ U) (cT Ψ (comovingEvolRHS ν U)) := by
  have c1 := continuous_cT hΨ.1.continuous hΨ.2.1 h.cont
  have c2 := continuous_cT hΨ.1.continuous hΨ.2.1 h.contN
  refine ⟨(c1.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self,
    (c2.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self,
    fun φ hφ hφc _ => weak_identity_cT h hΨ hφ hφc⟩

/-- **Integrated comoving identity, tested.** -/
theorem cT_sub_eq_integral {ν : ℝ} {U : ℝ → SpatialField} (h : WeakHyp P ν U)
    {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ) (s₁ s₂ : ℝ) :
    cT Ψ U s₂ - cT Ψ U s₁ = ∫ r in s₁..s₂, cT Ψ (comovingEvolRHS ν U) r := by
  set a : ℝ := min s₁ s₂ - 1 with ha
  set b : ℝ := max s₁ s₂ + 1 with hb
  have hab : a < b := by
    have := min_le_max (a := s₁) (b := s₂)
    linarith
  have hw := hasWeakDerivTime_cT h hΨ a b
  have hc := (continuous_cT hΨ.1.continuous hΨ.2.1 h.cont).continuousOn (s := Icc a b)
  have heq := hw.eqOn_rep hab hc (Filter.EventuallyEq.refl _ _)
  have h1 : s₁ ∈ Icc a b := ⟨by linarith [min_le_left s₁ s₂], by linarith [le_max_left s₁ s₂]⟩
  have h2 : s₂ ∈ Icc a b := ⟨by linarith [min_le_right s₁ s₂], by linarith [le_max_right s₁ s₂]⟩
  rw [heq h1, heq h2]
  exact hw.rep_sub_rep h1 h2

end UnforcedLeray.Short.IIb.BaseRepSub

end
