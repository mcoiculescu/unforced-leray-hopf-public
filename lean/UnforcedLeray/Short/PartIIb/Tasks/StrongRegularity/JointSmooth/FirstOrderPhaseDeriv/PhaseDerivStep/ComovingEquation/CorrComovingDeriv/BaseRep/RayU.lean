import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Comoving
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.LerayCont
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.ProjectedEvolutionTower.PointwiseDeriv.SolTestOrthEqZero
import UnforcedLeray.Analysis.DerivativeScaling
import UnforcedLeray.Cons.C03Background.Pieces
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# The projected equation integrated along comoving rays (helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

`ray_identity_U`: for a solution `U` of the compact-solenoidal weak equation (`WeakHyp`),
`U(s₂, e^{-s₂/2}x) - U(s₁, e^{-s₁/2}x) = ∫_{s₁}^{s₂} N(r, e^{-r/2}x) dr`,
`N = νΔU + ½U - 𝔓(U·∇U)`. The difference of the two sides is a continuous solenoidal `L⁴` field
(Minkowski for the ray integral) orthogonal to every compactly supported solenoidal test
(`cT_sub_eq_integral` and Fubini), hence zero (`solSepSpatial`). The gradient part of `T₀U`
never enters: along rays the drift `y·∇U` is absorbed by the chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.BochnerTime UnforcedLeray.RieszLp

/-! ## 1. Integrability on `uIoc × ℝ³` -/

theorem integrable_prod_uIoc' {E : Type*} [NormedAddCommGroup E] {Φ : ℝ → Space → E}
    (hΦ : Continuous (Function.uncurry Φ)) {S : Set Space} (hS : IsCompact S)
    (hΦS : ∀ r x, x ∉ S → Φ r x = 0) (a b : ℝ) :
    Integrable (Function.uncurry Φ) ((volume.restrict (Set.uIoc a b)).prod volume) := by
  have hK : IsCompact (uIcc a b ×ˢ S) := isCompact_uIcc.prod hS
  have h1 : IntegrableOn (Function.uncurry Φ) (uIcc a b ×ˢ S)
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    hΦ.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (Function.uncurry Φ) (uIcc a b ×ˢ univ)
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    refine h1.of_forall_sdiff_eq_zero (measurableSet_uIcc.prod MeasurableSet.univ) ?_
    rintro ⟨r, x⟩ ⟨⟨hr, -⟩, hx⟩
    have hxS : x ∉ S := fun hxS => hx ⟨hr, hxS⟩
    exact hΦS r x hxS
  have h3 : IntegrableOn (Function.uncurry Φ) (Set.uIoc a b ×ˢ univ)
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    h2.mono_set (prod_mono uIoc_subset_uIcc subset_rfl)
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h3
  exact h3

/-! ## 2. Solenoidality -/

theorem isSolenoidal_dil {F : SpatialField} (hF : IsSolenoidal F) (s : ℝ) :
    IsSolenoidal (fun x => F (dilScale s • x)) := by
  have h := DerivativeScaling.isSolenoidal_spatialScale hF 1 (dilScale_ne_zero s)
  have e : SpatialScaling.spatialScale 1 (dilScale s) F = fun x => F (dilScale s • x) := by
    funext x
    exact one_smul ℝ _
  rw [e] at h
  exact h

theorem isSolenoidal_comovingEvolRHS (ν : ℝ) {U : ℝ → SpatialField}
    (hU : IsUniformSmoothL4SliceFamily U) (hSol : ∀ τ, IsSolenoidal (U τ)) (τ : ℝ) :
    IsSolenoidal (comovingEvolRHS ν U τ) := by
  have hUs := HigherPhaseSub.sliceFamily_contDiff_infty hU τ
  have h1 : IsSolenoidal (spatialDiffReact ν (U τ)) :=
    Cons.C03.isSolenoidal_add
      (Cons.C03.isSolenoidal_const_smul
        (SolTestOrthEqZeroAux.isSolenoidal_spatialLaplacian hUs (hSol τ)) ν)
      (Cons.C03.isSolenoidal_const_smul (hSol τ) (1 / 2))
  exact SolTestOrthEqZeroAux.isSolenoidal_sub h1
    (PointwiseDerivSub.isSolenoidal_smoothConvectiveLeray hU hU τ)

theorem continuous_uncurry_ray {V : ℝ → SpatialField}
    (hV : Continuous fun x : ℝ × Space => V x.1 x.2) :
    Continuous (Function.uncurry fun (r : ℝ) (y : Space) => V r (dilScale r • y)) :=
  hV.comp continuous_ray

theorem continuous_intervalIntegral_param {F : ℝ → SpatialField}
    (hFc : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous fun x => ∫ r in a..b, F r x :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x r => F r x) (hFc.comp continuous_swap) a b

theorem fderiv_eq_zero_of_notMem_tsupport {φ : Space → ℝ} {x : Space} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 := by
  have h : x ∉ Function.support (fderiv ℝ φ) := fun hx' => hx (support_fderiv_subset ℝ hx')
  simpa using h

/-- The ray integral of solenoidal fields is solenoidal. -/
theorem isSolenoidal_intervalIntegral {F : ℝ → SpatialField}
    (hFc : Continuous (Function.uncurry F)) (hsol : ∀ r, IsSolenoidal (F r)) (a b : ℝ) :
    IsSolenoidal (fun x => ∫ r in a..b, F r x) := by
  have hJc := continuous_intervalIntegral_param hFc a b
  have hcs : ∀ φ : Space → ℝ, IsSpatialTest φ → HasCompactSupport
      (fun x => ∑ i : Fin 3, ((∫ r in a..b, F r x) : Space) i * spatialTestDerivative i φ x) := by
    intro φ hφ
    refine HasCompactSupport.intro hφ.compact.isCompact fun x hx => ?_
    simp [spatialTestDerivative, fderiv_eq_zero_of_notMem_tsupport hx]
  have hcont : ∀ φ : Space → ℝ, IsSpatialTest φ → ∀ G : SpatialField, Continuous G →
      Continuous (fun x => ∑ i : Fin 3, (G x) i * spatialTestDerivative i φ x) := by
    intro φ hφ G hG
    exact continuous_finsetSum _ fun i _ =>
      (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hG)).mul
        (LerayPairSolAux.spatialTestDerivative_continuous hφ i)
  refine ⟨fun φ hφ => (hcont φ hφ _ hJc).integrable_of_hasCompactSupport (hcs φ hφ),
    fun φ hφ => ?_⟩
  have hFr : ∀ x, Continuous fun r => F r x := fun x =>
    hFc.comp (continuous_id.prodMk continuous_const)
  have hpt : ∀ x, ∑ i : Fin 3, ((∫ r in a..b, F r x) : Space) i * spatialTestDerivative i φ x =
      ∫ r in a..b, ∑ i : Fin 3, (F r x) i * spatialTestDerivative i φ x := by
    intro x
    have hcomp : ∀ i : Fin 3, ((∫ r in a..b, F r x) : Space) i = ∫ r in a..b, (F r x) i := by
      intro i
      have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).intervalIntegral_comp_comm
        ((hFr x).intervalIntegrable (μ := volume) a b)
      simpa using this.symm
    have hii : ∀ i ∈ (Finset.univ : Finset (Fin 3)), IntervalIntegrable
        (fun r => (F r x) i * spatialTestDerivative i φ x) volume a b := fun i _ =>
      (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hFr x)).mul
        continuous_const).intervalIntegrable a b
    rw [intervalIntegral.integral_finset_sum hii]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_mul_const, hcomp i]
  simp_rw [hpt]
  have hHc : Continuous (Function.uncurry fun (r : ℝ) (x : Space) =>
      ∑ i : Fin 3, (F r x) i * spatialTestDerivative i φ x) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hFc).mul
      ((LerayPairSolAux.spatialTestDerivative_continuous hφ i).comp continuous_snd)
  have hint := integrable_prod_uIoc' hHc hφ.compact.isCompact (fun r x hx => by
    simp [spatialTestDerivative, fderiv_eq_zero_of_notMem_tsupport hx]) a b
  rw [← MeasureTheory.intervalIntegral_integral_swap hint]
  simp [(hsol _).identity φ hφ]

/-! ## 3. `L⁴` bounds -/

theorem exists_eLpNorm_slice_le {G : ℝ → SpatialField} (hG : IsUniformSmoothL4SliceFamily G) :
    ∃ M : ℝ, ∀ τ, eLpNorm (G τ) 4 volume ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM⟩ := hG.l4_bounded 0
  refine ⟨M, fun τ => ?_⟩
  have heq : eLpNorm (G τ) 4 volume =
      eLpNorm (fun y => iteratedFDeriv ℝ 0 (G τ) y) 4 volume :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero.symm)
  rw [heq]
  exact hM τ

theorem memLp_intervalIntegral_of_le {F : ℝ → SpatialField}
    (hFc : Continuous (Function.uncurry F)) {a b : ℝ} (hab : a ≤ b) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ r ∈ Icc a b, eLpNorm (F r) 4 volume ≤ C) :
    MemLp (fun x => ∫ r in a..b, F r x) 4 volume := by
  refine ⟨(continuous_intervalIntegral_param hFc a b).aestronglyMeasurable, ?_⟩
  simp_rw [intervalIntegral.integral_of_le hab]
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : Space) (r : ℝ) => F r x)
      ((volume : Measure Space).prod (volume.restrict (Ioc a b))) :=
    (hFc.comp continuous_swap).aestronglyMeasurable
  calc eLpNorm (fun x => ∫ r in Ioc a b, F r x) 4 volume
      ≤ ∫⁻ r in Ioc a b, eLpNorm (fun x => F r x) 4 volume :=
        PlanarBS.Conv.eLpNorm_integral_le (F := fun (x : Space) (r : ℝ) => F r x) hmeas
          (by norm_num) (by norm_num)
    _ ≤ ∫⁻ _ in Ioc a b, C :=
        setLIntegral_mono' measurableSet_Ioc fun r hr => hbound r (Ioc_subset_Icc_self hr)
    _ = C * volume (Ioc a b) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top (by simp)

theorem memLp_intervalIntegral {F : ℝ → SpatialField}
    (hFc : Continuous (Function.uncurry F)) (a b : ℝ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ r, r ∈ uIcc a b → eLpNorm (F r) 4 volume ≤ C) :
    MemLp (fun x => ∫ r in a..b, F r x) 4 volume := by
  rcases le_total a b with hab | hab
  · exact memLp_intervalIntegral_of_le hFc hab hC fun r hr =>
      hbound r (by rw [uIcc_of_le hab]; exact hr)
  · have h := memLp_intervalIntegral_of_le hFc hab hC fun r hr =>
      hbound r (by rw [uIcc_of_ge hab]; exact hr)
    have he : (fun x => ∫ r in a..b, F r x) = fun x => -∫ r in b..a, F r x := by
      funext x
      exact intervalIntegral.integral_symm (f := fun r => F r x) b a
    rw [he]
    exact h.neg

/-! ## 4. The ray identity -/

variable {P : ℝ} [hP : Fact (0 < P)]

/-- The ray identity from the tested identity (abstract `U`, `N`). -/
theorem ray_identity_of {U N : ℝ → SpatialField} (hU : IsUniformSmoothL4SliceFamily U)
    (hUsol : ∀ τ, IsSolenoidal (U τ)) (hUc : Continuous fun x : ℝ × Space => U x.1 x.2)
    (hN : IsUniformSmoothL4SliceFamily N) (hNsol : ∀ τ, IsSolenoidal (N τ))
    (hNc : Continuous fun x : ℝ × Space => N x.1 x.2)
    (hcT : ∀ Ψ : Space → CVec3, SpatialSolTest Ψ → ∀ s₁ s₂ : ℝ,
      cT Ψ U s₂ - cT Ψ U s₁ = ∫ r in s₁..s₂, cT Ψ N r) (s₁ s₂ : ℝ) (x : Space) :
    U s₂ (dilScale s₂ • x) - U s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, N r (dilScale r • x) := by
  have hFc : Continuous (Function.uncurry fun (r : ℝ) (y : Space) =>
      N r (dilScale r • y)) :=
    continuous_uncurry_ray (V := N) hNc
  have hAc : Continuous fun y : Space => U s₂ (dilScale s₂ • y) :=
    hUc.comp (continuous_const.prodMk (continuous_id.const_smul (dilScale s₂)))
  have hBc : Continuous fun y : Space => U s₁ (dilScale s₁ • y) :=
    hUc.comp (continuous_const.prodMk (continuous_id.const_smul (dilScale s₁)))
  have hJc : Continuous fun y : Space => ∫ r in s₁..s₂, N r (dilScale r • y) :=
    continuous_intervalIntegral_param hFc s₁ s₂
  suffices hzero : (fun y : Space => U s₂ (dilScale s₂ • y) - U s₁ (dilScale s₁ • y) -
      ∫ r in s₁..s₂, N r (dilScale r • y)) = 0 by
    exact sub_eq_zero.1 (congrFun hzero x)
  refine PointwiseDerivSub.eq_zero_of_isSolenoidal_and_spatialSolTest_orth
    ((hAc.sub hBc).sub hJc) ?_ ?_ ?_
  · -- `L⁴`
    have hmA : MemLp (fun y : Space => U s₂ (dilScale s₂ • y)) 4 volume :=
      memLp_comp_dilScale (E := Space) s₂ (LerayContSub.memLp_slice hU s₂)
    have hmB : MemLp (fun y : Space => U s₁ (dilScale s₁ • y)) 4 volume :=
      memLp_comp_dilScale (E := Space) s₁ (LerayContSub.memLp_slice hU s₁)
    obtain ⟨M, hM⟩ := exists_eLpNorm_slice_le hN
    have hmJ : MemLp (fun y : Space => ∫ r in s₁..s₂, N r (dilScale r • y))
        4 volume := by
      refine memLp_intervalIntegral hFc s₁ s₂
        (C := ENNReal.ofReal (dilConst 4 (max s₁ s₂)) * ENNReal.ofReal M)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) fun r hr => ?_
      rw [eLpNorm_comp_dilScale (E := Space) r
        ((HigherPhaseSub.sliceFamily_contDiff_infty hN r).continuous.aestronglyMeasurable)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (dilConst_mono 4 ?_)) (hM r)
      exact hr.2
    exact (hmA.sub hmB).sub hmJ
  · -- solenoidal
    exact SolTestOrthEqZeroAux.isSolenoidal_sub
      (SolTestOrthEqZeroAux.isSolenoidal_sub (isSolenoidal_dil (hUsol s₂) s₂)
        (isSolenoidal_dil (hUsol s₁) s₁))
      (isSolenoidal_intervalIntegral hFc
        (fun r => isSolenoidal_dil (hNsol r) r) s₁ s₂)
  · -- orthogonal to solenoidal tests
    intro Ψ hΨ
    have hΨc : Continuous Ψ := hΨ.1.continuous
    have hint : ∀ G : SpatialField, Continuous G →
        Integrable (fun y => dotL (Ψ y) (realC (G y))) := by
      intro G hG
      refine Continuous.integrable_of_hasCompactSupport
        ((dotL.continuous.comp hΨc).clm_apply (continuous_realC.comp hG)) ?_
      refine HasCompactSupport.intro hΨ.2.1.isCompact fun y hy => ?_
      rw [image_eq_zero_of_notMem_tsupport hy, map_zero, ContinuousLinearMap.zero_apply]
    have hsplit : (fun y => dotL (Ψ y) (realC (U s₂ (dilScale s₂ • y) - U s₁ (dilScale s₁ • y) -
        ∫ r in s₁..s₂, N r (dilScale r • y)))) =
        fun y => (dotL (Ψ y) (realC (U s₂ (dilScale s₂ • y))) -
          dotL (Ψ y) (realC (U s₁ (dilScale s₁ • y)))) -
          dotL (Ψ y) (realC (∫ r in s₁..s₂, N r (dilScale r • y))) := by
      funext y
      simp only [realC_sub', map_sub]
    have i2 : Integrable (fun y => dotL (Ψ y) (realC (U s₂ (dilScale s₂ • y)))) := hint _ hAc
    have i1 : Integrable (fun y => dotL (Ψ y) (realC (U s₁ (dilScale s₁ • y)))) := hint _ hBc
    have i3 : Integrable (fun y => dotL (Ψ y)
        (realC (∫ r in s₁..s₂, N r (dilScale r • y)))) := hint _ hJc
    have i21 : Integrable (fun y => dotL (Ψ y) (realC (U s₂ (dilScale s₂ • y))) -
        dotL (Ψ y) (realC (U s₁ (dilScale s₁ • y)))) := i2.sub i1
    rw [hsplit, integral_sub i21 i3, integral_sub i2 i1]
    have hFub : ∫ y, dotL (Ψ y) (realC (∫ r in s₁..s₂, N r (dilScale r • y))) =
        ∫ r in s₁..s₂, cT Ψ (N) r := by
      have hpt : ∀ y, dotL (Ψ y) (realC (∫ r in s₁..s₂, N r (dilScale r • y))) =
          ∫ r in s₁..s₂, dotL (Ψ y) (realC (N r (dilScale r • y))) := by
        intro y
        have hFr : Continuous fun r => N r (dilScale r • y) :=
          hFc.comp (continuous_id.prodMk continuous_const)
        have hLv : ∀ v : Space,
            (((dotL (Ψ y)).restrictScalars ℝ).comp ofReV : Space →L[ℝ] ℂ) v =
              dotL (Ψ y) (realC v) := by
          intro v
          rw [PointwiseDerivSub.realC_eq_ofReV]
          rfl
        rw [← hLv, ← ContinuousLinearMap.intervalIntegral_comp_comm _
          (hFr.intervalIntegrable s₁ s₂)]
        simp only [hLv]
      simp_rw [hpt]
      have hHc : Continuous (Function.uncurry fun (r : ℝ) (y : Space) =>
          dotL (Ψ y) (realC (N r (dilScale r • y)))) :=
        (dotL.continuous.comp (hΨc.comp continuous_snd)).clm_apply (continuous_realC.comp hFc)
      have hint2 := integrable_prod_uIoc' hHc hΨ.2.1.isCompact (fun r y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, map_zero, ContinuousLinearMap.zero_apply]) s₁ s₂
      rw [← MeasureTheory.intervalIntegral_integral_swap hint2]
      rfl
    have hc2 : ∫ y, dotL (Ψ y) (realC (U s₂ (dilScale s₂ • y))) = cT Ψ U s₂ := rfl
    have hc1 : ∫ y, dotL (Ψ y) (realC (U s₁ (dilScale s₁ • y))) = cT Ψ U s₁ := rfl
    rw [hc2, hc1, hFub, hcT Ψ hΨ s₁ s₂, sub_self]

/-- **Integrated projected equation along comoving rays.** -/
theorem ray_identity_U {ν : ℝ} {U : ℝ → SpatialField} (h : WeakHyp P ν U) (s₁ s₂ : ℝ)
    (x : Space) :
    U s₂ (dilScale s₂ • x) - U s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, comovingEvolRHS ν U r (dilScale r • x) :=
  ray_identity_of h.slice h.sol h.cont (sliceFamily_comovingEvolRHS ν h.slice)
    (isSolenoidal_comovingEvolRHS ν h.slice h.sol) h.contN
    (fun Ψ hΨ s₁ s₂ => cT_sub_eq_integral h hΨ s₁ s₂) s₁ s₂ x

end UnforcedLeray.Short.IIb.BaseRepSub

end
