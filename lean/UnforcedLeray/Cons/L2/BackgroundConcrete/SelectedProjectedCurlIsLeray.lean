import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedNewtonComponent
import UnforcedLeray.Lib.CZL2.RieszL2
import UnforcedLeray.Units.B0005.Bridge.Solenoidal

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open MeasureTheory
open UnforcedLeray.Blueprint UnforcedLeray.RieszLp UnforcedLeray.PressureAnalysis
open UnforcedLeray.PhaseSpace
open scoped ContDiff

private theorem projectedTest_slice_component_isSpatialTest {P : ℝ}
    {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ) (i : Fin 3) :
    IsSpatialTest (fun y : Space => Φ (τ, y) i) := by
  refine ⟨(EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
      (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)), ?_⟩
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  exact UnforcedLeray.B0005.hasCompactSupport_of_bound (R := R) fun y hy => by
    simp [hR τ y hy]

private theorem projectedTestNewton_divergence {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    spatialDivergence (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) y =
      lerayPotential (fun i x => Φ (τ, x) i) y := by
  let f : Fin 3 → Space → ℝ := fun i x => Φ (τ, x) i
  have hf : ∀ i, IsSpatialTest (f i) := fun i => by
    simpa [f] using projectedTest_slice_component_isSpatialTest hΦ τ i
  have hcomponent (i : Fin 3) :
      (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x) i) =
        newtonConv (f i) := by
    funext x
    simpa [f] using projectedTestNewtonVectorPotential_component hΦ τ x i
  have hB : ContDiff ℝ ∞ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) :=
    (contDiff_projectedTestNewtonVectorPotential hΦ).comp
      (contDiff_const.prodMk contDiff_id)
  have hcoord (i : Fin 3) :
      fderiv ℝ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) y
        (coordinateVector i) i =
        spatialTestDerivative i (fun x => projectedTestNewtonVectorPotential Φ (τ, x) i) y := by
    change (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
        (fderiv ℝ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) y
          (coordinateVector i)) =
      fderiv ℝ (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
        (projectedTestNewtonVectorPotential Φ (τ, x))) y (coordinateVector i)
    have hfd := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y
      (hB.differentiable (by simp) y).hasFDerivAt).fderiv
    exact (congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector i)) hfd).symm
  unfold spatialDivergence
  simp_rw [hcoord, hcomponent]
  simp_rw [spatialTestDerivative_newtonConv (hf _) _]
  rw [show lerayPotential f = newtonConv (divTest f) from rfl]
  rw [show divTest f = (fun x => ∑ i : Fin 3,
      spatialTestDerivative i (f i) x) from rfl]
  simpa using (congrFun
    (newtonConv_sum Finset.univ (fun i => (hf i).derivative i)) y).symm

private theorem projectedTestNewton_laplacian {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    spatialLaplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) y =
      -vecField (fun i x => Φ (τ, x) i) y := by
  let f : Fin 3 → Space → ℝ := fun i x => Φ (τ, x) i
  have hf : ∀ i, IsSpatialTest (f i) := fun i => by
    simpa [f] using projectedTest_slice_component_isSpatialTest hΦ τ i
  have hB : ContDiff ℝ ∞ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) :=
    (contDiff_projectedTestNewtonVectorPotential hΦ).comp
      (contDiff_const.prodMk contDiff_id)
  have hcomponent (i : Fin 3) :
      (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x) i) =
        newtonConv (f i) := by
    funext x
    simpa [f] using projectedTestNewtonVectorPotential_component hΦ τ x i
  ext i
  change spatialLaplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) y i =
    -vecField (fun i x => Φ (τ, x) i) y i
  have hL : spatialLaplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) y i =
      Heat.laplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x) i) y := by
    unfold spatialLaplacian
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    have hSecond (j : Fin 3) :
        fderiv ℝ (fun x : Space => fderiv ℝ
          (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
          (coordinateVector j)) y (coordinateVector j) i =
        fderiv ℝ (fun x : Space => fderiv ℝ
          (fun x => projectedTestNewtonVectorPotential Φ (τ, x) i) x
          (coordinateVector j)) y (coordinateVector j) := by
      have hfirst (x : Space) :
          (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
              (fderiv ℝ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) x
                (coordinateVector j)) =
          fderiv ℝ (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
            (projectedTestNewtonVectorPotential Φ (τ, x))) x (coordinateVector j) := by
        have hfd := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x
          (hB.differentiable (by simp) x).hasFDerivAt).fderiv
        exact (congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector j)) hfd).symm
      have hfunc :
          (fun x : Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
            (fderiv ℝ (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
              (coordinateVector j))) =
          (fun x : Space => fderiv ℝ
            (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
              (projectedTestNewtonVectorPotential Φ (τ, x))) x
            (coordinateVector j)) := funext hfirst
      have hD : DifferentiableAt ℝ
          (fderiv ℝ (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x))) y :=
        ((hB.contDiffAt (x := y)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
      have hG : DifferentiableAt ℝ
          (fun x : Space => fderiv ℝ
            (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
            (coordinateVector j)) y :=
        (hD.clm_apply (differentiableAt_const (coordinateVector j))).choose_spec.differentiableAt
      have hfd2 := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y
        hG.hasFDerivAt).fderiv
      change (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
          (fderiv ℝ (fun x : Space => fderiv ℝ
            (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
            (coordinateVector j)) y (coordinateVector j)) =
        fderiv ℝ (fun x => fderiv ℝ
          (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
            (projectedTestNewtonVectorPotential Φ (τ, x))) x (coordinateVector j)) y
          (coordinateVector j)
      have hstep : (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
          (fderiv ℝ (fun x : Space => fderiv ℝ
            (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
            (coordinateVector j)) y (coordinateVector j)) =
          (fderiv ℝ (fun x : Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
            (fderiv ℝ (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
              (coordinateVector j))) y (coordinateVector j)) :=
        (congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector j)) hfd2).symm
      have hstep2 : (fderiv ℝ (fun x : Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
          (fderiv ℝ (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) x
            (coordinateVector j))) y (coordinateVector j)) =
          fderiv ℝ (fun x => fderiv ℝ
            (fun x => (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
              (projectedTestNewtonVectorPotential Φ (τ, x))) x (coordinateVector j)) y
            (coordinateVector j) :=
        congrArg (fun g : Space → ℝ => fderiv ℝ g y (coordinateVector j)) hfunc
      exact hstep.trans hstep2
    simp_rw [hSecond]
    have hΔ : Heat.laplacian (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x) i) y =
        ∑ j : Fin 3, spatialTestDerivative j
          (spatialTestDerivative j (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x) i)) y := rfl
    change (∑ j : Fin 3, spatialTestDerivative j
      (spatialTestDerivative j (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x) i)) y) = _
    rw [← hΔ]
  calc
    spatialLaplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) y i =
        Heat.laplacian (fun x => projectedTestNewtonVectorPotential Φ (τ, x) i) y := hL
    _ = -f i y := by rw [hcomponent i, laplacian_newtonConv (hf i)]
    _ = -vecField f y i := by simp [vecField_apply]

private theorem spatialCurlST_eq_sliceCurl_local {H : SpaceTime → Space}
    (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space) :
    spatialCurlST H (τ, y) = Blueprint.curl (fun x => H (τ, x)) y := by
  have hAt := hH.differentiable (by simp) (τ, y)
  have hcomp := hAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => H (τ, x)) y = _ at heq
  simp only [spatialCurlST, Blueprint.curl]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) heq
  rw [hj']
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The curl of the actual Newton vector potential is the Newton representative of the
Helmholtz/Leray projection, pointwise on each phase slice. -/
theorem projectedTestNewtonCurl_eq_projectionFormula {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    spatialCurlST (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y) =
      (vecField (fun i x => Φ (τ, x) i) +
        gradField (lerayPotential (fun i x => Φ (τ, x) i))) y := by
  have hA : ContDiff ℝ ∞ (projectedTestNewtonVectorPotential Φ) :=
    contDiff_projectedTestNewtonVectorPotential hΦ
  have hC : ContDiff ℝ ∞ (fun z => spatialCurlST
      (projectedTestNewtonVectorPotential Φ) z) := contDiff_spatialCurlST_of_contDiff hA
  rw [spatialCurlST_eq_sliceCurl_local hC τ y]
  have hinner : (fun x : Space => spatialCurlST
      (projectedTestNewtonVectorPotential Φ) (τ, x)) =
      Blueprint.curl (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) := by
    funext x
    exact spatialCurlST_eq_sliceCurl_local hA τ x
  rw [hinner]
  have hslice : ContDiff ℝ ∞
      (fun x : Space => projectedTestNewtonVectorPotential Φ (τ, x)) :=
    (contDiff_projectedTestNewtonVectorPotential hΦ).comp
      (contDiff_const.prodMk contDiff_id)
  have hcurl := curl_curl_eq_gradDivergence_sub_laplacian hslice y
  rw [hcurl]
  have hdiv : spatialDivergence
      (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) =
      lerayPotential (fun i x => Φ (τ, x) i) :=
    funext (projectedTestNewton_divergence hΦ τ)
  rw [hdiv]
  have hlap : spatialLaplacian
      (fun x => projectedTestNewtonVectorPotential Φ (τ, x)) =
      -vecField (fun i x => Φ (τ, x) i) :=
    funext (projectedTestNewton_laplacian hΦ τ)
  rw [hlap]
  rw [sub_eq_add_neg]
  simp only [Pi.neg_apply, neg_neg]
  exact add_comm _ _

#print axioms projectedTestNewtonCurl_eq_projectionFormula

private theorem toL2_congr_ae_local {f g : SpatialField} (hf : MemLp f 2 volume)
    (hfg : f =ᵐ[volume] g) : toL2 f = toL2 g := by
  have hg : MemLp g 2 volume := (memLp_congr_ae hfg).mp hf
  rw [toL2_of_memLp hf, toL2_of_memLp hg]
  exact (hf.toLp_eq_toLp_iff hg).mpr hfg

/-- In the L² realization, the actual curl of the Newton vector potential is the Leray
projection of the original compact smooth phase test. -/
theorem projectedTestNewtonCurl_toL2_eq_lerayProjection {P : ℝ}
    {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    toL2 (fun y => spatialCurlST
      (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y)) =
      Leray.projection (toL2 (vecField (fun i y => Φ (τ, y) i))) := by
  let f : Fin 3 → Space → ℝ := fun i y => Φ (τ, y) i
  have hf : ∀ i, IsSpatialTest (f i) := fun i => by
    simpa [f] using projectedTest_slice_component_isSpatialTest hΦ τ i
  have hformula : ∀ y, spatialCurlST
      (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y) =
      (vecField f + gradField (lerayPotential f)) y := by
    intro y
    simpa [f] using projectedTestNewtonCurl_eq_projectionFormula hΦ τ y
  have hsum : MemLp (vecField f + gradField (lerayPotential f)) 2 volume :=
    (memLp_vecField hf 2).add (memLp_gradField_lerayPotential hf)
  have hmem : MemLp (fun y => spatialCurlST
      (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y)) 2 volume :=
    (memLp_congr_ae (ae_of_all volume hformula)).mpr hsum
  calc
    toL2 (fun y => spatialCurlST
        (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y)) =
        toL2 (vecField f + gradField (lerayPotential f)) :=
      toL2_congr_ae_local hmem (ae_of_all volume hformula)
    _ = Leray.projection (toL2 (vecField f)) :=
      (projection_toL2_vecField hf).symm

#print axioms projectedTestNewtonCurl_toL2_eq_lerayProjection

end UnforcedLeray.Cons.C03.Concrete

end
