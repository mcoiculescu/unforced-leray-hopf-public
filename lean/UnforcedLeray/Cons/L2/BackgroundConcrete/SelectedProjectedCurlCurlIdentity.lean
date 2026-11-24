import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedNewtonCurlPotential
import UnforcedLeray.Loc.L09CompactDatum.Solenoidal

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped ContDiff

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.RieszLp

/-- Spatial divergence of a smooth real vector field. -/
def spatialDivergence (B : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ B x (coordinateVector i) i

/-- Componentwise spatial Laplacian of a smooth real vector field. -/
def spatialLaplacian (B : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ B y (coordinateVector i)) x
    (coordinateVector i)

theorem curl_curl_eq_gradDivergence_sub_laplacian {B : Space → Space}
    (hB : ContDiff ℝ ∞ B) (x : Space) :
    Blueprint.curl (Blueprint.curl B) x =
      gradField (spatialDivergence B) x - spatialLaplacian B x := by
  have hBx : ContDiffAt ℝ ∞ B x := hB.contDiffAt (x := x)
  have hD : DifferentiableAt ℝ (fderiv ℝ B) x :=
    (hBx.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hcurl := UnforcedLeray.L09.hasFDerivAt_curl hD
  have hcurlDeriv (i : Fin 3) :
      fderiv ℝ (Blueprint.curl B) x (coordinateVector i) =
        ∑ j : Fin 3, Blueprint.crossProd (coordinateVector j)
          (fderiv ℝ (fderiv ℝ B) x (coordinateVector i) (coordinateVector j)) := by
    have heq := congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) hcurl.fderiv
    simpa [ContinuousLinearMap.coe_sum', Function.comp_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearMap.apply_apply,
      UnforcedLeray.L09.crossCLM_apply] using heq
  have hsymm : IsSymmSndFDerivAt ℝ B x := hBx.isSymmSndFDerivAt (by simp)
  have hsecond (i j : Fin 3) :
      fderiv ℝ (fderiv ℝ B) x (coordinateVector i) (coordinateVector j) =
        fderiv ℝ (fderiv ℝ B) x (coordinateVector j) (coordinateVector i) :=
    hsymm (coordinateVector i) (coordinateVector j)
  have hsecondCoord (i j k : Fin 3) :
      (fderiv ℝ (fderiv ℝ B) x (coordinateVector i) (coordinateVector j)) k =
        (fderiv ℝ (fderiv ℝ B) x (coordinateVector j) (coordinateVector i)) k :=
    congrArg (fun v : Space => v k) (hsecond i j)
  have hcomponent (i j : Fin 3) :
      fderiv ℝ (fun y : Space => fderiv ℝ B y (coordinateVector i) i) x
          (coordinateVector j) =
        (fderiv ℝ (fderiv ℝ B) x (coordinateVector j) (coordinateVector i)) i := by
    have hGi : DifferentiableAt ℝ
        (fun y : Space => fderiv ℝ B y (coordinateVector i)) x := by
      exact ((hBx.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiffAt_const (c := coordinateVector i))).differentiableAt (by simp)
    have hInner : fderiv ℝ (fun y : Space => fderiv ℝ B y (coordinateVector i)) x =
        (fderiv ℝ (fderiv ℝ B) x).flip (coordinateVector i) := by
      rw [fderiv_clm_apply hD (differentiableAt_const (coordinateVector i))]
      simp
    change fderiv ℝ (fun y : Space =>
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ B y (coordinateVector i)))
        x (coordinateVector j) = _
    rw [fderiv_clm_apply (differentiableAt_const
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ)) hGi]
    rw [hInner]
    simp
  have hgrad (k : Fin 3) :
      spatialTestDerivative k (spatialDivergence B) x =
        ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ B) x (coordinateVector k)
          (coordinateVector i)) i := by
    unfold spatialTestDerivative spatialDivergence
    rw [fderiv_fun_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      exact hcomponent i k
    · intro i hi
      change DifferentiableAt ℝ (fun y : Space =>
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ B y (coordinateVector i))) x
      have hV : DifferentiableAt ℝ
          (fun y : Space => fderiv ℝ B y (coordinateVector i)) x :=
        (hD.clm_apply (differentiableAt_const (coordinateVector i))).choose_spec.differentiableAt
      exact ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        hV.hasFDerivAt).differentiableAt
  have hlap (k : Fin 3) :
      spatialLaplacian B x k =
        ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ B) x (coordinateVector i)
          (coordinateVector i)) k := by
    unfold spatialLaplacian
    rw [WithLp.ofLp_sum]
    change (∑ i : Fin 3,
      (fderiv ℝ (fun y : Space => fderiv ℝ B y (coordinateVector i)) x
        (coordinateVector i)).ofLp k) = _
    apply Finset.sum_congr rfl
    intro i hi
    have hInner : fderiv ℝ (fun y : Space => fderiv ℝ B y (coordinateVector i)) x =
        (fderiv ℝ (fderiv ℝ B) x).flip (coordinateVector i) := by
      rw [fderiv_clm_apply hD (differentiableAt_const (coordinateVector i))]
      simp
    rw [hInner]
    rfl
  have hcurlcurl : Blueprint.curl (Blueprint.curl B) x =
      ∑ i : Fin 3, ∑ j : Fin 3, Blueprint.crossProd (coordinateVector i)
        (Blueprint.crossProd (coordinateVector j)
          (fderiv ℝ (fderiv ℝ B) x (coordinateVector i) (coordinateVector j))) := by
    change (∑ i : Fin 3, Blueprint.crossProd (coordinateVector i)
        (fderiv ℝ (Blueprint.curl B) x (coordinateVector i))) = _
    simp_rw [hcurlDeriv]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.sum_univ_three, UnforcedLeray.L09.crossProd_add_right]
  ext k
  rw [hcurlcurl]
  change (∑ i : Fin 3, ∑ j : Fin 3, Blueprint.crossProd (coordinateVector i)
      (Blueprint.crossProd (coordinateVector j)
        (fderiv ℝ (fderiv ℝ B) x (coordinateVector i) (coordinateVector j)))).ofLp k =
    (gradField (spatialDivergence B) x - spatialLaplacian B x).ofLp k
  simp only [WithLp.ofLp_sub, PiLp.sub_apply]
  rw [gradField_apply, hgrad k, hlap k]
  simp only [UnforcedLeray.L09.crossProd_crossProd, UnforcedLeray.L09.inner_coords,
    Finset.sum_sub_distrib, smul_eq_mul, PiLp.sub_apply, PiLp.smul_apply]
  simp_rw [WithLp.ofLp_sum, Finset.sum_apply]
  fin_cases k <;> simp [Fin.sum_univ_three, UnforcedLeray.L09.coordinateVector_apply,
    norm_coordinateVector, hsecondCoord]

#print axioms curl_curl_eq_gradDivergence_sub_laplacian

end UnforcedLeray.Cons.C03.Concrete

end
