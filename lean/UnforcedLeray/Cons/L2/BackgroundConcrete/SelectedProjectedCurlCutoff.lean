import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialJointSmooth
import UnforcedLeray.Lib.LerayLp.Cutoff
import UnforcedLeray.Loc.L09CompactDatum.Solenoidal
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Blueprint.Localization.Nonlinear

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

/-- The spatial curl of a space-time vector field, with the derivative taken only in spatial
coordinates. -/
def spatialCurlST (H : SpaceTime → Space) (z : SpaceTime) : Space :=
  ∑ j : Fin 3, Blueprint.crossProd (coordinateVector j)
    (fderiv ℝ H z (0, coordinateVector j))

/-- Curl of a spatially cut off smooth real vector potential, embedded as a complex phase test. -/
def projectedPotentialCurlCutoff (R : ℝ) (A : SpaceTime → Space) : SpaceTime → CVec3 :=
  fun z => realC (spatialCurlST (fun x => cutoff R x.2 • A x) z)

private theorem contDiff_realC_curl : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  have hEq : realC = UnforcedLeray.Axi.cplxV := by
    funext x
    ext i
    simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]
  rw [hEq]
  exact UnforcedLeray.Axi.cplxV.contDiff.comp contDiff_id

private theorem fderiv_sliceSpaceTime {F : SpaceTime → Space} (hF : ContDiff ℝ ∞ F)
    (τ : ℝ) (y : Space) (j : Fin 3) :
    fderiv ℝ (fun x : Space => F (τ, x)) y (coordinateVector j) =
      fderiv ℝ F (τ, y) (0, coordinateVector j) := by
  have hAt := hF.differentiable (by simp) (τ, y)
  have hcomp := hAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  have heq := hcomp.fderiv
  change fderiv ℝ (fun x : Space => F (τ, x)) y = _ at heq
  rw [heq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

private theorem spatialCurlST_eq_sliceCurl {H : SpaceTime → Space}
    (hH : ContDiff ℝ ∞ H) (τ : ℝ) (y : Space) :
    spatialCurlST H (τ, y) = Blueprint.curl (fun x => H (τ, x)) y := by
  simp only [spatialCurlST, Blueprint.curl]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_sliceSpaceTime hH τ y j]

theorem isSolTest_projectedPotentialCurlCutoff {P R : ℝ} (hP : 0 < P) {A : SpaceTime → Space}
    (hA : ContDiff ℝ ∞ A) (hAper : ∀ τ y, A (τ + P, y) = A (τ, y)) (hR : 0 < R) :
    IsSolTest P (projectedPotentialCurlCutoff R A) := by
  let H : SpaceTime → Space := fun z => cutoff R z.2 • A z
  have hH : ContDiff ℝ ∞ H := by
    dsimp [H]
    exact (cutoff_smooth R).comp contDiff_snd |>.smul hA
  have hder : ContDiff ℝ ∞ (fun z : SpaceTime => fderiv ℝ H z) :=
    hH.fderiv_right (m := ∞) (by simp)
  have hcurl : ContDiff ℝ ∞ (spatialCurlST H) := by
    unfold spatialCurlST
    apply ContDiff.sum
    intro j hj
    have hcomponent : ContDiff ℝ ∞
        (fun z : SpaceTime => fderiv ℝ H z (0, coordinateVector j)) :=
      hder.clm_apply contDiff_const
    change ContDiff ℝ ∞ (fun z : SpaceTime =>
      UnforcedLeray.L09.crossCLM (coordinateVector j)
        (fderiv ℝ H z (0, coordinateVector j)))
    exact (UnforcedLeray.L09.crossCLM (coordinateVector j)).contDiff.comp hcomponent
  have htestSmooth : ContDiff ℝ ∞ (projectedPotentialCurlCutoff R A) := by
    unfold projectedPotentialCurlCutoff
    exact contDiff_realC_curl.comp hcurl
  have hHper : ∀ z : SpaceTime, H (z + (P, 0)) = H z := by
    rintro ⟨τ, y⟩
    dsimp [H]
    simp only [Prod.fst_add, Prod.snd_add, Prod.snd_zero, add_zero]
    exact congrArg (fun v : Space => cutoff R y • v) (hAper τ y)
  have htestPer : ∀ τ y, projectedPotentialCurlCutoff R A (τ + P, y) =
      projectedPotentialCurlCutoff R A (τ, y) := by
    intro τ y
    have hD := fderiv_add_of_invariant hHper (τ, y)
    have hxy : (τ + P, y) = (τ, y) + (P, 0) := by ext <;> simp
    rw [hxy]
    unfold projectedPotentialCurlCutoff spatialCurlST
    rw [hD]
  have htestSupport : ∃ ρ, ∀ τ y, ρ < ‖y‖ →
      projectedPotentialCurlCutoff R A (τ, y) = 0 := by
    refine ⟨2 * R, ?_⟩
    intro τ y hy
    have hz : 2 * R < ‖y‖ := hy
    have hlocal : H =ᶠ[𝓝 (τ, y)] fun _ : SpaceTime => (0 : Space) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hz]
        with z hz
      dsimp [H]
      rw [cutoff_eq_zero hR (le_of_lt hz)]
      simp
    have hzero : fderiv ℝ H (τ, y) = 0 := by
      rw [hlocal.fderiv_eq]
      simp
    change realC (spatialCurlST H (τ, y)) = 0
    simp [spatialCurlST, hzero, realC]
  have htest : IsPhaseTest P (projectedPotentialCurlCutoff R A) :=
    ⟨htestSmooth, htestPer, htestSupport⟩
  refine ⟨htest, ?_⟩
  intro z
  rcases z with ⟨τ, y⟩
  let Hτ : Space → Space := fun x => H (τ, x)
  have hHτ : ContDiff ℝ ∞ Hτ := hH.comp (by fun_prop)
  have hcurlEq : spatialCurlST H (τ, y) = Blueprint.curl Hτ y :=
    spatialCurlST_eq_sliceCurl hH τ y
  have hdiv := UnforcedLeray.L09.div_curl_eq_zero
    (hHτ.contDiffAt (x := y))
  have hcurlfun : (fun x : Space => spatialCurlST H (τ, x)) = Blueprint.curl Hτ :=
    funext fun x => spatialCurlST_eq_sliceCurl hH τ x
  have hC : ContDiff ℝ ∞ (spatialCurlST H) := hcurl
  have hCAt := hC.differentiable (by simp) (τ, y)
  have hEmbed : realC = UnforcedLeray.Axi.cplxV := by
    funext x
    ext i
    simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]
  have hderiv (j : Fin 3) :
      PhaseSpace.dy j (projectedPotentialCurlCutoff R A) (τ, y) =
        UnforcedLeray.Axi.cplxV (fderiv ℝ (spatialCurlST H) (τ, y)
          (0, coordinateVector j)) := by
    rw [PhaseSpace.dy]
    change fderiv ℝ (fun z : SpaceTime => realC (spatialCurlST H z))
      (τ, y) (0, coordinateVector j) = _
    rw [hEmbed]
    have hcomp := UnforcedLeray.Axi.cplxV.hasFDerivAt.comp (τ, y) hCAt.hasFDerivAt
    have heq := congrArg (fun D : SpaceTime →L[ℝ] CVec3 => D (0, coordinateVector j))
      hcomp.fderiv
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using heq
  have hsliceDeriv (j : Fin 3) :
      fderiv ℝ (spatialCurlST H) (τ, y) (0, coordinateVector j) =
        fderiv ℝ (fun x : Space => spatialCurlST H (τ, x)) y (coordinateVector j) := by
    symm
    exact fderiv_sliceSpaceTime hC τ y j
  calc
    (∑ j : Fin 3, PhaseSpace.dy j (projectedPotentialCurlCutoff R A) (τ, y) j) =
        ∑ j : Fin 3, (UnforcedLeray.Axi.cplxV
          (fderiv ℝ (spatialCurlST H) (τ, y) (0, coordinateVector j))) j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hderiv j]
    _ = (((∑ j : Fin 3, fderiv ℝ (Blueprint.curl Hτ) y
          (coordinateVector j) j) : ℝ) : ℂ) := by
          simp_rw [UnforcedLeray.Axi.cplxV_apply, hsliceDeriv]
          rw [show (fun x : Space => spatialCurlST H (τ, x)) = Blueprint.curl Hτ from hcurlfun]
          simp only [map_sum, Complex.ofReal_sum]
    _ = 0 := by rw [hdiv]; simp

#print axioms isSolTest_projectedPotentialCurlCutoff

end UnforcedLeray.Cons.C03.Concrete

end
