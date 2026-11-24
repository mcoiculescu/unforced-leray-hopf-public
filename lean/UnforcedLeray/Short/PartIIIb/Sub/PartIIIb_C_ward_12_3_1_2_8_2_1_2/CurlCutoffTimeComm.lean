import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `curlCutoffTimeComm`: the phase derivative of the cut-off error

Proves `CurlCutoffTimeComm` (`Statements.lean`), source lines 1446-1455. The phase derivative
commutes with the spatial curl (symmetry of second derivatives), `∂_τ` of the cut-off factor
`χ_R(y)` vanishes, and `realC` is a continuous real-linear map.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

/-- The cross product with a fixed vector, as a continuous linear map. -/
def ctCross (a : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun b => Blueprint.crossProd a b
      map_add' := fun b c => UnforcedLeray.L09.crossProd_add_right a b c
      map_smul' := fun c b => UnforcedLeray.L09.crossProd_smul_right c a b }

theorem ctCross_apply (a b : Space) : ctCross a b = Blueprint.crossProd a b := rfl

theorem ctRealC_eq_cplxV : (realC : Space → CVec3) = ⇑UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

/-- Space-valued version of the symmetry of mixed second derivatives. -/
theorem ctFderivApply {G : ℝ × Space → Space} (hG : ContDiff ℝ ∞ G) (v w p : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ G q w) p v = fderiv ℝ (fderiv ℝ G) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ G y w) ((fderiv ℝ (fderiv ℝ G) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

/-- `∂_y` and `∂_τ` commute on smooth space-valued fields. -/
theorem ctDy_dτ {G : ℝ × Space → Space} (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    dy j (dτ G) = dτ (dy j G) := by
  funext p
  show fderiv ℝ (fun q => fderiv ℝ G q (1, 0)) p (0, coordinateVector j) =
    fderiv ℝ (fun q => fderiv ℝ G q (0, coordinateVector j)) p (1, 0)
  rw [ctFderivApply hG (0, coordinateVector j) (1, 0) p,
    ctFderivApply hG (1, 0) (0, coordinateVector j) p]
  exact (hG.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- The spatial curl commutes with `∂_τ`. -/
theorem ctDτ_spatialCurlST {G : ℝ × Space → Space} (hG : ContDiff ℝ ∞ G) :
    dτ (spatialCurlST G) = spatialCurlST (dτ G) := by
  have hdy : ∀ j : Fin 3, Differentiable ℝ (dy j G) := fun j => by
    have : ContDiff ℝ ∞ (dy j G) := by
      unfold dy
      exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact this.differentiable (by simp)
  funext w
  have hfun : spatialCurlST G = fun w => ∑ j : Fin 3, ctCross (coordinateVector j) (dy j G w) := by
    funext w'
    rfl
  show fderiv ℝ (spatialCurlST G) w (1, 0) = ∑ j : Fin 3, ctCross (coordinateVector j) (dy j (dτ G) w)
  rw [hfun, fderiv_fun_sum (A := fun j w' => ctCross (coordinateVector j) (dy j G w'))
    (fun j _ => (ctCross (coordinateVector j)).differentiableAt.comp w (hdy j w))]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => ?_)
  have hj : fderiv ℝ (fun w => ctCross (coordinateVector j) (dy j G w)) w =
      (ctCross (coordinateVector j)).comp (fderiv ℝ (dy j G) w) :=
    ((ctCross (coordinateVector j)).hasFDerivAt.comp w (hdy j w).hasFDerivAt).fderiv
  rw [hj, ContinuousLinearMap.comp_apply, ctDy_dτ hG j]
  rfl

/-- `realC` composed with a differentiable field commutes with `∂_τ`. -/
theorem ctDτ_realC {F : ℝ × Space → Space} (hF : Differentiable ℝ F) :
    dτ (fun z => realC (F z)) = fun z => realC (dτ F z) := by
  funext z
  have hc : HasFDerivAt (fun w => realC (F w)) (UnforcedLeray.Axi.cplxV.comp (fderiv ℝ F z)) z := by
    have h := UnforcedLeray.Axi.cplxV.hasFDerivAt.comp z (hF z).hasFDerivAt
    rw [ctRealC_eq_cplxV]
    exact h
  show fderiv ℝ (fun w => realC (F w)) z (1, 0) = realC (fderiv ℝ F z (1, 0))
  rw [hc.fderiv]
  rw [ctRealC_eq_cplxV]
  rfl

/-- `∂_τ (χ_R(y) B)` is `χ_R(y) ∂_τ B`: the cut-off factor does not depend on `τ`. -/
theorem ctDτ_cutoff_smul {B : ℝ × Space → Space} (hB : ContDiff ℝ ∞ B) (R : ℝ) :
    dτ (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w) =
      fun w => (cutoff R w.2 - 1) • dτ B w := by
  have hc1 : ContDiff ℝ ∞ (fun x : Space => cutoff R x - 1) :=
    (cutoff_smooth R).sub contDiff_const
  have ha : Differentiable ℝ (fun w : ℝ × Space => cutoff R w.2 - 1) :=
    (hc1.comp contDiff_snd).differentiable (by simp)
  have hBd : Differentiable ℝ B := hB.differentiable (by simp)
  have hz : ∀ w : ℝ × Space, fderiv ℝ (fun w : ℝ × Space => cutoff R w.2 - 1) w (1, 0) = 0 := by
    intro w
    have h2 : fderiv ℝ (fun w : ℝ × Space => cutoff R w.2 - 1) w =
        (fderiv ℝ (fun x : Space => cutoff R x - 1) w.2).comp (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((hc1.differentiable (by simp) w.2).hasFDerivAt.comp w hasFDerivAt_snd).fderiv
    rw [h2]
    simp
  funext w
  show fderiv ℝ ((fun w : ℝ × Space => cutoff R w.2 - 1) • B) w (1, 0) = _
  rw [fderiv_smul (ha w) (hBd w)]
  rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hz w, zero_smul, add_zero]
  rfl

theorem curlCutoffTimeComm : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.CurlCutoffTimeComm := by
  intro B hB R
  have hG : ContDiff ℝ ∞ (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w) :=
    (((cutoff_smooth R).comp contDiff_snd).sub contDiff_const).smul hB
  have hSC : Differentiable ℝ (spatialCurlST (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w)) :=
    (contDiff_spatialCurlST_of_contDiff hG).differentiable (by simp)
  show dτ (fun z => realC (spatialCurlST (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w) z)) =
    fun z => realC (spatialCurlST (fun w : ℝ × Space => (cutoff R w.2 - 1) • dτ B w) z)
  rw [ctDτ_realC hSC, ctDτ_spatialCurlST hG, ctDτ_cutoff_smul hB R]

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
