import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_2
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Part I, `PartI:T04/10/1/2/2/1`: the curl jet bound

Source of record: `the November 2 reference manuscript`, lines 285-288.
`Cyl.curl u z = ∂_q (u z).2 - ∂_η (u z).1` is `cbCurlLam ∘ fderiv ℝ u` for a fixed continuous
linear functional `cbCurlLam` of norm `≤ 2`, so `‖D^k curl u‖ ≤ 2 ‖D^{k+1} u‖`.

Statement: `curlJetBound_proof : CurlJetBound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The linear functional `T ↦ T(1,0)₁ - T(0,1)₀` on the derivative space. -/
def cbCurlLam : (Plane →L[ℝ] Vec) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 2)) ((1 : ℝ), (0 : ℝ))) -
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 2)) ((0 : ℝ), (1 : ℝ)))

theorem cbCurlLam_apply (T : Plane →L[ℝ] Vec) :
    cbCurlLam T = T (1, 0) 1 - T (0, 1) 0 := rfl

theorem norm_cbCurlLam_le : ‖cbCurlLam‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun T => ?_)
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have ha : ‖T (1, 0) 1‖ ≤ ‖T‖ := by
    have h1 := PiLp.norm_apply_le (T (1, 0)) 1
    have h2 := T.le_opNorm ((1 : ℝ), (0 : ℝ))
    have h3 : ‖T‖ * ‖((1 : ℝ), (0 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h10 (norm_nonneg _)
    linarith
  have hb : ‖T (0, 1) 0‖ ≤ ‖T‖ := by
    have h1 := PiLp.norm_apply_le (T (0, 1)) 0
    have h2 := T.le_opNorm ((0 : ℝ), (1 : ℝ))
    have h3 : ‖T‖ * ‖((0 : ℝ), (1 : ℝ))‖ ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left h01 (norm_nonneg _)
    linarith
  rw [cbCurlLam_apply]
  have := norm_sub_le (T (1, 0) 1) (T (0, 1) 0)
  rw [Real.norm_eq_abs] at this ha hb ⊢
  have ha' : |T (1, 0) 1| ≤ ‖T‖ := ha
  have hb' : |T (0, 1) 0| ≤ ‖T‖ := hb
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hsub : |T (1, 0) 1 - T (0, 1) 0| ≤ |T (1, 0) 1| + |T (0, 1) 0| := abs_sub _ _
  nlinarith [hsub, ha', hb', hT]

theorem curlJetBound_proof : CurlJetBound := by
  intro k
  refine ⟨2, by norm_num, ?_⟩
  intro u hu z
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hfun : UnforcedLeray.Cyl.curl u = fun w => cbCurlLam (fderiv ℝ u w) := by
    funext w
    have h0 : HasDerivAt (fun q : ℝ => (q, w.2)) ((1 : ℝ), (0 : ℝ)) w.1 :=
      (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
    have h0' : HasDerivAt (fun η : ℝ => (w.1, η)) ((0 : ℝ), (1 : ℝ)) w.2 :=
      (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
    have h1 : HasDerivAt (fun q : ℝ => u (q, w.2)) (fderiv ℝ u (w.1, w.2) (1, 0)) w.1 :=
      (hdiff (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.1 h0
    have h1' : HasDerivAt (fun η : ℝ => u (w.1, η)) (fderiv ℝ u (w.1, w.2) (0, 1)) w.2 :=
      (hdiff (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.2 h0'
    have h2 : HasDerivAt (fun q : ℝ => u (q, w.2) 1)
        ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (w.1, w.2) (1, 0))) w.1 :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        w.1 h1
    have h2' : HasDerivAt (fun η : ℝ => u (w.1, η) 0)
        ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (w.1, w.2) (0, 1))) w.2 :=
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        w.2 h1'
    have e1 : UnforcedLeray.Cyl.partialQ (fun x => u x 1) w =
        fderiv ℝ u w (1, 0) 1 := h2.deriv
    have e2 : UnforcedLeray.Cyl.partialEta (fun x => u x 0) w =
        fderiv ℝ u w (0, 1) 0 := h2'.deriv
    unfold UnforcedLeray.Cyl.curl
    rw [e1, e2, cbCurlLam_apply]
  have hcomp : (cbCurlLam ∘ fderiv ℝ u) = UnforcedLeray.Cyl.curl u := by
    rw [hfun]; rfl
  have hiter : iteratedFDeriv ℝ k (UnforcedLeray.Cyl.curl u) z =
      cbCurlLam.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ u) z) := by
    rw [← hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left cbCurlLam
      (hg.contDiffAt) (by exact_mod_cast le_top)
  rw [hiter]
  have hnorm := ContinuousLinearMap.norm_compContinuousMultilinearMap_le cbCurlLam
    (iteratedFDeriv ℝ k (fderiv ℝ u) z)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  calc _ ≤ ‖cbCurlLam‖ * ‖iteratedFDeriv ℝ (k + 1) u z‖ := hnorm
    _ ≤ 2 * ‖iteratedFDeriv ℝ (k + 1) u z‖ :=
        mul_le_mul_of_nonneg_right norm_cbCurlLam_le (norm_nonneg _)

end UnforcedLeray.Short.PartI

end
