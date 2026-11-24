import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Part III-a, `PartIII-a:T21/2/6/11`: jets of the curl

Source of record: `the November 2 reference manuscript`, calculus with
`curl u = ∂_q u₂ - ∂_η u₁` (SP 2875-2896 conventions).  The scalar curl of a smooth
`u : ℝ × ℝ → ℝ²` is `Λ ∘ Du`, where `Λ T = T(1,0)₁ - T(0,1)₀` is a continuous linear functional of
norm `≤ 2` on the derivative space.  Hence `‖D^j curl u‖ ≤ 2‖D^{j+1} u‖`.

Statement: `CurlJetBound`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The linear functional `T ↦ T(1,0)₁ - T(0,1)₀` on the derivative space. -/
noncomputable def curlLam :
    (ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 2)) ((1 : ℝ), (0 : ℝ))) -
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 2)) ((0 : ℝ), (1 : ℝ)))

theorem curlLam_apply (T : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    curlLam T = T (1, 0) 1 - T (0, 1) 0 := rfl

theorem norm_curlLam_le : ‖curlLam‖ ≤ 2 := by
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
  rw [curlLam_apply]
  have := norm_sub_le (T (1, 0) 1) (T (0, 1) 0)
  rw [Real.norm_eq_abs] at this ha hb ⊢
  have ha' : |T (1, 0) 1| ≤ ‖T‖ := ha
  have hb' : |T (0, 1) 0| ≤ ‖T‖ := hb
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hsub : |T (1, 0) 1 - T (0, 1) 0| ≤ |T (1, 0) 1| + |T (0, 1) 0| := abs_sub _ _
  nlinarith [hsub, ha', hb', hT]

theorem curlJetBound : CurlJetBound := by
  intro u hu j x
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hfun : UnforcedLeray.Cyl.curl u = fun z => curlLam (fderiv ℝ u z) := by
    funext z
    have h0 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    have h0' : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    have h1 : HasDerivAt (fun q : ℝ => u (q, z.2)) (fderiv ℝ u (z.1, z.2) (1, 0)) z.1 :=
      (hdiff (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h0
    have h1' : HasDerivAt (fun η : ℝ => u (z.1, η)) (fderiv ℝ u (z.1, z.2) (0, 1)) z.2 :=
      (hdiff (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h0'
    have h2 : HasDerivAt (fun q : ℝ => u (q, z.2) 1)
        ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (z.1, z.2) (1, 0))) z.1 :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        z.1 h1
    have h2' : HasDerivAt (fun η : ℝ => u (z.1, η) 0)
        ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (z.1, z.2) (0, 1))) z.2 :=
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        z.2 h1'
    have e1 : UnforcedLeray.Cyl.partialQ (fun w => u w 1) z =
        fderiv ℝ u z (1, 0) 1 := h2.deriv
    have e2 : UnforcedLeray.Cyl.partialEta (fun w => u w 0) z =
        fderiv ℝ u z (0, 1) 0 := h2'.deriv
    unfold UnforcedLeray.Cyl.curl
    rw [e1, e2, curlLam_apply]
  have hcomp : (curlLam ∘ fderiv ℝ u) = UnforcedLeray.Cyl.curl u := by
    rw [hfun]; rfl
  have hiter : iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl u) x =
      curlLam.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ u) x) := by
    rw [← hcomp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left curlLam
      (hg.contDiffAt) (by exact_mod_cast le_top)
  rw [hiter]
  have hnorm := ContinuousLinearMap.norm_compContinuousMultilinearMap_le curlLam
    (iteratedFDeriv ℝ j (fderiv ℝ u) x)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  calc _ ≤ ‖curlLam‖ * ‖iteratedFDeriv ℝ (j + 1) u x‖ := hnorm
    _ ≤ 2 * ‖iteratedFDeriv ℝ (j + 1) u x‖ :=
        mul_le_mul_of_nonneg_right norm_curlLam_le (norm_nonneg _)

end UnforcedLeray.Short.IIIa
