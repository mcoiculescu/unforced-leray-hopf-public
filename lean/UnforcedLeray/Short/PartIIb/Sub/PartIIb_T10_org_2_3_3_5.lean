import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of

/-!
# `PartII-b:T10/org/2/3/3/5`: the cutoff curls are compactly supported solenoidal test fields

For smooth `A` and smooth compactly supported `χ`, the field `B = χ(·/n) A` (`n ≥ 1`) is smooth and
compactly supported, so `curl B` is smooth and compactly supported; it is divergence free because
`∂ⱼ(curl B)ⱼ = ∂ⱼ∂ⱼ₊₁ Bⱼ₊₂ - ∂ⱼ∂ⱼ₊₂ Bⱼ₊₁` and second derivatives of `B` commute.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Components of the first derivatives of a smooth vector field are smooth. -/
private theorem comp_fderiv_contDiff_aux5 {B : Space → CVec3} (hB : ContDiff ℝ ∞ B) (a c : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ)) c) :=
  (contDiff_piLp_apply (p := 2) (i := c)).comp
    ((ContDiff.fderiv_right (m := ∞) hB (by simp)).clm_apply contDiff_const)

/-- The complex curl of a smooth vector field is smooth. -/
private theorem curlC_contDiff_aux5 {B : Space → CVec3} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (curlC B) := by
  refine (contDiff_piLp 2).2 fun k => ?_
  show ContDiff ℝ ∞ (fun x => fderiv ℝ B x (EuclideanSpace.single (k + 1) (1 : ℝ)) (k + 2)
    - fderiv ℝ B x (EuclideanSpace.single (k + 2) (1 : ℝ)) (k + 1))
  exact (comp_fderiv_contDiff_aux5 hB (k + 1) (k + 2)).sub
    (comp_fderiv_contDiff_aux5 hB (k + 2) (k + 1))

/-- Compact support of a compactly supported field passes to its complex curl. -/
private theorem curlC_compact_aux5 {B : Space → CVec3} (hB : HasCompactSupport B) :
    HasCompactSupport (curlC B) := by
  refine HasCompactSupport.intro hB fun x hx => ?_
  have hd : fderiv ℝ B x = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hx).fderiv
  simp [curlC, hd]
  rfl

/-- The `k`-th component of the derivative of a vector field, in direction `v`. -/
private theorem fderiv_component_aux5 {Ψ : Space → CVec3} (y : Space)
    (hΨ : DifferentiableAt ℝ Ψ y) (k : Fin 3) (v : Space) :
    fderiv ℝ Ψ y v k = fderiv ℝ (fun x => Ψ x k) y v := by
  let L : CVec3 →L[ℝ] ℂ := ContinuousLinearMap.restrictScalars ℝ (EuclideanSpace.proj k)
  have hL : HasFDerivAt (fun x => L (Ψ x)) (L.comp (fderiv ℝ Ψ y)) y :=
    L.hasFDerivAt.comp y hΨ.hasFDerivAt
  have hfun : (fun x => Ψ x k) = fun x => L (Ψ x) := rfl
  rw [hfun, hL.fderiv]
  rfl

/-- Derivative of the coordinate derivative of `B` in a direction. -/
private theorem fderiv_clm_apply_aux5 {B : Space → CVec3} (hB : ContDiff ℝ ∞ B) (y v : Space)
    (a : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ))) y v =
      fderiv ℝ (fderiv ℝ B) y v (EuclideanSpace.single a (1 : ℝ)) := by
  have hd : Differentiable ℝ (fderiv ℝ B) :=
    (ContDiff.fderiv_right (m := ∞) hB (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ)))
      ((fderiv ℝ (fderiv ℝ B) y).flip (EuclideanSpace.single a (1 : ℝ))) y := by
    simpa using (hd y).hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single a (1 : ℝ)) y)
  rw [hx.fderiv]
  rfl

/-- Divergence of the complex curl of a smooth vector field vanishes. -/
private theorem div_curl_zero_aux5 {B : Space → CVec3} (hB : ContDiff ℝ ∞ B) (y : Space) :
    ∑ j : Fin 3, fderiv ℝ (curlC B) y (EuclideanSpace.single j (1 : ℝ)) j = 0 := by
  have hs : IsSymmSndFDerivAt ℝ B y := hB.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsym : ∀ v w : Space, fderiv ℝ (fderiv ℝ B) y v w = fderiv ℝ (fderiv ℝ B) y w v :=
    fun v w => hs.eq v w
  have hcomp2 : ∀ (a c : Fin 3) (v : Space),
      fderiv ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ)) c) y v =
        fderiv ℝ (fderiv ℝ B) y v (EuclideanSpace.single a (1 : ℝ)) c := by
    intro a c v
    have hDa : DifferentiableAt ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ))) y :=
      ((ContDiff.fderiv_right (m := ∞) hB (by simp)).clm_apply contDiff_const).differentiable
        (by simp) y
    rw [← fderiv_clm_apply_aux5 hB y v a]
    exact (fderiv_component_aux5 (Ψ := fun x => fderiv ℝ B x (EuclideanSpace.single a (1 : ℝ)))
      y hDa c v).symm
  have hcurl : ∀ j : Fin 3, fderiv ℝ (curlC B) y (EuclideanSpace.single j (1 : ℝ)) j =
      fderiv ℝ (fderiv ℝ B) y (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single (j + 1) (1 : ℝ)) (j + 2)
        - fderiv ℝ (fderiv ℝ B) y (EuclideanSpace.single j (1 : ℝ))
          (EuclideanSpace.single (j + 2) (1 : ℝ)) (j + 1) := by
    intro j
    have hΨ : DifferentiableAt ℝ (curlC B) y :=
      ((curlC_contDiff_aux5 hB).differentiable (by simp)) y
    have hP1 : DifferentiableAt ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single (j + 1) (1 : ℝ)) (j + 2)) y :=
      ((comp_fderiv_contDiff_aux5 hB (j + 1) (j + 2)).differentiable (by simp)) y
    have hP2 : DifferentiableAt ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single (j + 2) (1 : ℝ)) (j + 1)) y :=
      ((comp_fderiv_contDiff_aux5 hB (j + 2) (j + 1)).differentiable (by simp)) y
    rw [fderiv_component_aux5 y hΨ j]
    show fderiv ℝ (fun x => fderiv ℝ B x (EuclideanSpace.single (j + 1) (1 : ℝ)) (j + 2)
      - fderiv ℝ B x (EuclideanSpace.single (j + 2) (1 : ℝ)) (j + 1)) y
        (EuclideanSpace.single j (1 : ℝ)) = _
    rw [fderiv_fun_sub hP1 hP2, ContinuousLinearMap.sub_apply, hcomp2, hcomp2]
  rw [Finset.sum_congr rfl (fun j _ => hcurl j), Fin.sum_univ_three]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [hsym (EuclideanSpace.single 1 (1 : ℝ)) (EuclideanSpace.single 0 (1 : ℝ)),
    hsym (EuclideanSpace.single 2 (1 : ℝ)) (EuclideanSpace.single 0 (1 : ℝ)),
    hsym (EuclideanSpace.single 2 (1 : ℝ)) (EuclideanSpace.single 1 (1 : ℝ))]
  ring

theorem cutoffCurlSolTest_proof : UnforcedLeray.Short.IIb.CutoffCurlSolTest := by
  intro A hA χ hχ hχc n hn
  have hn0 : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity)
  have hψ : ContDiff ℝ ∞ (fun x : Space => (n : ℝ)⁻¹ • x) := contDiff_id.const_smul _
  have hχψ : ContDiff ℝ ∞ (fun x => χ ((n : ℝ)⁻¹ • x)) := hχ.comp hψ
  have hBs : ContDiff ℝ ∞ (fun x => χ ((n : ℝ)⁻¹ • x) • A x) := hχψ.smul hA
  have hχn : HasCompactSupport (fun x => χ ((n : ℝ)⁻¹ • x)) := hχc.comp_smul hn0
  have hBc : HasCompactSupport (fun x => χ ((n : ℝ)⁻¹ • x) • A x) := hχn.smul_right
  unfold SpatialSolTest
  exact ⟨curlC_contDiff_aux5 hBs, curlC_compact_aux5 hBc, div_curl_zero_aux5 hBs⟩

end UnforcedLeray.Short.IIb
