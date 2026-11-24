import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Part I, `PartI:T04/10/1/2/2/3`: measurability in time of the cutoff vorticity jet energy

Source of record: `the November 2 reference manuscript`, lines 285-288.
The integrand `(r,z) ↦ η_R(z₂) ‖D^k curl v(r)(z)‖²` is continuous on the open set
`Ioo 0 T ×ˢ univ`, because the slices of a jointly smooth `v` have iterated derivatives given by
the joint ones composed with `inr`; Fubini-type measurability then gives the a.e. measurability.

Statement: `cutoffVortJetMeasurable_proof : CutoffVortJetMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The curl is the composition with `cbCurlLam` of the derivative. -/
theorem cm_curl_eq (u : Plane → Vec) (hu : ContDiff ℝ ∞ u) :
    UnforcedLeray.Cyl.curl u = fun w => cbCurlLam (fderiv ℝ u w) := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
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

/-- Slices of a function that is smooth on an open set: the iterated derivative of the slice
`w ↦ F (x.1, w)` at `x.2` is the joint iterated derivative at `x` composed with `inr`. -/
theorem cm_slice_iteratedFDeriv {F : ℝ × Plane → Vec} {U : Set (ℝ × Plane)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (m : ℕ) (x : ℝ × Plane) (hx : x ∈ U) :
    iteratedFDeriv ℝ m (fun w : Plane => F (x.1, w)) x.2 =
      (iteratedFDeriv ℝ m F x).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane) := by
  have hxe : (ContinuousLinearMap.inr ℝ ℝ Plane x.2) + ((x.1, 0) : ℝ × Plane) = x := by
    ext <;> simp
  have hfun : (fun w : Plane => F (x.1, w)) =
      (fun p : ℝ × Plane => F (p + (x.1, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ Plane) := by
    funext w
    simp
  have hU' : IsOpen ((fun p : ℝ × Plane => p + (x.1, 0)) ⁻¹' U) :=
    hU.preimage (continuous_id.add continuous_const)
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => F (p + (x.1, 0)))
      ((fun p : ℝ × Plane => p + (x.1, 0)) ⁻¹' U) :=
    hF.comp ((contDiff_id.add contDiff_const).contDiffOn) (fun p hp => hp)
  have hmem : (ContinuousLinearMap.inr ℝ ℝ Plane x.2) ∈
      (fun p : ℝ × Plane => p + (x.1, 0)) ⁻¹' U := by
    show (ContinuousLinearMap.inr ℝ ℝ Plane x.2) + (x.1, 0) ∈ U
    rw [hxe]
    exact hx
  have hopen2 : IsOpen ((ContinuousLinearMap.inr ℝ ℝ Plane) ⁻¹'
      ((fun p : ℝ × Plane => p + (x.1, 0)) ⁻¹' U)) :=
    hU'.preimage (ContinuousLinearMap.inr ℝ ℝ Plane).continuous
  have hmem2 : x.2 ∈ (ContinuousLinearMap.inr ℝ ℝ Plane) ⁻¹'
      ((fun p : ℝ × Plane => p + (x.1, 0)) ⁻¹' U) := hmem
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inr ℝ ℝ Plane) hG hU'.uniqueDiffOn hopen2.uniqueDiffOn hmem
    (i := m) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m hopen2 hmem2,
    iteratedFDerivWithin_of_isOpen m hU' hmem] at key
  have hG2 : iteratedFDeriv ℝ m (fun p : ℝ × Plane => F (p + (x.1, 0)))
      (ContinuousLinearMap.inr ℝ ℝ Plane x.2) = iteratedFDeriv ℝ m F x := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) m ((x.1, 0) : ℝ × Plane)
      (ContinuousLinearMap.inr ℝ ℝ Plane x.2)
    rw [hxe] at h
    exact h
  rw [hfun, key, hG2]

/-- Joint continuity of the slice-derivative operator on an open set. -/
theorem cm_continuousOn_slice {F : ℝ × Plane → Vec} {U : Set (ℝ × Plane)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (m : ℕ) :
    ContinuousOn (fun x : ℝ × Plane =>
      (iteratedFDeriv ℝ m F x).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)) U := by
  have h1 : ContinuousOn (iteratedFDeriv ℝ m F) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hF hU (by exact_mod_cast le_top)
  have h2 : Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × Plane) Vec =>
      M.compContinuousLinearMap (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ Plane)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ Plane)).continuous
  exact h2.comp_continuousOn h1

/-- Smoothness of a slice of a classical solution on `[0,T]`. -/
theorem cm_slice_contDiff {F : ℝ × Plane → Vec} {T : ℝ} (hFs : ContDiffOn ℝ ∞ F (Icc 0 T ×ˢ univ))
    (v : ℝ → Plane → Vec) (hFv : ∀ r w, F (r, w) = v r w) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (v r) := by
  have h := hFs.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
    (fun z _ => (⟨hr, mem_univ z⟩ : (r, z) ∈ Icc 0 T ×ˢ univ))
  have h' : ContDiffOn ℝ ∞ (fun z => F (r, z)) univ := h
  have hvr : (fun z => F (r, z)) = v r := funext (hFv r)
  rw [hvr] at h'
  exact contDiffOn_univ.1 h'

theorem cutoffVortJetMeasurable_proof : CutoffVortJetMeasurable := by
  intro ν c T v p hν hc hcls k R
  have hcl := hcls.classical
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × Plane → Vec, F = fun x => v x.1 x.2 := ⟨_, rfl⟩
  have hFv : ∀ r w, F (r, w) = v r w := fun r w => by rw [hFdef]
  have hFs : ContDiffOn ℝ ∞ F (Icc 0 T ×ˢ univ) := by
    rw [hFdef]; exact hcl.smooth_v
  have hU : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hFU : ContDiffOn ℝ ∞ F (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hFs.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hCE : Continuous (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec) :=
    (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec).continuous
  have hLL : Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Plane)
      (Plane →L[ℝ] Vec) => cbCurlLam.compContinuousMultilinearMap M) :=
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Plane)
      (Plane →L[ℝ] Vec) ℝ cbCurlLam).continuous
  have hMx := cm_continuousOn_slice hU hFU (k + 1)
  have hA : ContinuousOn (fun x : ℝ × Plane =>
      cbCurlLam.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec
        ((iteratedFDeriv ℝ (k + 1) F x).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)))) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (hLL.comp hCE).comp_continuousOn hMx
  have hη : Continuous (fun x : ℝ × Plane => etaCutoff R x.2.2) :=
    (cuEtaCutoffContinuous R).comp continuous_snd
  have hΦ : ContinuousOn (fun x : ℝ × Plane => etaCutoff R x.2.2 *
      ‖cbCurlLam.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec
        ((iteratedFDeriv ℝ (k + 1) F x).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)))‖ ^ 2)
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hη.continuousOn.mul (hA.norm.pow 2)
  have hEq : EqOn (fun x : ℝ × Plane => etaCutoff R x.2.2 *
      ‖iteratedFDeriv ℝ k (Cyl.curl (v x.1)) x.2‖ ^ 2)
      (fun x : ℝ × Plane => etaCutoff R x.2.2 *
      ‖cbCurlLam.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec
        ((iteratedFDeriv ℝ (k + 1) F x).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)))‖ ^ 2)
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    rintro ⟨r, z⟩ hx
    have hr : r ∈ Icc (0 : ℝ) T := ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩
    have hv : ContDiff ℝ ∞ (v r) := cm_slice_contDiff hFs v hFv hr
    have hdv : ContDiff ℝ ∞ (fun w => fderiv ℝ (v r) w) :=
      (contDiff_infty_iff_fderiv.mp hv).2
    have e1 : iteratedFDeriv ℝ k (Cyl.curl (v r)) z =
        cbCurlLam.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k (fun w => fderiv ℝ (v r) w) z) := by
      rw [cm_curl_eq (v r) hv]
      exact ContinuousLinearMap.iteratedFDeriv_comp_left cbCurlLam hdv.contDiffAt
        (by exact_mod_cast le_top)
    have e2 : iteratedFDeriv ℝ k (fun w => fderiv ℝ (v r) w) z =
        continuousMultilinearCurryRightEquiv' ℝ k Plane Vec (iteratedFDeriv ℝ (k + 1) (v r) z) := by
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    have e3 : iteratedFDeriv ℝ (k + 1) (v r) z =
        (iteratedFDeriv ℝ (k + 1) F (r, z)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane) := by
      have hvF : v r = fun w => F (r, w) := funext fun w => (hFv r w).symm
      rw [hvF]
      exact cm_slice_iteratedFDeriv hU hFU (k + 1) (r, z) hx
    show etaCutoff R z.2 * ‖iteratedFDeriv ℝ k (Cyl.curl (v r)) z‖ ^ 2 =
      etaCutoff R z.2 * ‖cbCurlLam.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ k Plane Vec
        ((iteratedFDeriv ℝ (k + 1) F (r, z)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)))‖ ^ 2
    rw [e1, e2, e3]
  have hFn : ContinuousOn (fun x : ℝ × Plane => etaCutoff R x.2.2 *
      ‖iteratedFDeriv ℝ k (Cyl.curl (v x.1)) x.2‖ ^ 2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hΦ.congr hEq
  have hcellm : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hae : Ioo (0 : ℝ) T =ᵐ[volume] Icc (0 : ℝ) T := Ioo_ae_eq_Icc
  have hint : AEStronglyMeasurable (fun r : ℝ => ∫ z, (fun x : ℝ × Plane => etaCutoff R x.2.2 *
      ‖iteratedFDeriv ℝ k (Cyl.curl (v x.1)) x.2‖ ^ 2) (r, z) ∂(volume.restrict (Cyl.cell c)))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
    refine AEStronglyMeasurable.integral_prod_right'
      (f := fun x : ℝ × Plane => etaCutoff R x.2.2 * ‖iteratedFDeriv ℝ k (Cyl.curl (v x.1)) x.2‖ ^ 2) ?_
    rw [show (volume.restrict (Ioo (0 : ℝ) T)).prod (volume.restrict (Cyl.cell c)) =
        volume.restrict (Ioo (0 : ℝ) T ×ˢ Cyl.cell c) from Measure.prod_restrict _ _]
    exact (hFn.mono (prod_mono subset_rfl (subset_univ _))).aestronglyMeasurable
      (measurableSet_Ioo.prod hcellm)
  rw [← Measure.restrict_congr_set hae]
  exact hint

end UnforcedLeray.Short.PartI

end
