import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX

/-!
# Joint continuity of the train velocity and of `∇E` on `[0, ∞) × ℝ²` (SP 3074-3075)

`IsTrain.smooth_v` gives joint smoothness of `v` on `[0, ∞) × ℝ²` (one-sided at `s = 0`). For a
jointly `C^∞` function `g` on `S = [0, ∞) × ℝ²`, the fixed-time derivative in the space
variable is the within-`S` derivative in the direction `(0, e)` (`fderiv_slice_apply`), so the
second space derivatives needed for `pd k (Ec tr s)` are within-`S` derivatives of a jointly
`C^1` function, hence jointly continuous on `S` (`continuousOn_second`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GCont3Aux

/-- The closed half-space `[0, ∞) × ℝ²` of `(s, z)`. -/
abbrev Sx : Set (ℝ × (ℝ × ℝ)) := Ici 0 ×ˢ (univ : Set (ℝ × ℝ))

lemma uniqueDiff_Sx : UniqueDiffOn ℝ Sx :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- Fixed-time slices of a function that is `C¹` on `S` are differentiable in the space
variable, with the within-`S` derivative in the direction `(0, ·)`. -/
lemma hasFDerivAt_slice {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ 1 g Sx) {t : ℝ} (ht : 0 ≤ t)
    (z : ℝ × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => g (t, w))
      ((fderivWithin ℝ g Sx (t, z)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z := by
  have hdiff : DifferentiableWithinAt ℝ g Sx (t, z) :=
    (hg.differentiableOn (by norm_num)) (t, z) ⟨ht, mem_univ z⟩
  have hline : HasFDerivAt (fun w : ℝ × ℝ => ((t, w) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  have hmaps : MapsTo (fun w : ℝ × ℝ => ((t, w) : ℝ × (ℝ × ℝ))) univ Sx :=
    fun w _ => ⟨ht, mem_univ w⟩
  have hc := hdiff.hasFDerivWithinAt.comp z hline.hasFDerivWithinAt hmaps
  exact hc.hasFDerivAt univ_mem

lemma fderiv_sub_of_hasFDerivAt {f g : ℝ × ℝ → ℝ} {f' g' : (ℝ × ℝ) →L[ℝ] ℝ} {z : ℝ × ℝ}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    fderiv ℝ (fun w => f w - g w) z = f' - g' :=
  (hf.sub hg).fderiv

lemma fderiv_slice_apply {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ 1 g Sx) {t : ℝ} (ht : 0 ≤ t)
    (z e : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ => g (t, w)) z e = fderivWithin ℝ g Sx (t, z) (0, e) := by
  rw [(hasFDerivAt_slice hg ht z).fderiv]
  simp

lemma contDiffOn_fderivWithin_apply {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ ∞ g Sx)
    (e : ℝ × (ℝ × ℝ)) : ContDiffOn ℝ 1 (fun q => fderivWithin ℝ g Sx q e) Sx := by
  have hg2 : ContDiffOn ℝ 2 g Sx := hg.of_le (by simp)
  have hX : ContDiffOn ℝ 1 (fderivWithin ℝ g Sx) Sx :=
    hg2.fderivWithin uniqueDiff_Sx (by norm_num)
  have hA : ContDiff ℝ 1 (ContinuousLinearMap.apply ℝ ℝ e) :=
    ContinuousLinearMap.contDiff _
  exact hA.comp_contDiffOn hX

lemma continuousOn_second {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ ∞ g Sx) (e v : ℝ × (ℝ × ℝ)) :
    ContinuousOn (fun p => fderivWithin ℝ (fun q => fderivWithin ℝ g Sx q e) Sx p v) Sx := by
  have h1 := contDiffOn_fderivWithin_apply hg e
  have h2 : ContinuousOn (fderivWithin ℝ (fun q => fderivWithin ℝ g Sx q e) Sx) Sx :=
    h1.continuousOn_fderivWithin uniqueDiff_Sx le_rfl
  exact (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn h2

end GCont3Aux

open GCont3Aux in
/-- Joint continuity on `[0, ∞) × ℝ²` of the train velocity and of `∂_k E_c`. -/
theorem train_joint_cont {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) ∧ ∀ k : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (fun x => UnforcedLeray.B0238.Ec tr p.1 x) p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  have hS : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) Sx := tr.isTrain.smooth_v
  refine ⟨hS.continuousOn, fun k => ?_⟩
  have hG : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) Sx := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hS
  -- the vorticity as a combination of within-`S` derivatives
  have hEc : ∀ t : ℝ, 0 ≤ t → UnforcedLeray.B0238.Ec tr t = fun z =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx (t, z) (0, (1, 0)) -
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx (t, z) (0, (0, 1)) := by
    intro t ht
    funext z
    have hv : ContDiff ℝ ∞ (tr.v t) := UnforcedLeray.B0238.contDiff_Vc tr ht
    have hv1 : ContDiff ℝ 1 (tr.v t) := hv.of_le (by simp)
    have e1 : fderiv ℝ (fun w : ℝ × ℝ => tr.v t w 1) z (1, 0) =
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx (t, z) (0, (1, 0)) :=
      fderiv_slice_apply ((hG 1).of_le (by simp)) ht z (1, 0)
    have e0 : fderiv ℝ (fun w : ℝ × ℝ => tr.v t w 0) z (0, 1) =
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx (t, z) (0, (0, 1)) :=
      fderiv_slice_apply ((hG 0).of_le (by simp)) ht z (0, 1)
    unfold UnforcedLeray.B0238.Ec
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z, e1, e0]
  -- the second derivatives, pointwise
  have hid' : ∀ (t : ℝ) (z : ℝ × ℝ), 0 ≤ t →
      B0579.pd k (fun x => UnforcedLeray.B0238.Ec tr t x) z =
        fderivWithin ℝ (fun q => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx q
            (0, (1, 0))) Sx (t, z) (0, B0579.dir k) -
          fderivWithin ℝ (fun q => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx q
            (0, (0, 1))) Sx (t, z) (0, B0579.dir k) := by
    intro t z ht
    have hD1 : ContDiffOn ℝ 1 (fun q => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) Sx q
        (0, (1, 0))) Sx := contDiffOn_fderivWithin_apply (hG 1) (0, (1, 0))
    have hD0 : ContDiffOn ℝ 1 (fun q => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) Sx q
        (0, (0, 1))) Sx := contDiffOn_fderivWithin_apply (hG 0) (0, (0, 1))
    have hA := hasFDerivAt_slice hD1 ht z
    have hB := hasFDerivAt_slice hD0 ht z
    unfold B0579.pd
    simp only [hEc t ht]
    rw [fderiv_sub_of_hasFDerivAt hA hB, ContinuousLinearMap.sub_apply]
    simp
  refine ContinuousOn.congr ((continuousOn_second (hG 1) (0, (1, 0)) (0, B0579.dir k)).sub
    (continuousOn_second (hG 0) (0, (0, 1)) (0, B0579.dir k))) ?_
  intro p hp
  exact hid' p.1 p.2 hp.1
