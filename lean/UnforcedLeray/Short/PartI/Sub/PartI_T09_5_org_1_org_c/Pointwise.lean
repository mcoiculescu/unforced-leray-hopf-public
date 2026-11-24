import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c
import UnforcedLeray.Units.B0151.Cell
import UnforcedLeray.Units.B0151.Linf
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs

/-!
# `PartI:T09/5/org/1/org/c/2`: pointwise age-continuity of the word derivatives of the train

Source: `the November 2 reference manuscript`,
lines 270-288 (`smooth_v`: the velocity is jointly smooth on `[0,infinity) x R^2`).

Proof outline.  Let `S = [0,infinity) x R^2` and let `G(s,z) = v(s,z)_k` be jointly `C^infinity`
on `S` (`IsTrain.smooth_v`).  The word derivative of the slice `z |-> G(s,z)` at a point of `S`
equals a nested within-`S` derivative `jointD w G (s,z)`, by induction on the word (each letter
is the slice derivative in the direction `(1,0)` or `(0,1)`, which is the within-`S` derivative
`fderiv_slice_apply`).  `jointD w G` is jointly `C^infinity` on `S`, hence continuous on `S`, so
`s |-> jointD w G (s,z)` is continuous within `[0,infinity)` at `s = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

namespace PointwiseAux

/-- The closed half-space `[0, infinity) x R^2` of `(s, z)`. -/
abbrev Sx : Set (ℝ × (ℝ × ℝ)) := Ici 0 ×ˢ (univ : Set (ℝ × ℝ))

lemma uniqueDiff_Sx : UniqueDiffOn ℝ Sx :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- Fixed-time slices of a function that is `C^1` on `S` are differentiable in the space
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

lemma fderiv_slice_apply {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ 1 g Sx) {t : ℝ} (ht : 0 ≤ t)
    (z e : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ => g (t, w)) z e = fderivWithin ℝ g Sx (t, z) (0, e) := by
  rw [(hasFDerivAt_slice hg ht z).fderiv]
  simp

/-- The within-`S` derivative in a fixed direction of a jointly `C^infinity` function is
jointly `C^infinity` on `S`. -/
lemma contDiffOn_fderivWithin_dir {g : ℝ × (ℝ × ℝ) → ℝ} (hg : ContDiffOn ℝ ∞ g Sx)
    (e : ℝ × (ℝ × ℝ)) : ContDiffOn ℝ ∞ (fun q => fderivWithin ℝ g Sx q e) Sx := by
  have hX : ContDiffOn ℝ ∞ (fderivWithin ℝ g Sx) Sx :=
    ((contDiffOn_infty_iff_fderivWithin uniqueDiff_Sx).1 hg).2
  have hA : ContDiff ℝ ∞ (ContinuousLinearMap.apply ℝ ℝ e) :=
    ContinuousLinearMap.contDiff _
  exact hA.comp_contDiffOn hX

/-- Direction of a letter: `true` is `∂_q` (`(1,0)`), `false` is `∂_η` (`(0,1)`). -/
def dirOf : Bool → ℝ × ℝ
  | true => (1, 0)
  | false => (0, 1)

/-- Nested within-`S` word derivatives; the head of the word is applied last, as in
`B0151.derivWord`. -/
def jointD : List Bool → (ℝ × (ℝ × ℝ) → ℝ) → (ℝ × (ℝ × ℝ) → ℝ)
  | [], G => G
  | b :: w, G => fun p => fderivWithin ℝ (jointD w G) Sx p (0, dirOf b)

lemma jointD_contDiffOn {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Sx) :
    ∀ w : List Bool, ContDiffOn ℝ ∞ (jointD w G) Sx
  | [] => hG
  | b :: w => by
      have h := jointD_contDiffOn hG w
      have e : jointD (b :: w) G = fun p => fderivWithin ℝ (jointD w G) Sx p (0, dirOf b) := rfl
      rw [e]
      exact contDiffOn_fderivWithin_dir h _

/-- The word derivative of a fixed-time slice equals the nested within-`S` derivative. -/
lemma derivWord_slice {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Sx) (w : List Bool) :
    ∀ {t : ℝ}, 0 ≤ t → ∀ z : ℝ × ℝ,
      B0151.derivWord w (fun x => G (t, x)) z = jointD w G (t, z) := by
  induction w with
  | nil => intro t ht z; rfl
  | cons b w ih =>
    intro t ht z
    have hw1 : ContDiffOn ℝ 1 (jointD w G) Sx := (jointD_contDiffOn hG w).of_le (by simp)
    have heq : B0151.derivWord w (fun x => G (t, x)) = fun x => jointD w G (t, x) :=
      funext fun x => ih ht x
    have hd : Differentiable ℝ (fun x => jointD w G (t, x)) :=
      fun x => (hasFDerivAt_slice hw1 ht x).differentiableAt
    cases b with
    | true =>
      show UnforcedLeray.GaussianVortex.partialX (B0151.derivWord w (fun x => G (t, x))) z =
        fderivWithin ℝ (jointD w G) Sx (t, z) (0, (1, 0))
      rw [heq, B0151.partialX_eq_fderiv hd z]
      exact fderiv_slice_apply hw1 ht z (1, 0)
    | false =>
      show UnforcedLeray.GaussianVortex.partialY (B0151.derivWord w (fun x => G (t, x))) z =
        fderivWithin ℝ (jointD w G) Sx (t, z) (0, (0, 1))
      rw [heq, B0151.partialY_eq_fderiv hd z]
      exact fderiv_slice_apply hw1 ht z (0, 1)

/-- Continuity within `[0, infinity)` at age `0` of the nested within-`S` derivatives. -/
lemma jointD_contWithin {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Sx) (w : List Bool)
    (z : ℝ × ℝ) :
    ContinuousWithinAt (fun s : ℝ => jointD w G (s, z)) (Ici 0) 0 := by
  have h1 : ContinuousWithinAt (jointD w G) Sx ((0 : ℝ), z) :=
    (jointD_contDiffOn hG w).continuousOn _ ⟨le_refl (0 : ℝ), mem_univ z⟩
  have h2 : ContinuousWithinAt (fun s : ℝ => ((s, z) : ℝ × (ℝ × ℝ))) (Ici 0) 0 :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  exact ContinuousWithinAt.comp (f := fun s : ℝ => ((s, z) : ℝ × (ℝ × ℝ))) (x := (0 : ℝ))
    h1 h2 (fun s hs => ⟨hs, mem_univ z⟩)

end PointwiseAux

/-- **Source fact (lines 270-288, `smooth_v`):** each word derivative of `v(s)` is continuous in
`z` for `s >= 0` and converges pointwise as `s -> 0+`. -/
theorem trainJetPointwiseAt0_proof : TrainJetPointwiseAt0 := by
  intro ν c hν hc tr _htr w k
  have hS : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) PointwiseAux.Sx :=
    tr.isTrain.smooth_v
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) PointwiseAux.Sx :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hS
  have hjoint : ∀ s : ℝ, 0 ≤ s → ∀ z : ℝ × ℝ,
      wordComp w (tr.v s) k z =
        PointwiseAux.jointD w (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (s, z) :=
    fun s hs z => PointwiseAux.derivWord_slice hG w hs z
  refine ⟨fun s hs => ?_, fun z => ?_⟩
  · have hv : ContDiff ℝ ∞ (tr.v s) := by
      have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
      exact contDiffOn_univ.1 h
    have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v s x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
    exact (B0151.contDiff_derivWord h1 w).continuous
  · have hc0 := PointwiseAux.jointD_contWithin hG w z
    have hc1 : Tendsto (fun s : ℝ => PointwiseAux.jointD w
        (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (s, z)) (nhdsWithin (0 : ℝ) (Ici 0))
        (𝓝 (PointwiseAux.jointD w (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (0, z))) := hc0
    have e1 : (fun s : ℝ => PointwiseAux.jointD w
        (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (s, z)) =ᶠ[nhdsWithin (0 : ℝ) (Ici 0)]
        (fun s : ℝ => wordComp w (tr.v s) k z) :=
      eventually_nhdsWithin_of_forall fun s hs => (hjoint s hs z).symm
    have e0 : wordComp w (tr.v 0) k z =
        PointwiseAux.jointD w (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) (0, z) :=
      hjoint 0 le_rfl z
    rw [e0]
    exact hc1.congr' e1

end UnforcedLeray.Short.PartI
