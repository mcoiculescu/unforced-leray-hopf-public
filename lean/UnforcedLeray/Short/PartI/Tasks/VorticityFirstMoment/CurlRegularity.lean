import UnforcedLeray.Short.PartI.Sub.T02_4
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `VorticityFirstMoment`: regularity of the curl (`CurlRegularity`)

Source of record: `the November 2 reference manuscript`, lines 276-288.

The target `CurlRegularity` (`Short/PartI/Sub/T02_4.lean`) asks, for a smooth `c`-periodic velocity
`v` with bounded spatial derivatives on `[0,T]`, that the vorticity `curl v` is

* (a) continuous on `[0,T] × ℝ²`;
* (b) `C²` on `(0,T) × ℝ²`;
* (c) bounded on `[0,T] × ℝ²`;
* (d) `c`-periodic in `q` at every time `s ∈ [0,T]`.

Proof outline.  The space-time components `crFc v k (s,z) = v s z k` are smooth on the closed strip
`S = [0,T] × ℝ²`.  Every slice `q ↦ (s,(q,η))` and `η ↦ (s,(q,η))` lies in `S` for `s ∈ [0,T]`, so
the classical partials of `v s` are the within-derivatives of the components on `S`
(`crDerivQ`, `crDerivE`).  This gives (a) by continuity of `fderivWithin` on the convex strip
(`ContDiffOn.continuousOn_fderivWithin`), and (b) by the open-set version of the same identity.
For (c), the slice `v s` is differentiable on the whole plane and the `k = 1` bound of
`HasBoundedDerivsOn` bounds its derivative.  For (d), periodicity passes through the partials.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The `k`-th component of a space-time velocity field, as a function of `(s, z)`. -/
def crFc (v : ℝ → Plane → Vec) (k : Fin 2) : ℝ × Plane → ℝ := fun x => v x.1 x.2 k

/-- The `∂_q` direction in the space-time coordinates `(s, (q, η))`. -/
def crEQ : ℝ × Plane := (0, (1, 0))

/-- The `∂_η` direction in the space-time coordinates `(s, (q, η))`. -/
def crEE : ℝ × Plane := (0, (0, 1))

theorem crFc_contDiffOn {v : ℝ → Plane → Vec} {S : Set (ℝ × Plane)}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) S) (k : Fin 2) :
    ContDiffOn ℝ ∞ (crFc v k) S :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hv

/-- Along the `q`-line `q ↦ (s,(q,η))`, which lies in `S`, the `q`-derivative of `F` is its
within-derivative in the direction `∂_q`. -/
theorem crDerivQ {F : ℝ × Plane → ℝ} {S : Set (ℝ × Plane)} {L : (ℝ × Plane) →L[ℝ] ℝ}
    {s : ℝ} {z : Plane} (hF : HasFDerivWithinAt F L S (s, z))
    (hS : ∀ q : ℝ, ((s, (q, z.2)) : ℝ × Plane) ∈ S) :
    deriv (fun q : ℝ => F (s, (q, z.2))) z.1 = L crEQ := by
  have hline : HasDerivAt (fun q : ℝ => ((s, (q, z.2)) : ℝ × Plane)) crEQ z.1 :=
    (hasDerivAt_const z.1 s).prodMk ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hcomp : HasDerivWithinAt (F ∘ fun q : ℝ => ((s, (q, z.2)) : ℝ × Plane)) (L crEQ)
      univ z.1 :=
    hF.comp_hasDerivWithinAt z.1 hline.hasDerivWithinAt (fun q _ => hS q)
  exact (hasDerivWithinAt_univ.mp hcomp).deriv

/-- Along the `η`-line `η ↦ (s,(q,η))`, which lies in `S`, the `η`-derivative of `F` is its
within-derivative in the direction `∂_η`. -/
theorem crDerivE {F : ℝ × Plane → ℝ} {S : Set (ℝ × Plane)} {L : (ℝ × Plane) →L[ℝ] ℝ}
    {s : ℝ} {z : Plane} (hF : HasFDerivWithinAt F L S (s, z))
    (hS : ∀ η : ℝ, ((s, (z.1, η)) : ℝ × Plane) ∈ S) :
    deriv (fun η : ℝ => F (s, (z.1, η))) z.2 = L crEE := by
  have hline : HasDerivAt (fun η : ℝ => ((s, (z.1, η)) : ℝ × Plane)) crEE z.2 :=
    (hasDerivAt_const z.2 s).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have hcomp : HasDerivWithinAt (F ∘ fun η : ℝ => ((s, (z.1, η)) : ℝ × Plane)) (L crEE)
      univ z.2 :=
    hF.comp_hasDerivWithinAt z.2 hline.hasDerivWithinAt (fun η _ => hS η)
  exact (hasDerivWithinAt_univ.mp hcomp).deriv

/-- The curl of a slice `v s`, `s ∈ [0,T]`, as within-derivatives of the components on the closed
strip `[0,T] × ℝ²`. -/
theorem crCurl_within {v : ℝ → Plane → Vec} {T s : ℝ} {z : Plane}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)))
    (hs : s ∈ Icc 0 T) :
    Cyl.curl (v s) z =
      fderivWithin ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) crEQ -
        fderivWithin ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) crEE := by
  have hmem : ((s, z) : ℝ × Plane) ∈ Icc 0 T ×ˢ (univ : Set Plane) := ⟨hs, mem_univ _⟩
  have hd1 : DifferentiableWithinAt ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) :=
    (crFc_contDiffOn hv 1).differentiableOn (by simp) _ hmem
  have hd0 : DifferentiableWithinAt ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) :=
    (crFc_contDiffOn hv 0).differentiableOn (by simp) _ hmem
  have h1 : Cyl.partialQ (fun w => v s w 1) z =
      fderivWithin ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) crEQ :=
    crDerivQ hd1.hasFDerivWithinAt (fun q => ⟨hs, mem_univ _⟩)
  have h0 : Cyl.partialEta (fun w => v s w 0) z =
      fderivWithin ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) (s, z) crEE :=
    crDerivE hd0.hasFDerivWithinAt (fun η => ⟨hs, mem_univ _⟩)
  show Cyl.partialQ (fun w => v s w 1) z - Cyl.partialEta (fun w => v s w 0) z = _
  rw [h1, h0]

/-- Part (a): the vorticity is continuous on the closed strip `[0,T] × ℝ²`. -/
theorem crContinuous {v : ℝ → Plane → Vec} {T : ℝ} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContinuousOn (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (Icc 0 T ×ˢ (univ : Set Plane)) := by
  have huniq : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Plane)) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) uniqueDiffOn_univ
  have hc1 : ContinuousOn (fderivWithin ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)))
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (crFc_contDiffOn hv 1).continuousOn_fderivWithin huniq (by simp)
  have hc0 : ContinuousOn (fderivWithin ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)))
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (crFc_contDiffOn hv 0).continuousOn_fderivWithin huniq (by simp)
  have hcont : ContinuousOn (fun x : ℝ × Plane =>
      fderivWithin ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) x crEQ -
        fderivWithin ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) x crEE)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (hc1.clm_apply continuousOn_const).sub (hc0.clm_apply continuousOn_const)
  refine hcont.congr ?_
  intro x hx
  exact crCurl_within hv hx.1

/-- The curl on the open strip `(0,T) × ℝ²` as a difference of ordinary space-time directional
derivatives of the components. -/
theorem crCurl_open {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : s ∈ Ioo 0 T) (z : Plane) :
    Cyl.curl (v s) z = fderiv ℝ (crFc v 1) (s, z) crEQ - fderiv ℝ (crFc v 0) (s, z) crEE := by
  have hU : IsOpen (Ioo 0 T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo 0 T ×ˢ (univ : Set Plane) ⊆ Icc 0 T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self subset_rfl
  have hmem : ((s, z) : ℝ × Plane) ∈ Ioo 0 T ×ˢ (univ : Set Plane) := ⟨hs, mem_univ _⟩
  have hF1 : ContDiffAt ℝ ∞ (crFc v 1) (s, z) :=
    ((crFc_contDiffOn hv 1).mono hsub).contDiffAt (hU.mem_nhds hmem)
  have hF0 : ContDiffAt ℝ ∞ (crFc v 0) (s, z) :=
    ((crFc_contDiffOn hv 0).mono hsub).contDiffAt (hU.mem_nhds hmem)
  have hW1 : HasFDerivWithinAt (crFc v 1) (fderiv ℝ (crFc v 1) (s, z))
      (Ioo 0 T ×ˢ (univ : Set Plane)) (s, z) :=
    (hF1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hW0 : HasFDerivWithinAt (crFc v 0) (fderiv ℝ (crFc v 0) (s, z))
      (Ioo 0 T ×ˢ (univ : Set Plane)) (s, z) :=
    (hF0.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have h1 : Cyl.partialQ (fun w => v s w 1) z = fderiv ℝ (crFc v 1) (s, z) crEQ :=
    crDerivQ hW1 (fun q => ⟨hs, mem_univ _⟩)
  have h0 : Cyl.partialEta (fun w => v s w 0) z = fderiv ℝ (crFc v 0) (s, z) crEE :=
    crDerivE hW0 (fun η => ⟨hs, mem_univ _⟩)
  show Cyl.partialQ (fun w => v s w 1) z - Cyl.partialEta (fun w => v s w 0) z = _
  rw [h1, h0]

/-- Part (b): the vorticity is `C²` (indeed `C^∞`) on the open strip `(0,T) × ℝ²`. -/
theorem crSmooth {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContDiffOn ℝ 2 (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (Ioo 0 T ×ˢ (univ : Set Plane)) := by
  have hU : IsOpen (Ioo 0 T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo 0 T ×ˢ (univ : Set Plane) ⊆ Icc 0 T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self subset_rfl
  have hF1 : ContDiffOn ℝ ∞ (crFc v 1) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (crFc_contDiffOn hv 1).mono hsub
  have hF0 : ContDiffOn ℝ ∞ (crFc v 0) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (crFc_contDiffOn hv 0).mono hsub
  have hd1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (crFc v 1) x) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    hF1.fderiv_of_isOpen hU (by simp)
  have hd0 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (crFc v 0) x) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    hF0.fderiv_of_isOpen hU (by simp)
  have hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      fderiv ℝ (crFc v 1) x crEQ - fderiv ℝ (crFc v 0) x crEE)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (hd1.clm_apply contDiffOn_const).sub (hd0.clm_apply contDiffOn_const)
  have hG' : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    hG.congr (fun x hx => crCurl_open hv hx.1 x.2)
  exact hG'.of_le (by simp)

/-- Part (c): the vorticity is bounded on `[0,T] × ℝ²` by `2 M₁`, where `M₁` bounds the first
spatial derivative of `v` (`HasBoundedDerivsOn`, `k = 1`). -/
theorem crBounded {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)))
    (hb : HasBoundedDerivsOn T v) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ M := by
  obtain ⟨M1, hM1⟩ := hb 1
  refine ⟨M1 + M1, fun s hs z => ?_⟩
  -- the slice `w ↦ v s w` is differentiable on the whole plane
  have hdiff : Differentiable ℝ (v s) := by
    intro w
    have h1 : DifferentiableWithinAt ℝ (fun x : ℝ × Plane => v x.1 x.2)
        (Icc 0 T ×ˢ (univ : Set Plane)) (s, w) :=
      hv.differentiableOn (by simp) _ ⟨hs, mem_univ w⟩
    have h2 : DifferentiableWithinAt ℝ (fun w' : Plane => ((s, w') : ℝ × Plane)) univ w :=
      DifferentiableAt.differentiableWithinAt
        (((differentiable_const s).prodMk differentiable_id) w)
    have h3 : DifferentiableWithinAt ℝ ((fun x : ℝ × Plane => v x.1 x.2) ∘
        fun w' : Plane => ((s, w') : ℝ × Plane)) univ w :=
      DifferentiableWithinAt.comp w h1 h2 (fun w' _ => ⟨hs, mem_univ w'⟩)
    exact differentiableWithinAt_univ.mp h3
  -- the coordinate components of `v s` and their derivatives
  have hk1 : Differentiable ℝ (fun w => v s w 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiable.comp hdiff
  have hk0 : Differentiable ℝ (fun w => v s w 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiable.comp hdiff
  have hfq : HasFDerivAt (fun w => v s w 1)
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp (fderiv ℝ (v s) z)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have hfe : HasFDerivAt (fun w => v s w 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (fderiv ℝ (v s) z)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have hQ : Cyl.partialQ (fun w => v s w 1) z = fderiv ℝ (v s) z ((1 : ℝ), (0 : ℝ)) 1 := by
    have e1 := Cyl.partialQ_eq_fderiv hk1 z
    rw [hfq.fderiv] at e1
    exact e1
  have hE : Cyl.partialEta (fun w => v s w 0) z = fderiv ℝ (v s) z ((0 : ℝ), (1 : ℝ)) 0 := by
    have e0 := Cyl.partialEta_eq_fderiv hk0 z
    rw [hfe.fderiv] at e0
    exact e0
  have hcurl : Cyl.curl (v s) z =
      fderiv ℝ (v s) z ((1 : ℝ), (0 : ℝ)) 1 - fderiv ℝ (v s) z ((0 : ℝ), (1 : ℝ)) 0 := by
    show Cyl.partialQ (fun w => v s w 1) z - Cyl.partialEta (fun w => v s w 0) z = _
    rw [hQ, hE]
  -- operator-norm bound on the derivative of the slice
  have hD : ‖fderiv ℝ (v s) z‖ ≤ M1 := by
    have h := hM1 s hs z
    rwa [norm_iteratedFDeriv_one] at h
  have hbound : ∀ w : Plane, ‖w‖ ≤ 1 → ‖fderiv ℝ (v s) z w‖ ≤ M1 := fun w hw =>
    calc ‖fderiv ℝ (v s) z w‖ ≤ ‖fderiv ℝ (v s) z‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm (fderiv ℝ (v s) z) w
      _ ≤ ‖fderiv ℝ (v s) z‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = ‖fderiv ℝ (v s) z‖ := mul_one _
      _ ≤ M1 := hD
  have hw1 : ‖(((1 : ℝ), (0 : ℝ)) : Plane)‖ ≤ 1 := by simp [Prod.norm_def]
  have hw2 : ‖(((0 : ℝ), (1 : ℝ)) : Plane)‖ ≤ 1 := by simp [Prod.norm_def]
  have hc1 : |fderiv ℝ (v s) z ((1 : ℝ), (0 : ℝ)) 1| ≤ M1 := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (fderiv ℝ (v s) z ((1 : ℝ), (0 : ℝ))) 1).trans (hbound _ hw1)
  have hc2 : |fderiv ℝ (v s) z ((0 : ℝ), (1 : ℝ)) 0| ≤ M1 := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (fderiv ℝ (v s) z ((0 : ℝ), (1 : ℝ))) 0).trans (hbound _ hw2)
  rw [hcurl]
  have ha := abs_le.1 hc1
  have hb' := abs_le.1 hc2
  exact abs_le.2 ⟨by linarith [ha.1, hb'.2], by linarith [ha.2, hb'.1]⟩

/-- Part (d): the vorticity of a `c`-periodic velocity is `c`-periodic in `q`. -/
theorem crPeriodic {v : ℝ → Plane → Vec} {c T : ℝ}
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Cyl.IsPeriodic c (Cyl.curl (v s)) := by
  have h1 : Cyl.IsPeriodic c (fun w => v s w 1) := (hper s hs).fun_comp (fun x : Vec => x 1)
  have h0 : Cyl.IsPeriodic c (fun w => v s w 0) := (hper s hs).fun_comp (fun x : Vec => x 0)
  intro z
  show Cyl.partialQ (fun w => v s w 1) (z.1 + c, z.2) -
      Cyl.partialEta (fun w => v s w 0) (z.1 + c, z.2) =
    Cyl.partialQ (fun w => v s w 1) z - Cyl.partialEta (fun w => v s w 0) z
  rw [h1.partialQ z, h0.partialEta z]

/-- **Regularity of the vorticity** (`CurlRegularity`, source lines 276-288): the curl of a smooth
`c`-periodic velocity with bounded derivatives on `[0,T]` is continuous on `[0,T] × ℝ²`, `C²` on
`(0,T) × ℝ²`, bounded, and `c`-periodic in `q`. -/
theorem curlRegularity : CurlRegularity := by
  intro c T v hc hT hv hper hb
  exact ⟨crContinuous hT hv, crSmooth hv, crBounded hv hb, fun s hs => crPeriodic hper hs⟩

end UnforcedLeray.Short.PartI
