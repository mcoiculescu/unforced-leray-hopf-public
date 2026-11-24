import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2_2
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv

/-!
# Part I, `APL2TimeDerivQE`: time derivative of the vorticity gradient (source lines 285-288)

For `s ∈ (0,T)`, `∂_s ∂_q ω = ∂_q F` and `∂_s ∂_η ω = ∂_η F` where `F = apL2F ν (v s)`.
Route: the scalar vorticity equation gives `∂_t ω(t,z) = F(z)` at `t = s`; mixed partials of
the `C²` function `(t,z) ↦ ω` commute (`ContDiffAt.isSymmSndFDerivAt`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

lemma tdSymm {W : ℝ × Plane → ℝ} {x : ℝ × Plane} (hW : ContDiffAt ℝ 2 W x)
    (a b : ℝ × Plane) :
    fderiv ℝ (fderiv ℝ W) x a b = fderiv ℝ (fderiv ℝ W) x b a :=
  hW.isSymmSndFDerivAt (by simp) a b

lemma tdFDiff {W : ℝ × Plane → ℝ} {x : ℝ × Plane} (hW : ContDiffAt ℝ 2 W x) :
    DifferentiableAt ℝ (fderiv ℝ W) x :=
  (hW.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

lemma tdFD {W : ℝ × Plane → ℝ} {x : ℝ × Plane} (hW : ContDiffAt ℝ 2 W x) (v w : ℝ × Plane) :
    fderiv ℝ (fun y => fderiv ℝ W y v) x w = fderiv ℝ (fderiv ℝ W) x w v := by
  have h2 : HasFDerivAt (fun y => fderiv ℝ W y v)
      ((fderiv ℝ W x).comp (0 : (ℝ × Plane) →L[ℝ] (ℝ × Plane))
        + (fderiv ℝ (fderiv ℝ W) x).flip v) x :=
    (tdFDiff hW).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h2.fderiv]
  simp

lemma tdTimeSlice {W : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hW : ContDiffAt ℝ 2 W (s, z))
    (v : ℝ × Plane) :
    deriv (fun t : ℝ => fderiv ℝ W (t, z) v) s
      = fderiv ℝ (fderiv ℝ W) (s, z) ((1 : ℝ), (0 : Plane)) v := by
  have h2 : HasFDerivAt (fun y => fderiv ℝ W y v)
      ((fderiv ℝ W (s, z)).comp (0 : (ℝ × Plane) →L[ℝ] (ℝ × Plane))
        + (fderiv ℝ (fderiv ℝ W) (s, z)).flip v) (s, z) :=
    (tdFDiff hW).hasFDerivAt.clm_apply (hasFDerivAt_const v (s, z))
  have h3 : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  have h4 := h2.comp_hasDerivAt s h3
  have h5 : deriv (fun t : ℝ => fderiv ℝ W (t, z) v) s
      = ((fderiv ℝ W (s, z)).comp (0 : (ℝ × Plane) →L[ℝ] (ℝ × Plane))
        + (fderiv ℝ (fderiv ℝ W) (s, z)).flip v) ((1 : ℝ), (0 : Plane)) := h4.deriv
  rw [h5]
  simp

lemma tdSpaceQ {G : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hG : DifferentiableAt ℝ G (s, z)) :
    Cyl.partialQ (fun z' : Plane => G (s, z')) z
      = fderiv ℝ G (s, z) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
  have hg : HasDerivAt (fun q : ℝ => ((s, (q, z.2)) : ℝ × Plane)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
      z.1 :=
    (hasDerivAt_const z.1 s).prodMk ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have h := hG.hasFDerivAt.comp_hasDerivAt z.1 hg
  unfold Cyl.partialQ
  exact h.deriv

lemma tdSpaceE {G : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hG : DifferentiableAt ℝ G (s, z)) :
    Cyl.partialEta (fun z' : Plane => G (s, z')) z
      = fderiv ℝ G (s, z) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
  have hg : HasDerivAt (fun η : ℝ => ((s, (z.1, η)) : ℝ × Plane)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      z.2 :=
    (hasDerivAt_const z.2 s).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have h := hG.hasFDerivAt.comp_hasDerivAt z.2 hg
  unfold Cyl.partialEta
  exact h.deriv

theorem tdMixedQ {W : ℝ × Plane → ℝ} {T : ℝ}
    (hW : ContDiffOn ℝ 2 W (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    deriv (fun t => Cyl.partialQ (fun z' : Plane => W (t, z')) z) s
      = Cyl.partialQ (fun z' : Plane => fderiv ℝ W (s, z') ((1 : ℝ), (0 : Plane))) z := by
  have hU : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hc : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), ContDiffAt ℝ 2 W x :=
    fun x hx => hW.contDiffAt (hU.mem_nhds hx)
  have hD : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), DifferentiableAt ℝ W x :=
    fun x hx => (hc x hx).differentiableAt (by norm_num)
  have hxs : (s, z) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) := Set.mk_mem_prod hs (mem_univ z)
  have hEv : (fun t => Cyl.partialQ (fun z' : Plane => W (t, z')) z)
      =ᶠ[𝓝 s] (fun t => fderiv ℝ W (t, z) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact tdSpaceQ (G := W) (s := t) (hD (t, z) (Set.mk_mem_prod ht (mem_univ z)))
  rw [hEv.deriv_eq]
  have hG : DifferentiableAt ℝ (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane))) (s, z) :=
    (tdFDiff (hc (s, z) hxs)).clm_apply (differentiableAt_const _)
  rw [tdTimeSlice (hc (s, z) hxs) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))]
  rw [show Cyl.partialQ (fun z' : Plane => fderiv ℝ W (s, z') ((1 : ℝ), (0 : Plane))) z
      = fderiv ℝ (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane))) (s, z)
          ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) from tdSpaceQ hG]
  rw [tdFD (hc (s, z) hxs) ((1 : ℝ), (0 : Plane)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))]
  exact tdSymm (hc (s, z) hxs) ((1 : ℝ), (0 : Plane)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))

theorem tdMixedE {W : ℝ × Plane → ℝ} {T : ℝ}
    (hW : ContDiffOn ℝ 2 W (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    deriv (fun t => Cyl.partialEta (fun z' : Plane => W (t, z')) z) s
      = Cyl.partialEta (fun z' : Plane => fderiv ℝ W (s, z') ((1 : ℝ), (0 : Plane))) z := by
  have hU : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hc : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), ContDiffAt ℝ 2 W x :=
    fun x hx => hW.contDiffAt (hU.mem_nhds hx)
  have hD : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), DifferentiableAt ℝ W x :=
    fun x hx => (hc x hx).differentiableAt (by norm_num)
  have hxs : (s, z) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) := Set.mk_mem_prod hs (mem_univ z)
  have hEv : (fun t => Cyl.partialEta (fun z' : Plane => W (t, z')) z)
      =ᶠ[𝓝 s] (fun t => fderiv ℝ W (t, z) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact tdSpaceE (G := W) (s := t) (hD (t, z) (Set.mk_mem_prod ht (mem_univ z)))
  rw [hEv.deriv_eq]
  have hG : DifferentiableAt ℝ (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane))) (s, z) :=
    (tdFDiff (hc (s, z) hxs)).clm_apply (differentiableAt_const _)
  rw [tdTimeSlice (hc (s, z) hxs) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))]
  rw [show Cyl.partialEta (fun z' : Plane => fderiv ℝ W (s, z') ((1 : ℝ), (0 : Plane))) z
      = fderiv ℝ (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane))) (s, z)
          ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) from tdSpaceE hG]
  rw [tdFD (hc (s, z) hxs) ((1 : ℝ), (0 : Plane)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))]
  exact tdSymm (hc (s, z) hxs) ((1 : ℝ), (0 : Plane)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

/-- **`APL2TimeDerivQE`** (source lines 285-288): the time derivative of `∂_qω`, `∂_ηω` equals
the `q`, `η` derivative of the vorticity right-hand side `F = apL2F ν (v s)`. -/
theorem aPL2TimeDerivQE : UnforcedLeray.Short.PartI.APL2TimeDerivQE := by
  intro ν c T v p hν hc hcls s hs z
  have hW : ContDiffOn ℝ 2 (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    crSmooth hcls.classical.smooth_v
  have hF : ∀ z' : Plane,
      fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z') ((1 : ℝ), (0 : Plane))
        = apL2F ν (v s) z' := by
    intro z'
    have h := localVorticityEquation ν c T v p hν hc hcls.pos hcls.classical s hs z'
    have hd : deriv (fun t => Cyl.curl (v t) z') s
        = fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z') ((1 : ℝ), (0 : Plane)) :=
      (apHD_deriv_at hW hs.1 hs.2 z').deriv
    unfold UnforcedLeray.B0238.vorticityResidual at h
    rw [hd] at h
    unfold apL2F
    linarith
  have e1 : apL2F ν (v s) = fun z' : Plane =>
      fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z') ((1 : ℝ), (0 : Plane)) :=
    funext fun z' => (hF z').symm
  rw [e1]
  constructor
  · exact tdMixedQ hW hs z
  · exact tdMixedE hW hs z

end UnforcedLeray.Short.PartI
