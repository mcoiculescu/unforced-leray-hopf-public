import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq

/-!
# Part I, task `PartI:T08/2/2/2/1`: `SliceWordReg`

Source: `the November 2 reference manuscript`, lines 276-288 (smooth for positive
time, up to `s = 0`).  Route: induction on the word; the line `t ↦ (s, (t, η))` stays in
`Ici 0 ×ˢ univ`, so the slice partial is `fderivWithin G U x (0, (1, 0))`, which is `C^∞` on `U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem swrUD : UniqueDiffOn ℝ ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) :=
  UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ

theorem swrLineX {G : ℝ × Plane → ℝ} (hG : ContDiffOn ℝ ∞ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)))
    (x : ℝ × Plane) (hx : x ∈ (Ici (0:ℝ)) ×ˢ (univ : Set Plane)) :
    deriv (fun t : ℝ => G (x.1, (t, x.2.2))) x.2.1 =
      fderivWithin ℝ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) x (0, (1, 0)) := by
  have hd : DifferentiableWithinAt ℝ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) x :=
    (hG.differentiableOn (by simp)) x hx
  have hγ : HasDerivAt (fun t : ℝ => ((x.1, (t, x.2.2)) : ℝ × Plane)) ((0, (1, 0)) : ℝ × Plane)
      x.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have hmaps : MapsTo (fun t : ℝ => ((x.1, (t, x.2.2)) : ℝ × Plane)) univ
      ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) := fun t _ => ⟨hx.1, mem_univ _⟩
  have h := (hd.hasFDerivWithinAt).comp_hasDerivWithinAt x.2.1 hγ.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.1 h).deriv

theorem swrLineY {G : ℝ × Plane → ℝ} (hG : ContDiffOn ℝ ∞ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)))
    (x : ℝ × Plane) (hx : x ∈ (Ici (0:ℝ)) ×ˢ (univ : Set Plane)) :
    deriv (fun t : ℝ => G (x.1, (x.2.1, t))) x.2.2 =
      fderivWithin ℝ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) x (0, (0, 1)) := by
  have hd : DifferentiableWithinAt ℝ G ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) x :=
    (hG.differentiableOn (by simp)) x hx
  have hγ : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : ℝ × Plane)) ((0, (0, 1)) : ℝ × Plane)
      x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have hmaps : MapsTo (fun t : ℝ => ((x.1, (x.2.1, t)) : ℝ × Plane)) univ
      ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) := fun t _ => ⟨hx.1, mem_univ _⟩
  have h := (hd.hasFDerivWithinAt).comp_hasDerivWithinAt x.2.2 hγ.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.1 h).deriv

theorem sliceWordReg_proof : UnforcedLeray.Short.PartI.SliceWordReg := by
  intro F hF u
  induction u with
  | nil => exact hF
  | cons b u ih =>
    set G : ℝ × Plane → ℝ := fun x => B0151.derivWord u (fun z => F (x.1, z)) x.2 with hGdef
    have hU := swrUD
    have hc : ∀ v : ℝ × Plane, ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ G
        ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) x v) ((Ici (0:ℝ)) ×ˢ (univ : Set Plane)) := fun v =>
      ((contDiffOn_infty_iff_fderivWithin hU).1 ih).2.clm_apply contDiffOn_const
    cases b
    · refine (hc (0, (0, 1))).congr ?_
      intro x hx
      exact swrLineY ih x hx
    · refine (hc (0, (1, 0))).congr ?_
      intro x hx
      exact swrLineX ih x hx

end UnforcedLeray.Short.PartI
