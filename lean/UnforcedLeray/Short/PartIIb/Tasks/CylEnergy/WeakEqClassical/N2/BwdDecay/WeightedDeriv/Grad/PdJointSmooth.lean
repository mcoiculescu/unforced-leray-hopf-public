import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!

function are jointly smooth.

Source: `the November 2 reference manuscript` lines 2100-2105.

On the band `Icc s t ×ˢ univ` with `s < t` the within-derivative `fderivWithin` of the joint map is
smooth (the set has unique differentiability); its value on the vector `inr (dir j)` is the spatial
partial.  For `t ≤ s` the band is a single time slice or empty.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem pdJointSmooth : UnforcedLeray.Short.IIb.PdJointSmooth := by
  intro s t U j hU
  -- spatial slices of `U` at times of the band are smooth
  have hslice : ∀ r ∈ Icc s t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U r) := by
    intro r hr
    have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => (r, x)) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h := hU.comp hcomp (fun x _ => ⟨hr, mem_univ _⟩)
    exact contDiffOn_univ.1 h
  rcases lt_or_ge s t with hst | hst
  · -- main case `s < t`
    have hS : UniqueDiffOn ℝ (Icc s t ×ˢ (univ : Set B0579.Plane)) :=
      (uniqueDiffOn_Icc hst).prod uniqueDiffOn_univ
    have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ))
        (Icc s t ×ˢ univ) :=
      hU.fderivWithin hS (by simp)
    have hG : ∀ z ∈ Icc s t ×ˢ (univ : Set B0579.Plane),
        B0579.pd j (U z.1) z.2 =
          fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) z
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane (B0579.dir j)) := by
      intro z hz
      obtain ⟨r, x⟩ := z
      have hr : r ∈ Icc s t := hz.1
      have hFd : DifferentiableWithinAt ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2)
          (Icc s t ×ˢ univ) (r, x) :=
        hU.differentiableOn (by simp) _ hz
      have hF' := hFd.hasFDerivWithinAt
      have hg : HasFDerivAt (fun y : B0579.Plane => (r, y))
          (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) x :=
        (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
      have hg' : HasFDerivWithinAt (fun y : B0579.Plane => (r, y))
          (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) (univ : Set B0579.Plane) x :=
        hg.hasFDerivWithinAt
      have hcomp := HasFDerivWithinAt.comp x hF' hg'
        (fun y _ => (⟨hr, mem_univ y⟩ : (r, y) ∈ Icc s t ×ˢ (univ : Set B0579.Plane)))
      have hsl := hasFDerivWithinAt_univ.1 hcomp
      have hsl' : HasFDerivAt (U r)
          ((fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) (r, x)).comp
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane)) x := hsl
      unfold B0579.pd
      show fderiv ℝ (U r) x (B0579.dir j) = _
      rw [hsl'.fderiv]
      rfl
    have hH : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) z
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane (B0579.dir j)))
        (Icc s t ×ˢ univ) :=
      hD.clm_apply contDiffOn_const
    exact hH.congr (fun z hz => hG z hz)
  · -- degenerate band `t ≤ s`
    rcases eq_or_lt_of_le hst with h | h
    · -- `t = s`: a single time slice
      have hsub : ∀ r ∈ Icc s t, r = s := fun r hr => le_antisymm (by linarith [hr.2]) hr.1
      have hsl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U s) :=
        hslice s ⟨le_rfl, by linarith⟩
      have hpd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : B0579.Plane => B0579.pd j (U s) x) := by
        unfold B0579.pd
        exact (hsl.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
      have hcongr : ∀ z ∈ Icc s t ×ˢ (univ : Set B0579.Plane),
          B0579.pd j (U z.1) z.2 = (fun x : B0579.Plane => B0579.pd j (U s) x) z.2 := by
        intro z hz
        rw [hsub z.1 hz.1]
      exact ((hpd.comp contDiff_snd).contDiffOn).congr hcongr
    · -- `t < s`: the band is empty
      have hempty : Icc s t ×ˢ (univ : Set B0579.Plane) = ∅ := by
        rw [Icc_eq_empty (not_le.2 h), empty_prod]
      rw [hempty]
      exact contDiffOn_empty

end UnforcedLeray.Short.IIb
