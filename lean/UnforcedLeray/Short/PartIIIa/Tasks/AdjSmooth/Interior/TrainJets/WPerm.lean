import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Differentiating `q ↦ c q u` at a constant vector `u` (within `s`). -/
theorem fderivWithin_clm_apply_const_aux {s : Set (ℝ × (ℝ × ℝ))} {x : ℝ × (ℝ × ℝ)}
    (c : ℝ × (ℝ × ℝ) → (ℝ × (ℝ × ℝ) →L[ℝ] ℝ)) (u : ℝ × (ℝ × ℝ))
    (hxs : UniqueDiffWithinAt ℝ s x) (hc : DifferentiableWithinAt ℝ c s x) :
    fderivWithin ℝ (fun y => c y u) s x = (fderivWithin ℝ c s x).flip u := by
  have h := fderivWithin_clm_apply (𝕜 := ℝ) hxs hc (differentiableWithinAt_const u)
  simp only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h
  exact h

/-- The closure of the interior of `tjU` is `tjU`. -/
theorem closure_interior_tjU : closure (interior tjU) = tjU := by
  have hint : interior tjU = Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    show interior (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) = _
    rw [interior_prod_eq, interior_Ici, interior_univ]
  rw [hint, closure_prod_eq, closure_Ioi, closure_univ]

/-- **Words do not depend on the order of their letters** (symmetry of mixed derivatives within
`tjU`; `tjU` is the closure of its interior `Ioi 0 ×ˢ univ`). (Induction on `List.Perm`: `cons` by
`fderivWithin_congr`; `swap` by `ContDiffWithinAt.isSymmSndFDerivWithinAt` for `tjW L h` and the
derivative of `q ↦ fderivWithin g tjU q v`; `trans`.) -/
theorem tjWPerm : TjWPerm := by
  intro h hh L L' hLL'
  have key : ∀ L L' : List (Fin 3), L.Perm L' → EqOn (tjW L h) (tjW L' h) tjU := by
    intro L L' hperm
    induction hperm with
    | nil =>
      intro p _
      rfl
    | cons x _ ih =>
      intro p hp
      simp only [tjW_cons]
      rw [fderivWithin_congr ih (ih hp)]
    | swap x y l =>
      intro p hp
      have hg : ContDiffOn ℝ ∞ (tjW l h) tjU := tjW_contDiffOn hh l
      have hc : DifferentiableWithinAt ℝ (fderivWithin ℝ (tjW l h) tjU) tjU p :=
        ((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_tjU).1 hg).2.differentiableOn
          (by simp) p hp
      have hsym : IsSymmSndFDerivWithinAt ℝ (tjW l h) tjU p :=
        (hg.contDiffWithinAt hp).isSymmSndFDerivWithinAt (by simp) uniqueDiffOn_tjU
          (by rw [closure_interior_tjU]; exact hp) hp
      simp only [tjW_cons]
      rw [fderivWithin_clm_apply_const_aux _ (stDir x) (uniqueDiffOn_tjU p hp) hc,
        fderivWithin_clm_apply_const_aux _ (stDir y) (uniqueDiffOn_tjU p hp) hc]
      simp only [ContinuousLinearMap.flip_apply]
      exact hsym (stDir y) (stDir x)
    | trans _ _ ih1 ih2 =>
      intro p hp
      exact (ih1 hp).trans (ih2 hp)
  intro p hp
  exact key L L' hLL' hp

end UnforcedLeray.Short.IIIa
