import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2

/-!
# Part I, task `PartI:T08/7/3` (`JTQuad`): assembly from `JTAdvInt` and `JTBoundQ`

Source: `the November 2 reference manuscript` lines 352-358. The leaves are stated in
`Sub/PartI_T08_7_2.lean`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartI

theorem jtQuad_of (hI : JTAdvInt) (hQ : JTBoundQ) : JTQuad := by
  intro j
  obtain ⟨A, hA, h⟩ := hQ j
  refine ⟨A, hA, ?_⟩
  intro c V f G M H
  have H' := H
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hM⟩ := H'
  rw [advection_eq_advB]
  exact ⟨contDiff_advB hf.1 hf.1, hI j c f f f hf.1 hf.1 hf (Or.inl hf) hfb hfb, h c V f G M H⟩

end UnforcedLeray.Short.PartI
