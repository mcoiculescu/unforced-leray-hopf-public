import UnforcedLeray.Short.PartIIa.Sub.N02_4_5

/-!
# Part II-a, task `PartII-a:N02/4/5/2` (`NzGreenKey2D` from `NzGreenKey1D`)

Conditional theorem: `nzGreenKey2D_of (h : NzGreenKey1D) : NzGreenKey2D`. The one-dimensional
Green identity is a hypothesis (sibling task `NzGreenKey1D`).

Route. For `a` smooth with compact support and `x = (x1, x2)`, the slice `u s = a (x1, s)` is
`C²` with compact support (the `s`-projection of `tsupport a`, compact, contains the support of
`u`). By the chain rule `deriv u s = ∂_η a (x1, s)` and `iteratedDeriv 2 u s = ∂_η (∂_η a) (x1, s)`.
The one-dimensional identity at `η = x2` is then the two-dimensional identity at `x`.

Source of record: `the November 2 reference manuscript`, lines 1713-1722 (the
one-mode reduction on a nonzero `q`-frequency, which fixes the form of the equation in `NzGreenKey2D`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Chain rule on a slice: the `s`-derivative of `s ↦ g (x1, s)` at `t` is `∂_η g (x1, t)`. -/
theorem nzgk2_hasDerivAt_slice {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (x1 t : ℝ) :
    HasDerivAt (fun s : ℝ => g (x1, s)) (fderiv ℝ g (x1, t) (0, 1)) t := by
  have hf : HasDerivAt (fun s : ℝ => ((x1, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t x1).prodMk (hasDerivAt_id' t)
  exact (hg (x1, t)).hasFDerivAt.comp_hasDerivAt t hf

theorem nzGreenKey2D_of (h : NzGreenKey1D) : NzGreenKey2D := by
  unfold NzGreenKey1D at h
  unfold NzGreenKey2D
  intro k hk a ha hcs x
  obtain ⟨x1, x2⟩ := x
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdb : Differentiable ℝ (fun y : ℝ × ℝ => fderiv ℝ a y (0, 1)) :=
    (nzms_dEta_smooth ha).differentiable (by simp)
  have hemb : ContDiff ℝ ∞ (fun s : ℝ => ((x1, s) : ℝ × ℝ)) :=
    (contDiff_const (c := x1)).prodMk contDiff_id
  have hu : ContDiff ℝ 2 (fun s : ℝ => a (x1, s)) := (ha.comp hemb).of_le (by simp)
  have hu_cs : HasCompactSupport (fun s : ℝ => a (x1, s)) := by
    apply HasCompactSupport.intro (IsCompact.image hcs continuous_snd)
    intro s hs
    by_contra hne
    apply hs
    have hne' : a (x1, s) ≠ 0 := hne
    exact ⟨(x1, s), subset_tsupport a (Function.mem_support.mpr hne'), rfl⟩
  have hu2 : ∀ s : ℝ, iteratedDeriv 2 (fun r : ℝ => a (x1, r)) s =
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ a y (0, 1)) (x1, s) (0, 1) := by
    intro s
    have h1 : deriv (fun r : ℝ => a (x1, r)) = fun r : ℝ => fderiv ℝ a (x1, r) (0, 1) := by
      funext r
      exact (nzgk2_hasDerivAt_slice hda x1 r).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    exact (nzgk2_hasDerivAt_slice hdb x1 s).deriv
  have key := h k hk (fun s : ℝ => a (x1, s)) hu hu_cs x2
  simp only [hu2] at key
  unfold nzConv
  exact key

end UnforcedLeray.Short.PartIIa
