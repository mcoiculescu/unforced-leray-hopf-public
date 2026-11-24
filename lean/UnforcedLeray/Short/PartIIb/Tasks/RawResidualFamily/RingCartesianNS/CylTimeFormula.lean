import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `CylTimeFormula`: the cylindrical time derivative

Proves `UnforcedLeray.Short.IIb.CylTimeFormula` (defined in `Sub/R1_7.lean`). Source of record:
`the November 2 reference manuscript`, SP 1263 (the ring residual `F_R`), and
`paper/main.tex` 2867-2888 (B0187: the cylindrical residual of `u_r e_r + u_z e_z`, where
`physT F r z t = ∂_t F(r, z, t)`).

Proof idea. For `x ∉ Axi.axis` and `t > 0`, the point `(ϱ x, x₃, t)` lies in the open set
`meridDomain = {r > 0, t > 0}`, where the profiles `ur`, `uz` are `C¹`. Hence `s ↦ ur (ϱ x) x₃ s`
and `s ↦ uz (ϱ x) x₃ s` are differentiable at `t`, with derivative `physT`. The fixed vectors
`eR x`, `e3` then give the time derivative of `s ↦ cylField ur uz s x` by the chain rule.

No hypotheses are added, and the file contains no placeholder proofs, new axioms or
kernel-evaluation shortcuts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-- The meridional domain `{r > 0, t > 0}` is open. -/
theorem cylTime_isOpen_meridDomain : IsOpen meridDomain := by
  have h1 : IsOpen {q : ℝ × ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {q : ℝ × ℝ × ℝ | 0 < q.2.2} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
  exact h1.inter h2

/-- For `x` off the axis at positive time, `(ϱ x, x₃, t) ∈ meridDomain`. -/
theorem cylTime_mem_meridDomain (x : Space) (t : ℝ) (hx : x ∉ Axi.axis) (ht : 0 < t) :
    (Axi.ϱ x, x 2, t) ∈ meridDomain :=
  ⟨Axi.ϱ_pos hx, ht⟩

/-- A `C¹` meridional profile is differentiable in time at a point `(r, z, t)` of `meridDomain`,
with time derivative `physT f r z t`. -/
theorem cylTime_hasDerivAt (f : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) (hmem : (r, z, t) ∈ meridDomain)
    (hf : MeridSmooth 1 f) :
    HasDerivAt (fun s => f r z s) (physT f r z t) t := by
  have hc : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) meridDomain := hf
  have hD : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) (r, z, t) :=
    hc.contDiffAt (cylTime_isOpen_meridDomain.mem_nhds hmem)
  have hg : DifferentiableAt ℝ (fun s : ℝ => ((r, z, s) : ℝ × ℝ × ℝ)) t :=
    (differentiableAt_const r).prodMk ((differentiableAt_const z).prodMk differentiableAt_id)
  have hdiff : DifferentiableAt ℝ
      ((fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) ∘ (fun s : ℝ => ((r, z, s) : ℝ × ℝ × ℝ))) t :=
    DifferentiableAt.comp t hD.differentiableAt_one hg
  exact hdiff.hasDerivAt

/-- **Time derivative of the meridional lift**: off the axis, at `t > 0`,
`∂_t (u_r e_r + u_z e_z) = (∂_t u_r) e_r + (∂_t u_z) e_z` (`B0187.physT`), for `u_r, u_z` of class
`C¹` jointly on `{r, t > 0}`. This is the leaf Prop `CylTimeFormula`. -/
theorem cylTimeFormula : CylTimeFormula := by
  unfold CylTimeFormula
  intro ur uz t x ht hx hur huz
  have hmem : (Axi.ϱ x, x 2, t) ∈ meridDomain := cylTime_mem_meridDomain x t hx ht
  have hr : HasDerivAt (fun s => ur (Axi.ϱ x) (x 2) s) (physT ur (Axi.ϱ x) (x 2) t) t :=
    cylTime_hasDerivAt ur _ _ t hmem hur
  have hz : HasDerivAt (fun s => uz (Axi.ϱ x) (x 2) s) (physT uz (Axi.ϱ x) (x 2) t) t :=
    cylTime_hasDerivAt uz _ _ t hmem huz
  have h := (hr.smul_const (Axi.eR x)).add (hz.smul_const Axi.e3)
  exact h.deriv

end UnforcedLeray.Short.IIb

end
