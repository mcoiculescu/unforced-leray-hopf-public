import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3

/-!
# `PartIII-b:C/grad/3/5`: `GradMeas` from joint continuity on `{0 < s}`

Source `the November 2 reference manuscript`
5063-5079 (measurability implicit).  `gradAcoef` on `s > 0` is `s⁻¹ • matTen (cylGrad …)`, and
`cylGrad` is built from `dQ`, `dEta`, `Kop` of the components of `ĥ_A`, i.e. from the lattice
sums `h^p_A`, `ψ^p_A` and their first and second `x`- and `s`-derivatives.  Those continuity
leaves are not proved yet (the same blocker as `HAcMeas`, `Sub/PartIII-b_C_inst_11_4.lean`).

Proved here: the reduction `gradMeas_of_contOn` (continuity on `{0 < s}` gives `GradMeas`, since
`gradMeasure c` is carried by `{0 < s}`, `ae_gradMeasure_fst_pos`).  The unconditional
`gradMeas` is NOT proved in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Joint continuity of the physical tensor coefficient `s⁻¹∇ĥ_A` on `{0 < s}`
(needed input: reduces to the lattice-sum continuity and differentiability leaves). -/
def GradContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (gradAcoef ν ε χf A) {p : Chart | 0 < p.1}

/-- Reduction: continuity on `{0 < p.1}` gives `GradMeas`, since `gradMeasure c` is carried
by `{0 < p.1}`. -/
theorem gradMeas_of_contOn (as : ℝ) (χf : ℝ → ℝ) (h : GradContOn as χf) : GradMeas as χf := by
  intro hχ ν ε hν A hA
  have hc := h hχ ν ε hν A hA
  have hm : MeasurableSet {p : Chart | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hr : AEStronglyMeasurable (gradAcoef ν ε χf A)
      ((gradMeasure (cOf ν)).restrict {p : Chart | 0 < p.1}) :=
    hc.aestronglyMeasurable hm
  have hae : ∀ᵐ p ∂(gradMeasure (cOf ν)), p ∈ {p : Chart | 0 < p.1} :=
    ae_gradMeasure_fst_pos (cOf ν)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hr

end UnforcedLeray.Short.PartIIIb.Concrete
