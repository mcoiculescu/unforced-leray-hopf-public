import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Cond
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzModeSolve`): the domination hypotheses of the Green convolution

The generic parameter-integral machinery of `Tasks/F05aAdjResolventSolution/ParamIntegralSmooth.lean`
(`ParamIntegralSmoothAux.GenHyp`, `pm_contDiff`, `pm_hasFDerivAt_gen`, `pm_deriv_formula`; target space
arbitrary normed) applies to the Green family `t ↦ (x ↦ G_k(t) h(s, η - t))` as soon as the three
hypotheses of `GenHyp` hold. `NzConvGenHyp` states exactly this; `NzConvSmooth` follows at once
(`nzConvSmooth_of`, proved here), and `NzConvFderiv`, `NzConvDecay` follow from it by moving
`fderiv`/`iteratedFDeriv` under the integral (`pm_hasFDerivAt_gen`, `pm_deriv_formula`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Leaf `NzConvGenHyp`: domination hypotheses for the Green family.** For `k ≠ 0` and smooth
compactly supported `h`, the family `G t x = G_k(t) h(x.1, x.2 - t)` (`t ∈ ℝ` with Lebesgue measure,
`x ∈ ℝ × ℝ`) satisfies `GenHyp`: (1) each `G t` is smooth; (2) `t ↦ iteratedFDeriv ℝ j (G t) x` is
a.e.-strongly measurable (it is continuous in `t`: `iteratedFDeriv ℝ j (G t) x =
G_k(t) • iteratedFDeriv ℝ j h (x - (0, t))` by `iteratedFDeriv_comp_add_right` / `iteratedFDeriv_const_smul_apply`,
and `iteratedFDeriv ℝ j h` is continuous); (3) for each order `j`, the integrable bound
`b_j(t) = |G_k(t)| · M_j`, `M_j = sup ‖iteratedFDeriv ℝ j h‖` (finite: `iteratedFDeriv ℝ j h` is
continuous with compact support, `HasCompactSupport.iteratedFDeriv`,
`HasCompactSupport.exists_bound_of_continuous`), `G_k` integrable (`exp_neg_integrableOn_Ioi` on both half
lines, `|G_k(t)| = e^{-|k||t|}/(2|k|)`). -/
def NzConvGenHyp : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
    ParamIntegralSmoothAux.GenHyp (volume : Measure ℝ)
      (fun (t : ℝ) (x : ℝ × ℝ) => (nzGreen k t : ℂ) * h (x.1, x.2 - t))

/-- `NzConvSmooth` from `NzConvGenHyp` (proved). -/
theorem nzConvSmooth_of (hG : NzConvGenHyp) : NzConvSmooth := by
  intro k hk h hh hcs
  exact ParamIntegralSmoothAux.pm_contDiff (m := volume) (hG k hk h hh hcs)

end UnforcedLeray.Short.PartIIa
