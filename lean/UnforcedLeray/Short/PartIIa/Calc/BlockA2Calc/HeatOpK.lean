import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/5`: the heat operator and `K`

Source: `the November 2 reference manuscript`, line 1284
(`(∂_s - ν∂_η²)K = (K+2)(∂_s - ν∂_η²)` on families smooth for `s > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- **`(∂_s - ν∂_η²)K = (K+2)(∂_s - ν∂_η²)`** (task `PartII-a:R02/12/5`), from the pointwise
commutator `[∂_s, K] = 2∂_s` (`ProfileCommutators`), the iterated commutator
`∂_η²K = (K+2)∂_η²` (`IterCalcComm` with `a = 2`), and linearity of `K` at the point. -/
theorem heatOpK_of (hC : UnforcedLeray.Short.PartIIa.ProfileCommutators)
    (hI : UnforcedLeray.Short.PartIIa.Jet.IterCalcComm) :
    UnforcedLeray.Short.PartIIa.Jet.A2.HeatOpK := by
  intro F hF ν c hν hc tr htr x hx
  have hU := hF ν c hν hc tr htr
  have hf2 : ContDiffAt ℝ 2 (F ν c tr) x :=
    (hU.contDiffAt (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)
  have ha := (hC (F ν c tr) x hf2).2.2
  have e2 : partialEta (partialEta (ageOperator (F ν c tr))) x
      = ageOperator (partialEta (partialEta (F ν c tr))) x
        + 2 * partialEta (partialEta (F ν c tr)) x := by
    have h := (hI (F ν c tr) hU 2 0).2.2 hx
    simp only [Nat.cast_ofNat] at h
    exact h
  have hdiff : ∀ G : ProfilePoint → ℝ, ContDiffOn ℝ ∞ G {y | 0 < y.2.2} →
      DifferentiableAt ℝ G x := fun G hG =>
    (hG.contDiffAt (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).differentiableAt
      (by norm_num)
  have hAc : ContDiffOn ℝ ∞ (partialAge (F ν c tr)) {y | 0 < y.2.2} :=
    UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hU esDir
  have hEc : ContDiffOn ℝ ∞ (partialEta (F ν c tr)) {y | 0 < y.2.2} :=
    UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hU eηDir
  have hBc : ContDiffOn ℝ ∞ (partialEta (partialEta (F ν c tr))) {y | 0 < y.2.2} :=
    UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hEc eηDir
  have hA := hdiff _ hAc
  have hB := hdiff _ hBc
  have hfun : heatOp F ν c tr
      = fun y => partialAge (F ν c tr) y + (-ν) * partialEta (partialEta (F ν c tr)) y := by
    funext y
    show partialAge (F ν c tr) y - ν * partialEta (partialEta (F ν c tr)) y
      = partialAge (F ν c tr) y + (-ν) * partialEta (partialEta (F ν c tr)) y
    ring
  show partialAge (ageOperator (F ν c tr)) x - ν * partialEta (partialEta (ageOperator (F ν c tr))) x
      = ageOperator (heatOp F ν c tr) x + 2 * heatOp F ν c tr x
  rw [hfun, ageOperator_add_mul hA hB (-ν)]
  dsimp only
  linear_combination ha - ν * e2

end UnforcedLeray.Short.PartIIa.Jet.A2
