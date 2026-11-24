import UnforcedLeray.Short.PartIIa.Calc.BaseJets
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.MeanStreamSmooth

/-!
# Part II-a, base jets: the mean stream is smooth and `q`-independent (`MeanSmoothQ`)

Target: `UnforcedLeray.Short.PartIIa.Jet.meanSmoothQ_of : MeanSmoothQ` (`Calc/BaseJets.lean`).

Source of record: `the November 2 reference manuscript`, lines 397-404 (the mean
stream `S = \bar ψ` is a function of `(s, η)` only).

Smoothness: `meanStreamSmooth_of` gives `S(s, η)` smooth on `(0,∞) × ℝ`, and
`contDiffOn_trainProfile_of_eta` composes with the profile coordinates. The `∂_q`-independence:
the profile `y ↦ S(y.2.2, y.2.1)` is constant along the line `x + t eqDir` (since `eqDir` has zero
`(s, η)` components), so its derivative in the direction `eqDir` vanishes at each point with `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream)

/-- The mean profile `y ↦ S(y.2.2, y.2.1)` is invariant under translation along `eqDir`. -/
theorem wmq_const_q (G : ℝ → ℝ → ℝ) (x : ProfilePoint) (t : ℝ) :
    trainProfile (fun s z => G s z.2) (x + t • eqDir) = trainProfile (fun s z => G s z.2) x := by
  have e : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  show G (x + t • eqDir).2.2 (x + t • eqDir).2.1 = G x.2.2 x.2.1
  rw [e]

/-- A differentiable function that is constant along a line has zero derivative along it. -/
theorem wmq_fderiv_zero {g : ProfilePoint → ℝ} {x v : ProfilePoint}
    (hg : DifferentiableAt ℝ g x) (hc : ∀ t : ℝ, g (x + t • v) = g x) :
    fderiv ℝ g x v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa using h
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg.hasFDerivAt hl (by simp)
  have hconst : (g ∘ fun t : ℝ => x + t • v) = fun _ => g x := funext fun t => hc t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const (0 : ℝ) (g x))

/-- **The mean stream is smooth and `q`-independent** (lines 397-404): from `LateIngredients`. -/
theorem meanSmoothQ_of (h : LateIngredients) : MeanSmoothQ := by
  unfold MeanSmoothQ
  refine ⟨?_, ?_⟩
  · intro ν c hν hc tr htr
    exact contDiffOn_trainProfile_of_eta (G := meanStream tr)
      (meanStreamSmooth_of h.smooth ν c hν hc tr htr)
  · intro ν c hν hc tr htr x hx
    have hS := contDiffOn_trainProfile_of_eta (G := meanStream tr)
      (meanStreamSmooth_of h.smooth ν c hν hc tr htr)
    have hdiff : DifferentiableAt ℝ (trainProfile (fun s z => meanStream tr s z.2)) x :=
      (hS.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)
    exact wmq_fderiv_zero hdiff (fun t => wmq_const_q (meanStream tr) x t)

end UnforcedLeray.Short.PartIIa.Jet
