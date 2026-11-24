import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`: the lemma `GammaOdd`

Source of record: `the November 2 reference manuscript`, lines 261-288. Uniqueness
gives `v(-q,-η,s) = -v(q,η,s)`, so the first component of a slice `w` satisfies
`w₁(q,-η) = -w₁(-q,η)`. Substituting `q ↦ -q` and using `c`-periodicity in `q` gives
`Γ(-η) = -Γ(η)`, where `Γ(η) = ∫₀^c w₁(q,η) dq` is `sliceGamma c w η`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Lemma `GammaOdd`**: `Γ(-η) = -Γ(η)` for every stream slice. -/
theorem gammaOdd : GammaOdd := by
  unfold GammaOdd
  intro c w hs η
  -- the first component is `c`-periodic in `q`
  have hp : Function.Periodic (fun q : ℝ => w (q, η) 0) c := by
    intro q
    have h : w (q + c, η) = w (q, η) := hs.periodic (q, η)
    show w (q + c, η) 0 = w (q, η) 0
    rw [h]
  -- oddness of the first component: `w₁(q, -η) = -w₁(-q, η)`
  have hodd : ∀ q : ℝ, w (q, -η) 0 = -w (-q, η) 0 := by
    intro q
    have h : w (q, -η) = -w (-q, η) := by
      have h0 := hs.odd (-q, η)
      have hz : -((-q, η) : ℝ × ℝ) = (q, -η) := by simp
      rw [hz] at h0
      exact h0
    simp [h]
  -- the integral over `[-c, 0]` equals the one over `[0, c]` by periodicity
  have hshift : ∫ x in (-c)..0, w (x, η) 0 = ∫ x in (0 : ℝ)..c, w (x, η) 0 := by
    have h := hp.intervalIntegral_add_eq (-c) 0
    simpa using h
  -- substitution `q ↦ -q`
  have hc : ∫ q in (0 : ℝ)..c, w (-q, η) 0 = ∫ x in (-c)..(-(0 : ℝ)), w (x, η) 0 :=
    intervalIntegral.integral_comp_neg (fun x => w (x, η) 0)
  unfold sliceGamma
  simp_rw [hodd]
  rw [intervalIntegral.integral_neg, hc, neg_zero, hshift]

end UnforcedLeray.Short.PartI
