import UnforcedLeray.Short.PartIIa.Sub.R02_3

/-!
# Part II-a, task `PartII-a:R02/3`: continuity of the slice derivatives

Source of record: `the November 2 reference manuscript`, lines 447-459.

Target: `sliceDerivContinuous_of` (`Sub/R02_2.lean`, `Sub/R02_3.lean`): from the age-derivative
smoothness `AgeDerivSmooth`, every slice derivative `η ↦ ∂_η^b ∂_s^ℓ G(s, η)` of a jointly `C^∞`
function `G` on `(0,∞) × ℝ` is continuous at each age `s > 0`.

Proof: `H(s', η) = ∂_{s'}^ℓ G(s', η)` is jointly `C^∞` on `(0,∞) × ℝ` by `AgeDerivSmooth`. Its
restriction to the slice `s`, the map `η ↦ H(s, η)`, is `C^∞` on all of `ℝ`, since it is the
composite of `H` with the smooth map `η ↦ (s, η)`, which sends `ℝ` into `(0,∞) × ℝ`. Its
`b`-th derivative is continuous.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Continuity of the slice derivatives** (`sct:expansion` inputs, source lines 447-459): under
`AgeDerivSmooth`, `SliceDerivContinuous` holds. -/
theorem sliceDerivContinuous_of (hA : UnforcedLeray.Short.PartIIa.AgeDerivSmooth) :
    UnforcedLeray.Short.PartIIa.SliceDerivContinuous := by
  unfold UnforcedLeray.Short.PartIIa.SliceDerivContinuous
  intro G hG b ℓ s hs
  -- joint smoothness of the age derivative of order `ℓ`
  have hH : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1)
      (Ioi 0 ×ˢ univ) := hA.1 G hG ℓ
  -- restriction to the slice at age `s`: `η ↦ H (s, η)` is smooth on all of `ℝ`
  have hφ : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) := by
    intro e _
    exact ⟨hs, trivial⟩
  have hcomp : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1) ∘ (fun e : ℝ => ((s, e) : ℝ × ℝ)))
      univ :=
    hH.comp (contDiffOn_univ.mpr hφ) hmaps
  have hslice : ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => G r e) s) :=
    contDiffOn_univ.mp hcomp
  -- the `b`-th derivative of a `C^∞` function on `ℝ` is continuous
  exact ContDiff.continuous_iteratedDeriv b hslice (by exact_mod_cast le_top)

end UnforcedLeray.Short.PartIIa
