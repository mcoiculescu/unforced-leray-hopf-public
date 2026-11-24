import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T02/3`: `ReflectPressureDecay` (leaf of `ClassicalOdd`)

Source of record: `the November 2 reference manuscript`, line 288 ("Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`"). The Prop `ReflectPressureDecay` is defined in
`Short/PartI/Sub/T02_3.lean`: for every `T` and every `p` with `PressureDecayOn T p`, the reflected
pressure `reflP p s z = p s (-z)` again satisfies `PressureDecayOn T`.

## What is proved here

`reflectPressureDecay : ReflectPressureDecay`. The map `z ↦ -z` sends the filter
`comap (fun z => |z.2|) atTop` to itself, because `|(-z).2| = |z.2|`. Composing the decay of `p s`
with this filter map gives the decay of `p s ∘ neg = reflP p s`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The negation map `z ↦ -z` on the plane preserves the filter of `|η| → ∞`. -/
theorem rp_neg_tendsto :
    Tendsto (fun z : Plane => -z) (comap (fun z : Plane => |z.2|) atTop)
      (comap (fun z : Plane => |z.2|) atTop) := by
  rw [Filter.tendsto_comap_iff]
  have e : ((fun z : Plane => |z.2|) ∘ (fun z : Plane => -z)) = fun z : Plane => |z.2| := by
    funext z
    simp [abs_neg]
  rw [e]
  exact Filter.tendsto_comap

/-- Reflection preserves pressure decay: if `p` tends to `0` along `|η| → ∞` on `[0,T]`, so does
`reflP p`. -/
theorem reflectPressureDecay : ReflectPressureDecay := by
  intro T p hp s hs
  exact (hp s hs).comp rp_neg_tendsto

end UnforcedLeray.Short.PartI
