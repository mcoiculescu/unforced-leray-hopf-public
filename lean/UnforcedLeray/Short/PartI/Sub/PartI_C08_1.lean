import UnforcedLeray.Short.PartI.Sub.PartI_C08
import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1

/-!
# `PartI:C08/1`: decomposition of `MildOnPosImpliesCanonicalMild`

Source `the November 2 reference manuscript`
lines 1094-1125 ("Conversely every normalized solution satisfies the integrals").  Mirror image of
`PartI_C07_1_1`: a curve mild on `(0,∞)` for `Cons.G3b.S` is continuous on `[b,∞)`, satisfies the
full Duhamel equation `FullMildEq`, and (with the complementary evolution `U` supplied by the given
canonical mild `V₀`) the Dyson regrouping converse gives the coupled mild system.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray Set

/-- **Leaf A** (source 1094-1125, continuity on `[b,∞)`): a curve mild on `(0,∞)` is continuous on
`[b,∞)`, `b > 0`.  Sketch: for `θ ≤ θ'`, `V' θ = Cons.G3b.S θ θ' (V' θ')`; fix `θ' > ` any bound and
use strong continuity of `θ ↦ Cons.G3b.S θ θ' x` on `(0,θ']` (or `Spine.mildSpatialSmoothing`). -/
def MildOnPosContinuous : Prop :=
  ∀ (b : ℝ) (V' : ℝ → B0010.XG), 0 < b → Spine.IsMildOnPos V' → ContinuousOn V' (Ici b)

/-- **Leaf B** (source 1094-1125): a curve mild on `(0,∞)` for `Cons.G3b.S` satisfies the Duhamel
equation `FullMildEq` on `[b,∞)`.  Sketch: `Cons.G3b.S_mild` (the Duhamel identity of `S` for the
free evolution and the bounded perturbation `L₀`), applied to `V' θ = S θ θ' (V' θ')`. -/
def MildOnPosFullMildEq : Prop :=
  ∀ (b : ℝ) (V' : ℝ → B0010.XG), 0 < b → Spine.IsMildOnPos V' → FullMildEq b V'

/-- **Leaf C** (source 1094-1125, "Conversely ... satisfies the integrals", the converse of
`CoupledImpliesFullMild`): if `U` is the mild complementary evolution for the clock `canonicalClock b`
and `V'` is continuous on `[b,∞)` and satisfies `FullMildEq b`, then `(A, r)` with `W = e^{λθ}θ^κ V'`,
`A = ℓ W`, `r = W - A q` solves the coupled mild equations for `canonicalS U`.  Sketch: regroup the
Dyson series of the full generator along `Q = 1 - q⊗ℓ` (`Evolution.dyson_sum_regroup`,
`Cons.G3b.canonicalActualCoupling_mild_of_complement`; compare `CoupledImpliesFullMild`); Gronwall
for the bounded coupling maps against the mild complementary evolution (unique by
`MildComplementUnique`). -/
def FullMildImpliesCoupled : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd (canonicalClock b) U →
    ∀ V' : ℝ → B0010.XG, ContinuousOn V' (Ici b) → FullMildEq b V' →
      CoupledMild (canonicalS U) (seedQDq l q hq) (seedLD qd hqd) b
        (fun θ => l (canonicalW lam (seedKappa l q hq) V' θ))
        (fun θ => canonicalW lam (seedKappa l q hq) V' θ -
          l (canonicalW lam (seedKappa l q hq) V' θ) • q)

theorem mildOnPosImpliesCanonicalMild_of (hA : MildOnPosContinuous) (hB : MildOnPosFullMildEq)
    (hC : FullMildImpliesCoupled) : MildOnPosImpliesCanonicalMild := by
  intro lam q l hI qd hl hq hqd b hb V₀ hV₀ V' hV'
  obtain ⟨-, U, hU, -⟩ := hV₀
  exact ⟨hA b V' hb hV', U, hU, hC lam q l hI qd hl hq hqd b hb U hU V' (hA b V' hb hV')
    (hB b V' hb hV')⟩

end UnforcedLeray.Short.PartI
