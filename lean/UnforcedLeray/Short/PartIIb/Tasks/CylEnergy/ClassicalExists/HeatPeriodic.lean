import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!


Statement `HeatPeriodic` (`Sub/T22_1/Stages.lean`): if `g (x.1 + c, x.2) = g x` for all `x`, then
`heatSG a g` and `heatSGd i a g` are `c`-periodic in the first variable, for every `a`.

Proof. Write `w = (c, 0)`, so `(x.1 + c, x.2) = x + w`. The kernel integral
`∫ K(x + w - y) g(y) dy` is invariant under `y ↦ y + w` (`integral_add_right_eq_self`), and after
the substitution `K(x + w - (y + w)) g(y + w) = K(x - y) g(y)`, using `x + w - (y + w) = x - y` and
the periodicity of `g`. The case `a ≤ 0` of `heatSG` is `g` itself, which is periodic by hypothesis.
`heatSGd` has no case split, so the same substitution covers all `a`.

Source of record: `the November 2 reference manuscript`, lines 2074-2093 and
2103-2105 (the cylinder equation and the smoothing). The statement is standard heat-kernel calculus.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- Shift invariance of a kernel integral against a `w`-periodic function, with `w = (c, 0)`. -/
theorem heatPeriodic_shift (K : Pl → ℝ) (g : Pl → ℝ) (c : ℝ)
    (hper : ∀ y : Pl, g (y + ((c, 0) : Pl)) = g y) (x : Pl) :
    ∫ y : Pl, K (x + ((c, 0) : Pl) - y) * g y = ∫ y : Pl, K (x - y) * g y := by
  calc ∫ y : Pl, K (x + ((c, 0) : Pl) - y) * g y
      = ∫ y : Pl, K (x + ((c, 0) : Pl) - (y + ((c, 0) : Pl))) * g (y + ((c, 0) : Pl)) :=
        (integral_add_right_eq_self (μ := volume)
          (fun y : Pl => K (x + ((c, 0) : Pl) - y) * g y) ((c, 0) : Pl)).symm
    _ = ∫ y : Pl, K (x - y) * g y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [hper y, show x + ((c, 0) : Pl) - (y + ((c, 0) : Pl)) = x - y by abel]

/-- **`T22/1/5`** `q`-periodicity (here `c`-periodicity in the first variable) is preserved by the
heat semigroup and by its derivative kernels. -/
theorem heatPeriodic : UnforcedLeray.Short.IIb.CylPDE.HeatPeriodic := by
  intro c g hg a x
  have hper : ∀ y : Pl, g (y + ((c, 0) : Pl)) = g y := fun y => by
    have e : y + ((c, 0) : Pl) = (y.1 + c, y.2) := by ext <;> simp
    rw [e]
    exact hg y
  have hx : ((x.1 + c, x.2) : Pl) = x + ((c, 0) : Pl) := by ext <;> simp
  rw [hx]
  refine ⟨?_, fun i => ?_⟩
  · unfold heatSG
    split_ifs with h
    · exact hper x
    · exact heatPeriodic_shift (heatK a) g c hper x
  · unfold heatSGd
    exact heatPeriodic_shift (heatKd i a) g c hper x

end CylPDE

end UnforcedLeray.Short.IIb
