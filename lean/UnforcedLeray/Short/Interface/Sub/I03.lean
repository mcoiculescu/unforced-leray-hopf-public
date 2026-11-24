import UnforcedLeray.Short.Interface.Statements

/-!
# Interface leaf 1 (`L3BackgroundOfPath`): conditional assembly

Source of record: `the November 2 reference manuscript`, lines 6064-6070
("Gaussian convolution and the bounds on `a` give ... Hence `U ∈ C_per C₀`, `∇U ∈ C_per L³`").

Leaf 1 splits into two analytic facts about continuous periodic paths:

* `C0PathProps` (task `Interface:I01`, target of `c0Path_props`): a continuous `P`-periodic
  `C₀`-valued path `V` is continuous in space at every phase, uniformly bounded, jointly
  continuous in `(τ, y)`, and periodic as a path of functions.
* `L3PathRepProp` (task `Interface:I02`, target of `l3Path_rep`): a continuous `P`-periodic
  `L³`-valued path `W` has a representative `dW` that is periodic for every phase, jointly
  a.e.-strongly measurable, equal a.e. to `W τ` at every phase, with uniformly bounded `L³` norm.

`l3BackgroundOfPath_of` assembles Leaf 1 from them. The unconditional theorem
`l3BackgroundOfPath` is the task `Interface:I03` (`Short/Interface/Leaf1.lean`), which applies
`l3BackgroundOfPath_of` to the proved `c0Path_props` and `l3Path_rep`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- Sub-lemma 1 of Leaf 1 (lines 6064-6070, `U ∈ C_per C₀`); proved as `c0Path_props`
(task `Interface:I01`, file `Short/Interface/Leaf1_Value.lean`). -/
def C0PathProps : Prop :=
  ∀ {P : ℝ} (hP : 0 < P) (V : ℝ → ZeroAtInftyContinuousMap Space Space) (hVc : Continuous V)
    (hVp : Function.Periodic V P),
    (∀ τ, Continuous (V τ : SpatialField)) ∧ (∃ C : ℝ, ∀ τ y, ‖(V τ : SpatialField) y‖ ≤ C) ∧
      Continuous (fun z : SpaceTime => (V z.1 : SpatialField) z.2) ∧
      Function.Periodic (fun τ => (V τ : SpatialField)) P

/-- Sub-lemma 2 of Leaf 1 (lines 6064-6070, `∇U ∈ C_per L³`); proved as `l3Path_rep`
(task `Interface:I02`, file `Short/Interface/Leaf1_Deriv.lean`). -/
def L3PathRepProp : Prop :=
  ∀ {P : ℝ} (hP : 0 < P) (W : ℝ → Lp Space 3 (volume : Measure Space)) (hWc : Continuous W)
    (hWp : Function.Periodic W P),
    ∃ dW : ℝ → SpatialField, Function.Periodic dW P ∧
      AEStronglyMeasurable (fun z : SpaceTime => dW z.1 z.2) volume ∧
      (∀ τ, dW τ =ᵐ[volume] (W τ : SpatialField)) ∧
      ∃ C : ℝ, ∀ τ, eLpNorm (dW τ) 3 volume ≤ ENNReal.ofReal C

/-- Leaf 1 from its two sub-lemmas. The regular background is the `C₀` path `V` itself; the
weak derivative `∂_j V τ` is the representative `dV j τ` of the `L³` path `W · j`, transported
along `V τ =ᵐ U τ` and `dV j τ =ᵐ W τ j` by `HasWeakSpatialDerivative.congr`. -/
theorem l3BackgroundOfPath_of (h₁ : C0PathProps) (h₂ : L3PathRepProp) : L3BackgroundOfPath := by
  intro P U V W hP hVc hVp hVU hWc hWp hWd
  obtain ⟨hcont, hbdd, hjoint, hper⟩ := h₁ hP V hVc hVp
  have hrep : ∀ j : Fin 3, ∃ dW : ℝ → SpatialField, Function.Periodic dW P ∧
      AEStronglyMeasurable (fun z : SpaceTime => dW z.1 z.2) volume ∧
      (∀ τ, dW τ =ᵐ[volume] (W τ j : SpatialField)) ∧
      ∃ C : ℝ, ∀ τ, eLpNorm (dW τ) 3 volume ≤ ENNReal.ofReal C := by
    intro j
    refine h₂ hP (fun τ => W τ j) ((continuous_apply j).comp hWc) ?_
    intro τ
    exact congrFun (hWp τ) j
  choose dV hdVp hdVm hdVe hdVC using hrep
  choose Cj hCj using hdVC
  refine ⟨dV, hper, hcont, hbdd, hjoint.aestronglyMeasurable, hdVp, hdVm, ?_, ?_⟩
  · intro τ j
    exact (hWd τ j).congr (hVU τ).symm (hdVe j τ).symm
  · refine ⟨∑ i, |Cj i|, ?_⟩
    intro τ j
    refine ⟨(Lp.memLp (W τ j)).ae_eq (hdVe j τ).symm, ?_⟩
    refine (hCj j τ).trans (ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self (Cj j)).trans
      (Finset.single_le_sum (f := fun i => |Cj i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))

end UnforcedLeray.Short.Interface
