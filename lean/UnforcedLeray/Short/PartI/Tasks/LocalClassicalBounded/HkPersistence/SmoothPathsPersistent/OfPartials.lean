import UnforcedLeray.Short.PartI.Sub.T02_1_2

/-!
# Part I, task `PartI:T02/1/2/6` (helper): one `H^{k+1}` element from its value and two partials

Source of record: `the November 2 reference manuscript`, lines 261-288.

Given continuous paths `x : X → H^r` and `y₀, y₁ : X → H^k` (on the cylinder `Sob.cylinder c`,
weight `ρw^0`) such that `y_j(t)` is the weak `∂_j`-derivative of `x(t)` at the value level, we build
a continuous path `z : X → H^{k+1}` with the same `L²`-value as `x`. The element is `Sob.W.ofFields`
with components `liftComp`: the value of `x` at the empty word, and at the word `cons j β` the
`β`-derivative of `y_j`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI.SmoothPathsPersistentAux

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The component fields of the lift of `(v, w)`: at the empty word the value `v`, and at the
word `cons j β` (with `j = f 0`) the `β`-derivative of `w j`. -/
def liftComp {c : ℝ} {r k : ℕ} (v : Cyl.H ℝ Cyl.Vec2 c 0 r) (w : Fin 2 → Cyl.H ℝ Cyl.Vec2 c 0 k) :
    Sob.Idx 2 (k + 1) →
      Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))
  | ⟨⟨0, _⟩, _⟩ => Cyl.H.val v
  | ⟨⟨j + 1, hj⟩, f⟩ =>
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 k 2
        ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ (w (f 0))

/-- **Lift of two partials.** If `y_j(t)` is the weak `∂_j`-derivative (value level) of `x(t)`,
and `x`, `y_j` are continuous, then there is a continuous `z : X → H^{k+1}` with the same
`L²`-value as `x` at every `t`. -/
theorem ofPartials {X : Type*} [TopologicalSpace X] {c : ℝ} {r k : ℕ}
    (x : X → Cyl.H ℝ Cyl.Vec2 c 0 r) (y : Fin 2 → X → Cyl.H ℝ Cyl.Vec2 c 0 k)
    (hx : Continuous x) (hy : ∀ j, Continuous (y j))
    (hxy : ∀ (j : Fin 2) (t : X), Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (x t) : Plane → Cyl.Vec2) (Cyl.H.val (y j t) : Plane → Cyl.Vec2)) :
    ∃ z : X → Cyl.H ℝ Cyl.Vec2 c 0 (k + 1), Continuous z ∧
      ∀ t, Cyl.H.val (z t) = Cyl.H.val (x t) := by
  have hw : ∀ (t : X) (α : Sob.Idx 2 (k + 1)),
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
        (liftComp (x t) (fun j => y j t) (Sob.Idx.zero : Sob.Idx 2 (k + 1)) : Plane → Cyl.Vec2)
        (liftComp (x t) (fun j => y j t) α : Plane → Cyl.Vec2) := by
    intro t α
    rcases α with ⟨⟨j, hj⟩, f⟩
    cases j with
    | zero =>
      have e : (Sob.cylinder c).word (⟨⟨0, hj⟩, f⟩ : Sob.Idx 2 (k + 1)) =
          (Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 (k + 1)) := by
        simp [Sob.TestDomain.word, Sob.Idx.zero]
      rw [e]
      exact Sob.W.hasWeakDeriv (x t) Sob.Idx.zero
    | succ j =>
      have e : (Sob.cylinder c).word (⟨⟨j + 1, hj⟩, f⟩ : Sob.Idx 2 (k + 1)) =
          [(Sob.cylinder c).dir (f 0)] ++
            (Sob.cylinder c).word (⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ :
              Sob.Idx 2 k) := by
        simp [Sob.TestDomain.word, List.ofFn_succ]
      rw [e]
      exact (hxy (f 0) t).append
        (Sob.W.hasWeakDeriv (y (f 0) t)
          (⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ : Sob.Idx 2 k))
  obtain ⟨Z, hZ⟩ : ∃ Z : X → Cyl.H ℝ Cyl.Vec2 c 0 (k + 1), ∀ t, Z t = Sob.W.ofFields
      (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 1)
      (p := 2) (fun α => (liftComp (x t) (fun j => y j t) α : Plane → Cyl.Vec2))
      (fun α => Lp.memLp _) (fun α => hw t α) :=
    ⟨fun t => Sob.W.ofFields (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Cyl.Vec2) (k := k + 1) (p := 2)
      (fun α => (liftComp (x t) (fun j => y j t) α : Plane → Cyl.Vec2))
      (fun α => Lp.memLp _) (fun α => hw t α), fun t => rfl⟩
  refine ⟨Z, ?_, ?_⟩
  · have hcomp : ∀ α : Sob.Idx 2 (k + 1), Continuous fun t => liftComp (x t) (fun j => y j t) α := by
      intro α
      rcases α with ⟨⟨j, hj⟩, f⟩
      cases j with
      | zero =>
        exact (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 r 2).continuous.comp hx
      | succ j =>
        exact (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 k 2
          (⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ : Sob.Idx 2 k)).continuous.comp
          (hy (f 0))
    apply continuous_induced_rng.2
    have hfun : (Subtype.val ∘ Z) = fun t => WithLp.toLp 2 (fun α => liftComp (x t) (fun j => y j t) α) := by
      funext t
      rw [Function.comp_apply, hZ t]
      exact congrArg (WithLp.toLp 2) (funext fun α => Lp.toLp_coeFn _ _)
    rw [hfun]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hcomp)
  · intro t
    rw [hZ t]
    refine (Sob.W.value_ofFields (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Cyl.Vec2) (k := k + 1) (p := 2) _ _ _).trans ?_
    exact Lp.toLp_coeFn _ _

#print axioms UnforcedLeray.Short.PartI.SmoothPathsPersistentAux.ofPartials

end UnforcedLeray.Short.PartI.SmoothPathsPersistentAux
