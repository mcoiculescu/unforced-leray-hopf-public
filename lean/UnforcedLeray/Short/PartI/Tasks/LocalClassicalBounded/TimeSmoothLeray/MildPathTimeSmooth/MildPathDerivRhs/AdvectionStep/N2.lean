import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The components of the glued field: the empty word gives the value of `x`, and the word
`cons j β` gives the `β`-th derivative of `y j`. -/
def gluedComp {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m) (y : Fin 2 → Cyl.H ℝ Cyl.Vec2 c 0 m) :
    Sob.Idx 2 (m + 1) → Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
  fun α => match α with
    | ⟨⟨0, _⟩, _⟩ => Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x
    | ⟨⟨j + 1, h⟩, w⟩ => Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2
        ⟨⟨j, by omega⟩, Fin.tail w⟩ (y (w 0))

theorem gluedComp_zero {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m)
    (y : Fin 2 → Cyl.H ℝ Cyl.Vec2 c 0 m) :
    gluedComp x y Sob.Idx.zero = Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x :=
  rfl

theorem gluedComp_cons {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m)
    (y : Fin 2 → Cyl.H ℝ Cyl.Vec2 c 0 m) (i : Fin 2) (β : Sob.Idx 2 m) :
    gluedComp x y (Sob.Idx.cons i β) =
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 β (y i) :=
  rfl

/-- Each component of the glued field is a weak derivative of the zero component. -/
theorem gluedComp_hw {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m)
    (y : Fin 2 → Cyl.H ℝ Cyl.Vec2 c 0 m)
    (hy : ∀ j : Fin 2, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] (hVal x) (hVal (y j)))
    (α : Sob.Idx 2 (m + 1)) :
    Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
      (⇑(gluedComp x y Sob.Idx.zero)) (⇑(gluedComp x y α)) := by
  obtain ⟨⟨j, hj⟩, w⟩ := α
  cases j with
  | zero =>
    have e : (⟨⟨0, hj⟩, w⟩ : Sob.Idx 2 (m + 1)) = Sob.Idx.zero := by
      congr 1
      exact Subsingleton.elim _ _
    rw [e]
    have h0 := Sob.W.hasWeakDeriv x (Sob.Idx.zero : Sob.Idx 2 m)
    rw [Sob.TestDomain.word_zero] at h0 ⊢
    exact h0
  | succ j =>
    have eα : (⟨⟨j + 1, hj⟩, w⟩ : Sob.Idx 2 (m + 1)) =
        Sob.Idx.cons (w 0) ⟨⟨j, by omega⟩, Fin.tail w⟩ :=
      Sigma.ext rfl (heq_of_eq (Fin.cons_self_tail w).symm)
    rw [eα, Sob.TestDomain.word_cons, gluedComp_cons]
    have hA := hy (w 0)
    have hB := Sob.W.hasWeakDeriv (y (w 0)) (⟨⟨j, by omega⟩, Fin.tail w⟩ : Sob.Idx 2 m)
    exact hA.append hB

/-- **Lemma N2 (gluing of the first derivatives).** -/
theorem cylGlueFirstOrder : CylGlueFirstOrder := by
  intro c m x y hy
  refine ⟨Sob.W.ofFields (fun α => (gluedComp x y α : Plane → Cyl.Vec2))
    (fun α => Lp.memLp _) (fun α => gluedComp_hw x y hy α), ?_, ?_⟩
  · unfold hVal
    rw [Sob.W.value_ofFields]
    have h1 := MemLp.coeFn_toLp (Lp.memLp (gluedComp x y Sob.Idx.zero))
    exact h1.filter_mono (ae_cell_le c)
  · intro j
    unfold hVal
    rw [Sob.W.value_partialDeriv, Sob.W.deriv_ofFields]
    have h1 := MemLp.coeFn_toLp (Lp.memLp (gluedComp x y (Sob.Idx.cons j Sob.Idx.zero)))
    refine (h1.filter_mono (ae_cell_le c)).trans ?_
    rw [gluedComp_cons]
    exact Filter.EventuallyEq.rfl

end UnforcedLeray.Short.PartI
