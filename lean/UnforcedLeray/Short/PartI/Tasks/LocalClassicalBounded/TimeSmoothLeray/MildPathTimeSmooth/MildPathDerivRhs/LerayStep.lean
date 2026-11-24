import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.P0WeakDeriv

/-!
# Part I, task `PartI:T02/1/4/4/1/3`: `LerayStep` (`P₀` climbs one level of `H^m`)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the mild solution is smooth; the Leray projection `P₀`
preserves every `H^m`, `m ≥ 3`).

Target: `LerayStep` (`Short/PartI/Sub/T02_1_4_4_1.lean`): `LerayAt c hc m hm → LerayAt c hc (m+1) _`.

## Strategy

1. Values decide elements.  `Sob.W.value_injective` and `value_restrict` (`rfl`) show that an
   identity in `H^3` is an identity of `L²` values, so `LerayAt (m+1)` only asks for a bounded
   operator `Q` on `H^{m+1}` with `value (Q x) = value (P (res x))`.
2. `Q` is `Sob.W.ofFields` made linear.  Its components (index `∅`: the value of `P (res x)`;
   index `cons j β`: the `β`-derivative of `P (∂_j x)`) are bounded linear maps into the tuple
   space `Sob.SobTuple`, and the codomain is restricted to the Sobolev graph `Sob.SobSub`
   (`ContinuousLinearMap.codRestrict`).  Linearity and boundedness are then automatic.
3. Membership in the graph needs the weak relations
   `HasWeakDeriv [∂_j] (value (P (res x))) (value (P (∂_j x)))` (`keyAux`).  They follow from the
   `H^3` commutation `p0WeakDeriv_proof` (`P0WeakDeriv`): `value (P y) = value (P₀ (res₃ y))` by
   `LerayAt` at level `m`, and weak derivatives only see `L²` values.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

namespace LerayStepAux

/-- Restriction does not change the `L²` value (`value_restrict` is `rfl`). -/
theorem valRestrictAux {c : ℝ} {k' k : ℕ} (h : k' ≤ k) (y : Cyl.H ℝ Cyl.Vec2 c 0 k) :
    Cyl.H.val (Sob.W.restrict h y : Cyl.H ℝ Cyl.Vec2 c 0 k') = Cyl.H.val y := rfl

/-- The component of index `α` of the lift of `x ∈ H^{m+1}`: at the empty word the value of
`P (res x)`, and at the word `cons j β` the `β`-derivative of `P (∂_j x)`. -/
def compAux {c : ℝ} {m : ℕ} (P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m) :
    Sob.Idx 2 (m + 1) →
      (Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ]
        Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
  | ⟨⟨0, _⟩, _⟩ =>
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2).comp
        (P.comp (Sob.W.restrict (Nat.le_succ m) :
          Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m))
  | ⟨⟨j + 1, hj⟩, f⟩ =>
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2
        ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩).comp
        (P.comp (Sob.W.partialDeriv (k := m) (f 0) :
          Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m))

/-- The lift as a bounded linear map into the Sobolev tuple space `Sob.SobTuple`. -/
def tupleAux {c : ℝ} {m : ℕ} (P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m) :
    Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ]
      Sob.SobTuple (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) Cyl.Vec2 (m + 1) 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sob.Idx 2 (m + 1) =>
      Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => compAux P α)

/-- The key weak-derivative relation: the `∂_j`-derivative of `P (res x)` is `P (∂_j x)`.
It is the `H^3` relation `P0WeakDeriv` read off at level `3`, since weak derivatives and `L²`
values do not see the level. -/
theorem keyAux {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 3 ≤ m)
    (P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m)
    (hP : ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 m,
      (Sob.W.restrict hm (P y) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        P0H3CLM hc (Sob.W.restrict hm y : Cyl.H ℝ Cyl.Vec2 c 0 3))
    (x : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) (j : Fin 2) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (P (Sob.W.restrict (Nat.le_succ m) x)) : Plane → Cyl.Vec2)
      (Cyl.H.val (P (Sob.W.partialDeriv (k := m) j x)) : Plane → Cyl.Vec2) := by
  have hx := Sob.W.hasWeakDeriv x (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 m))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hx
  have hw : Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (Sob.W.restrict (hm.trans (Nat.le_succ m)) x : Cyl.H ℝ Cyl.Vec2 c 0 3) :
        Plane → Cyl.Vec2)
      (Cyl.H.val (Sob.W.restrict hm (Sob.W.partialDeriv (k := m) j x) :
        Cyl.H ℝ Cyl.Vec2 c 0 3) : Plane → Cyl.Vec2) := by
    rw [valRestrictAux, valRestrictAux]
    exact hx
  have h3 := p0WeakDeriv_proof c hc j _ _ hw
  have hPv : ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 m,
      (Cyl.H.val (P y) : Plane → Cyl.Vec2) =
        (Cyl.H.val (P0H3CLM hc (Sob.W.restrict hm y : Cyl.H ℝ Cyl.Vec2 c 0 3)) :
          Plane → Cyl.Vec2) := by
    intro y
    rw [← hP y, valRestrictAux]
  have hA : (Sob.W.restrict hm (Sob.W.restrict (Nat.le_succ m) x) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      Sob.W.restrict (hm.trans (Nat.le_succ m)) x :=
    restrict_restrict c hm (Nat.le_succ m) (hm.trans (Nat.le_succ m)) x
  rw [hPv, hPv, hA]
  exact h3

/-- The lift lands in the Sobolev graph: its components are the weak derivatives of its value. -/
theorem memAux {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 3 ≤ m)
    (P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m)
    (hP : ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 m,
      (Sob.W.restrict hm (P y) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        P0H3CLM hc (Sob.W.restrict hm y : Cyl.H ℝ Cyl.Vec2 c 0 3))
    (x : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) :
    tupleAux P x ∈ Sob.SobSub (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (m + 1) 2 := by
  rw [Sob.mem_SobSub_iff]
  intro α
  rcases α with ⟨⟨j, hj⟩, f⟩
  cases j with
  | zero =>
    have e : (Sob.cylinder c).word (⟨⟨0, hj⟩, f⟩ : Sob.Idx 2 (m + 1)) = [] := by
      simp [Sob.TestDomain.word]
    rw [e]
    have hy := Sob.W.hasWeakDeriv (P (Sob.W.restrict (Nat.le_succ m) x))
      (Sob.Idx.zero : Sob.Idx 2 m)
    rw [Cyl.word_zero c] at hy
    exact hy
  | succ j =>
    have e : (Sob.cylinder c).word (⟨⟨j + 1, hj⟩, f⟩ : Sob.Idx 2 (m + 1)) =
        [(Sob.cylinder c).dir (f 0)] ++
          (Sob.cylinder c).word (⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ :
            Sob.Idx 2 m) := by
      simp [Sob.TestDomain.word, List.ofFn_succ]
    rw [e]
    exact (keyAux hc hm P hP x (f 0)).append
      (Sob.W.hasWeakDeriv (P (Sob.W.partialDeriv (k := m) (f 0) x))
        (⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, fun i => f i.succ⟩ : Sob.Idx 2 m))

/-- The lift `Q : H^{m+1} → H^{m+1}`: bounded linear, with the components of `P (res x)`. -/
def liftAux {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 3 ≤ m)
    (P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m)
    (hP : ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 m,
      (Sob.W.restrict hm (P y) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        P0H3CLM hc (Sob.W.restrict hm y : Cyl.H ℝ Cyl.Vec2 c 0 3)) :
    Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) :=
  (tupleAux P).codRestrict
    (Sob.SobSub (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (m + 1) 2)
    (fun x => memAux hc hm P hP x)

end LerayStepAux

/-- **`LerayStep`** (source lines 261-288): the Leray projection on `H^m` extends to `H^{m+1}`.
Proof: `LerayStepAux.liftAux` with the value identity `valRestrictAux`, `LerayAt` at level `m`
and `restrict_restrict`. -/
theorem lerayStep : LerayStep := by
  intro c hc m hm hLer
  obtain ⟨P, hP⟩ := hLer
  refine ⟨LerayStepAux.liftAux hc hm P hP, fun x => ?_⟩
  have hA : (Sob.W.restrict hm (Sob.W.restrict (Nat.le_succ m) x) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      Sob.W.restrict (hm.trans (Nat.le_succ m)) x :=
    restrict_restrict c hm (Nat.le_succ m) (hm.trans (Nat.le_succ m)) x
  have h2 : Cyl.H.val (P (Sob.W.restrict (Nat.le_succ m) x)) =
      Cyl.H.val (P0H3CLM hc (Sob.W.restrict (hm.trans (Nat.le_succ m)) x :
        Cyl.H ℝ Cyl.Vec2 c 0 3)) := by
    rw [← LerayStepAux.valRestrictAux hm (P (Sob.W.restrict (Nat.le_succ m) x)), hP, hA]
  have hL : Cyl.H.val (LerayStepAux.liftAux hc hm P hP x) =
      Cyl.H.val (P (Sob.W.restrict (Nat.le_succ m) x)) := rfl
  apply Sob.W.value_injective
  exact (LerayStepAux.valRestrictAux (hm.trans (Nat.le_succ m))
    (LerayStepAux.liftAux hc hm P hP x)).trans (hL.trans h2)

#print axioms UnforcedLeray.Short.PartI.lerayStep

end UnforcedLeray.Short.PartI
