import UnforcedLeray.Short.PartI.Sub.T02_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.SmoothPathsPersistent.OfPartials

/-!
# Part I, task `PartI:T02/1/2/6`: `SmoothPathsPersistent`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `smoothPathsPersistent : SmoothPathsPersistent` (`Short/PartI/Sub/T02_1_2.lean`): if a
continuous `H³` path `u` on `[0,T]` has derivative paths of every order (`SmoothPath n u` for all
`n`), then `u` lifts to `C([0,T], H^{k+3})` for every `k` (`PersistentFamily`).

Proof.

1. `derivPaths_of`: the first derivative paths of `a` are unique (`HasDerivPath.unique`), so each
   `∂_j a` is one fixed path `d_j`, and `d_j` again has all `SmoothPath n`.
2. `lift_aux` by induction on `m`: every `a` with all `SmoothPath n` lifts to `C([0,T], H^{m+3})`
   with the same `L²`-value.  The base is `a` itself.  The step lifts `d_0, d_1` (induction
   hypothesis) to `y_0, y_1 ∈ C([0,T], H^{m+3})` and then uses `ofPartials` (helper file
   `HkPersistence/SmoothPathsPersistent/OfPartials.lean`) to build `z ∈ C([0,T], H^{m+4})`.
3. `smoothPathsPersistent` is `lift_aux` for each `k`.

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

/-- The first derivative paths of a path with all derivative paths are themselves smooth: each
`∂_j a` is unique, so it is the first derivative of `a` in direction `j` for every `n`. -/
theorem derivPaths_of {c T : ℝ} {a : MPath c T} (hS : ∀ n : ℕ, SmoothPath c T n a) :
    ∀ j : Fin 2, ∃ d : MPath c T, HasDerivPath c T j a d ∧ ∀ n : ℕ, SmoothPath c T n d := by
  intro j
  obtain ⟨d, hd, -⟩ := smoothPath_succ.mp (hS 1) j
  refine ⟨d, hd, fun n => ?_⟩
  obtain ⟨d', hd', hs'⟩ := smoothPath_succ.mp (hS (n + 1)) j
  rw [← HasDerivPath.unique hd' hd]
  exact hs'

/-- **Lift by induction on the level.** Every `a` with all `SmoothPath n` lifts to a continuous
path in `H^{m+3}` with the same `H³`-restriction. -/
theorem lift_aux (c T : ℝ) (m : ℕ) : ∀ a : MPath c T, (∀ n : ℕ, SmoothPath c T n a) →
    ∃ ak : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 (m + 3)),
      ∀ t, Sob.W.restrict (Nat.le_add_left 3 m) (ak t) = a t := by
  induction m with
  | zero =>
    intro a _
    refine ⟨a, fun t => ?_⟩
    apply Sob.W.ext
    rfl
  | succ m ih =>
    intro a hS
    choose d hd hdS using derivPaths_of hS
    choose y hy using fun j => ih (d j) (hdS j)
    have hxy : ∀ (j : Fin 2) (t : Icc (0 : ℝ) T),
        Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
          (Cyl.H.val (a t) : Plane → Cyl.Vec2) (Cyl.H.val (y j t) : Plane → Cyl.Vec2) := by
      intro j t
      have hv : Cyl.H.val (d j t) = Cyl.H.val (y j t) := by
        rw [← hy j t]
        exact Sob.W.value_restrict _ _
      rw [← hv]
      exact hd j t
    obtain ⟨z, hzc, hzv⟩ := SmoothPathsPersistentAux.ofPartials
      (fun t => (a t : Cyl.H ℝ Cyl.Vec2 c 0 3)) (fun j t => y j t) a.continuous
      (fun j => (y j).continuous) hxy
    refine ⟨⟨z, hzc⟩, fun t => ?_⟩
    apply Sob.W.ext
    rw [Sob.W.value_restrict]
    exact hzv t

/-- **Task `PartI:T02/1/2/6`** (source lines 261-288): a path with all derivative paths
(`SmoothPath n u` for all `n`) is persistent: it lifts to `C([0,T], H^{k+3})` for every `k`. -/
theorem smoothPathsPersistent : SmoothPathsPersistent := by
  unfold SmoothPathsPersistent
  intro c T _hc _hT u hS
  unfold PersistentFamily
  intro k
  exact lift_aux c T k u hS

#print axioms UnforcedLeray.Short.PartI.smoothPathsPersistent

end UnforcedLeray.Short.PartI
