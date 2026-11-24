import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1

/-!
# Level compatibility for `rhsFamily_of` (task `PartI:T02/1/4/4/1/4`)

Helper lemmas for `RhsFamilyOf.lean`:

* `pd_restrict_comm`: restriction commutes with the weak partial derivative;
* `hLap_restrict`: restriction commutes with `hLap`;
* `measure_zero_eq`: the order-zero measure of the cylinder scale is the cell measure;
* `advection_restrict`: restriction carries the advection map of level `k + 3` to the level-3
  advection map `B0`, a.e. (hence in `H^3`, by `Sob.W.value_injective`);
* `restrict_three_self`, `restrict_zero_three`: restriction to the same level is the identity.

Every step is `Sob.W.value_injective` followed by `rfl` (`value_restrict`, `value_partialDeriv`,
`deriv_restrict` are `rfl`), or a.e. reasoning on `hVal`; the proof is complete with no placeholders.
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

/-- Restriction commutes with the weak partial derivative (`value_partialDeriv`,
`deriv_restrict` and `Idx.castLE` on words starting with `i` are `rfl`). -/
theorem pd_restrict_comm (c : ℝ) (i : Fin 2) {j m : ℕ} (h : j ≤ m)
    (x : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) :
    (Sob.W.restrict h (Sob.W.partialDeriv (k := m) i x) : Cyl.H ℝ Cyl.Vec2 c 0 j) =
      Sob.W.partialDeriv (k := j) i (Sob.W.restrict (Nat.add_le_add_right h 1) x) := by
  apply Sob.W.value_injective
  rfl

/-- Restriction commutes with `hLap` (a sum of composites of partial derivatives). -/
theorem hLap_restrict (c : ℝ) {j m : ℕ} (h : j ≤ m) (v : Cyl.H ℝ Cyl.Vec2 c 0 (m + 2)) :
    (Sob.W.restrict h (hLap c m v) : Cyl.H ℝ Cyl.Vec2 c 0 j) =
      hLap c j (Sob.W.restrict (Nat.add_le_add_right h 2) v) := by
  unfold hLap
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pd_restrict_comm c i h, pd_restrict_comm c i (Nat.add_le_add_right h 1)]

/-- The order-zero measure of the cylinder scale is the cell measure (`ρw c ^ 0 = 1`). -/
theorem measure_zero_eq (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.cylinder_μ_eq]
  unfold Sob.wμ
  simp only [Cyl.ρwW_rpow_apply, Real.rpow_zero, ENNReal.ofReal_one]
  simp

/-- **Advection restriction.**  The level-`m` advection map restricts to the level-3 one:
`restrict (B a b) = B0 (restrict a) (restrict b)` in `H^3`.  Both sides have the a.e. value
`∑_i a_i ∂_i b` (the derivatives agree after restriction by `pd_restrict_comm`). -/
theorem advection_restrict (c : ℝ) {m : ℕ} (hm : 3 ≤ m)
    (B : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ]
      Cyl.H ℝ Cyl.Vec2 c 0 m)
    (hB : IsAdvectionOp c m B)
    (B0 : Cyl.H ℝ Cyl.Vec2 c 0 (3 + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (3 + 1) →L[ℝ]
      Cyl.H ℝ Cyl.Vec2 c 0 3)
    (hB0 : IsAdvectionOp c 3 B0) (a b : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) :
    (Sob.W.restrict hm (B a b) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      B0 (Sob.W.restrict (Nat.add_le_add_right hm 1) a)
        (Sob.W.restrict (Nat.add_le_add_right hm 1) b) := by
  apply Sob.W.value_injective
  have hae : ∀ f g : Plane → Cyl.Vec2, f =ᵐ[Cyl.cellμ c] g →
      f =ᵐ[Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))] g := by
    intro f g h
    rw [measure_zero_eq c]
    exact h
  apply Lp.ext
  apply hae
  have hpd : ∀ i : Fin 2,
      hVal (Sob.W.partialDeriv (k := 3) i
        (Sob.W.restrict (Nat.add_le_add_right hm 1) b)) =
        hVal (Sob.W.partialDeriv (k := m) i b) := by
    intro i
    exact congrArg hVal (pd_restrict_comm c i hm b).symm
  have key : hVal (B a b) =ᵐ[Cyl.cellμ c]
      hVal (B0 (Sob.W.restrict (Nat.add_le_add_right hm 1) a)
        (Sob.W.restrict (Nat.add_le_add_right hm 1) b)) := by
    filter_upwards [hB a b, hB0 (Sob.W.restrict (Nat.add_le_add_right hm 1) a)
      (Sob.W.restrict (Nat.add_le_add_right hm 1) b)] with z hz1 hz2
    rw [hz1, hz2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpd i]
    rfl
  exact key

/-- Restriction to the same level is the identity. -/
theorem restrict_three_self (c : ℝ) (x : Cyl.H ℝ Cyl.Vec2 c 0 3) :
    (Sob.W.restrict (le_refl 3) x : Cyl.H ℝ Cyl.Vec2 c 0 3) = x := by
  apply Sob.W.value_injective
  rfl

/-- Restriction from `H^{0+3}` to `H^3` is the identity. -/
theorem restrict_zero_three (c : ℝ) (x : Cyl.H ℝ Cyl.Vec2 c 0 (0 + 3)) :
    (Sob.W.restrict (Nat.le_add_left 3 0) x : Cyl.H ℝ Cyl.Vec2 c 0 3) = x := by
  apply Sob.W.value_injective
  rfl

end UnforcedLeray.Short.PartI
