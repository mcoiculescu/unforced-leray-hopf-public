import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.RhsFamilyOf.Restrict

/-!
# Part I, task `PartI:T02/1/4/4/1/4`: the family `R_k` (`rhsFamily_of`, conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Given the bounded advection maps `B_m : H^{m+1} × H^{m+1} → H^m` (`AdvectionBilinear`, `m ≥ 3`)
and the Leray projections `P_m` on `H^m` restricting to `P₀` (`LerayLevels`), the family

  `R_k v = ν • hLap c (k+3) v - P_{k+3} (B_{k+3} (res v) (res v))`,  `res = restrict : H^{k+5} → H^{k+4}`,

is smooth (a continuous linear map minus the composite of a bounded bilinear map with the
continuous diagonal, then a continuous linear map), satisfies `IsRhsOp` at level `0` (the
advection term of `w ∈ H^5` is `A = B_3 (res w) (res w)`, `P_3 = P₀` on `H^3`), and is compatible
with restriction (`hLap_restrict`, `advection_restrict`, `P_{k+3}` restricts to `P₀`, `restrict_restrict`).

Helper lemmas are in `RhsFamilyOf/Restrict.lean`; the proof is complete with no placeholders.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **Assembly of the family `R_k`** (`RhsFamily`) from the product estimate `AdvectionBilinear`
and the Leray levels `LerayLevels`.  See the module docstring for the construction. -/
theorem rhsFamily_of (hAdv : AdvectionBilinear) (hLer : LerayLevels) : RhsFamily := by
  intro ν c hν hc hc1
  -- the advection maps `B k : H^{k+4} × H^{k+4} → H^{k+3}` and the Leray maps `P k` on `H^{k+3}`
  have hBk : ∀ k : ℕ, ∃ B : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3 + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (k + 3 + 1) →L[ℝ]
      Cyl.H ℝ Cyl.Vec2 c 0 (k + 3), IsAdvectionOp c (k + 3) B :=
    fun k => hAdv c hc hc1 (k + 3) (Nat.le_add_left 3 k)
  choose B hB using hBk
  have hPk : ∀ k : ℕ, ∃ P : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (k + 3),
      ∀ x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3),
        (Sob.W.restrict (Nat.le_add_left 3 k) (P x) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
          P0H3CLM hc (Sob.W.restrict (Nat.le_add_left 3 k) x : Cyl.H ℝ Cyl.Vec2 c 0 3) :=
    fun k => hLer c hc (k + 3) (Nat.le_add_left 3 k)
  choose P hP using hPk
  -- at level `3` the Leray map `P 0` is `P0H3CLM`
  have hPid : ∀ x : Cyl.H ℝ Cyl.Vec2 c 0 3, P 0 x = P0H3CLM hc x := by
    intro x
    apply restrict_injective c (Nat.le_add_left 3 0)
    rw [hP 0 x, restrict_zero_three c x, restrict_zero_three c (P0H3CLM hc x)]
  -- smoothness of the candidate `R_k`
  have hsm : ∀ k : ℕ, ContDiff ℝ ∞ (fun v : Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) =>
      ν • hLap c (k + 3) v - P k (B k (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v)
        (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v))) := by
    intro k
    have hres : ContDiff ℝ ∞ (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) :
        Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (k + 3 + 1)) :=
      ContinuousLinearMap.contDiff _
    have hbil : ContDiff ℝ ∞ (fun p : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3 + 1) ×
        Cyl.H ℝ Cyl.Vec2 c 0 (k + 3 + 1) => B k p.1 p.2) :=
      (B k).isBoundedBilinearMap.contDiff
    have hquad : ContDiff ℝ ∞ (fun v : Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) =>
        B k (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v)
          (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v)) :=
      hbil.comp (hres.prodMk hres)
    have hlin : ContDiff ℝ ∞ (fun v : Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) => ν • hLap c (k + 3) v) :=
      (ν • hLap c (k + 3)).contDiff
    exact hlin.sub ((P k).contDiff.comp hquad)
  refine ⟨fun k v => ν • hLap c (k + 3) v - P k (B k (Sob.W.restrict
      (show k + 3 + 1 ≤ k + 2 + 3 by omega) v) (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v)),
    hsm, ?_, ?_⟩
  · -- `IsRhsOp` at level `0`
    unfold IsRhsOp
    refine ⟨(hsm 0).continuous, fun w => ?_⟩
    refine ⟨B 0 (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)
      (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w), ?_, ?_⟩
    · exact hB 0 (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)
        (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)
    · show ν • hLap c (0 + 3) w - P 0 (B 0 (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)
          (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)) =
        ν • hLap c 3 w - P0H3CLM hc (B 0 (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w)
          (Sob.W.restrict (by omega : 0 + 3 + 1 ≤ 5) w))
      rw [hPid]
  · -- compatibility with restriction
    intro k v
    dsimp only
    have e1 : (Sob.W.restrict (Nat.add_le_add_right (Nat.le_add_left 3 k) 1)
        (Sob.W.restrict (show k + 3 + 1 ≤ k + 2 + 3 by omega) v) : Cyl.H ℝ Cyl.Vec2 c 0 (3 + 1)) =
        Sob.W.restrict (show 3 + 1 ≤ 5 by omega)
          (Sob.W.restrict (show 5 ≤ k + 2 + 3 by omega) v) := by
      apply Sob.W.value_injective
      rfl
    rw [map_sub, map_smul, hLap_restrict c (Nat.le_add_left 3 k) v, hP k,
      advection_restrict c (Nat.le_add_left 3 k) (B k) (hB k) (B 0) (hB 0), e1, hPid]

end UnforcedLeray.Short.PartI
