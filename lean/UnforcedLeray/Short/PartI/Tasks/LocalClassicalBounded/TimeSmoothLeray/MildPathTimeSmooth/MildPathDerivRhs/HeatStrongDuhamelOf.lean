import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ViscousSemigroup
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupJointContinuous

/-!
# Part I, task `PartI:T02/1/4/4/1/9`: the strong Duhamel formula for the `H^3` heat semigroup
(conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `heatStrongDuhamel_of : HeatGeneratorH5 → AbstractStrongDuhamel → HeatStrongDuhamel`
(the `Lemma S` of `Short/PartI/Sub/T02_1_4_4_1.lean`).

Proof: instantiate the abstract strong Duhamel lemma `AbstractStrongDuhamel` with
* `X = VectorH3 c` (the `H^3` space), `Y = H^5`,
* `j = Sob.W.restrict (3 ≤ 5)` (restriction `H^5 → H^3`),
* `L = ν • hLap c 3` (the viscous Laplacian as a bounded map `H^5 → H^3`),
* `S θ = heatVecH3Semigroup (θ := ν θ)` (the viscous `H^3` heat semigroup),
* `v = extendCompactPath hT.le ub` and the given `G`.

The hypotheses of `AbstractStrongDuhamel` are discharged by the library:
contraction (`norm_heatVecH3Semigroup_le_one`), `S 0 = id`
(`heatVecH3Semigroup_eq_id_of_nonpos`), the semigroup law
(`heatVecH3Semigroup_viscous_comp_of_nonneg`), strong continuity
(`continuous_heatVecH3Semigroup_joint`), and the generator property `HeatGeneratorH5`.
The endpoint and mild-equation conversions use `extendCompactPath_apply_of_mem`.
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

/-- **Lemma S** (strong Duhamel for the `H^3` heat semigroup with an `H^5` solution): the leaves
`HeatGeneratorH5` and `AbstractStrongDuhamel` imply `HeatStrongDuhamel`. -/
theorem heatStrongDuhamel_of (hG : HeatGeneratorH5) (hA : AbstractStrongDuhamel) :
    HeatStrongDuhamel := by
  intro ν c hν hc T hT ub G hmild
  -- the restriction `H^5 → H^3`, the generator `ν • hLap`, and the viscous heat family
  let j : Cyl.H ℝ Cyl.Vec2 c 0 5 →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 3 :=
    Sob.W.restrict (by norm_num : 3 ≤ 5)
  let L : Cyl.H ℝ Cyl.Vec2 c 0 5 →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 3 := ν • hLap c 3
  let S : ℝ → (Cyl.H ℝ Cyl.Vec2 c 0 3 →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 3) := fun θ =>
    HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * θ) hc
  have hnorm : ∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1 := fun θ _ =>
    HeatCylinder.norm_heatVecH3Semigroup_le_one (c := c) (θ := ν * θ) hc
  have h0 : S 0 = ContinuousLinearMap.id ℝ (Cyl.H ℝ Cyl.Vec2 c 0 3) := by
    show HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * 0) hc = _
    rw [mul_zero]
    exact HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl (0 : ℝ))
  have hcomp : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (S a).comp (S b) = S (a + b) := fun a b ha hb =>
    HeatCylinder.heatVecH3Semigroup_viscous_comp_of_nonneg hc hν.le ha hb
  have hcont : ∀ x : Cyl.H ℝ Cyl.Vec2 c 0 3, Continuous fun θ : ℝ => S θ x := by
    intro x
    have hmul : Continuous fun θ : ℝ => ν * θ := continuous_const.mul continuous_id
    have hpair : Continuous fun θ : ℝ => ((ν * θ, x) : ℝ × Cyl.H ℝ Cyl.Vec2 c 0 3) :=
      hmul.prodMk continuous_const
    exact (HeatCylinder.continuous_heatVecH3Semigroup_joint hc).comp hpair
  have hgen : ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 5,
      Tendsto (fun h : ℝ => h⁻¹ • (S h (j y) - j y)) (𝓝[>] (0 : ℝ)) (𝓝 (L y)) :=
    fun y => hG ν c hν hc y
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hmild' : ∀ t ∈ Icc (0 : ℝ) T,
      j (extendCompactPath hT.le ub t) =
        S t (j (extendCompactPath hT.le ub 0)) - ∫ r in (0 : ℝ)..t, S (t - r) (G r) := by
    intro t ht
    rw [extendCompactPath_apply_of_mem hT.le ub ht,
      extendCompactPath_apply_of_mem hT.le ub h0mem]
    exact hmild t ht
  have key := hA (VectorH3 c) (Cyl.H ℝ Cyl.Vec2 c 0 5) j L S hnorm h0 hcomp hcont hgen
    T hT ⇑G (extendCompactPath hT.le ub) G.continuous (extendCompactPath hT.le ub).continuous
    hmild'
  intro t ht
  have hk := key t ht
  rw [extendCompactPath_apply_of_mem hT.le ub ht,
    extendCompactPath_apply_of_mem hT.le ub h0mem] at hk
  exact hk

end UnforcedLeray.Short.PartI
