import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupP0

/-!
# Part I, task `PartI:T02/1/4/4/1`: the mild equation in semigroup form (from `HeatDivIdent`)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015: the mild solution is smooth for positive time).

Target: `mildDuhamelStrongForm_of (h : HeatDivIdent) : MildDuhamelStrongForm`, a conditional
theorem in which the leaf `HeatDivIdent` is taken as a hypothesis.

Proof outline.
* Evaluate the fixed-point equation `u = seed + projectedNonlinearDuhamelCompactMap u` at `t`.
  The nonlinear map is the negative of `projectedHeatNonlinearityIntegral`
  (`projectedNonlinearDuhamelCompactMap_apply`).
* The seed at `t ∈ [0,T]` is `P₀ (S(νt) d)` with `d = projectedInitialDatumH3`; since `d = u 0`
  is `P₀`-fixed and `P₀` commutes with `S`, this equals `S(νt) d`.
* For `r ∈ (0,t)`, `u r` is the restriction of `ub r`, and `HeatDivIdent` with the advection term
  `A_r` of `ub r` (`IsRhsOp`) identifies the integrand with `S(ν(t-r)) (ν Δub r - R0 (ub r))`.
* Pass from the open interval `Ioo 0 t` to the interval integral `∫ r in 0..t`.
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

set_option maxHeartbeats 1600000 in
/-- **Lemma D** (source lines 261-288): the mild equation in semigroup form, from the leaf
`HeatDivIdent`.  See the file docstring for the proof outline. -/
theorem mildDuhamelStrongForm_of (h : HeatDivIdent) : MildDuhamelStrongForm := by
  intro ν c hν hc hc1 T hT u hu ub hub R0 hR0 t ht
  obtain ⟨hmild, hP0, hu0⟩ := hu
  obtain ⟨-, hRop⟩ := hR0
  -- the value of the fixed-point equation at `t`
  have hstep : u ⟨t, ht⟩ = projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) t
      + -projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT.le u) t := by
    exact congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f ⟨t, ht⟩) hmild
  -- the initial datum is `P₀`-fixed, since it is the trace `u 0`
  have hPd : P0H3CLM hc (projectedInitialDatumH3 hc) = projectedInitialDatumH3 hc := by
    rw [← hu0]
    exact hP0 _
  -- the seed at time `t` is the heat semigroup applied to the datum
  have hseed : projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) t =
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * t) hc (projectedInitialDatumH3 hc) := by
    have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht.1
    change P0H3CLM hc (HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc
      (projectedInitialDatumH3 hc)) = _
    rw [max_eq_right hνt, HeatCylinder.heatVecH3Semigroup_P0H3CLM_comm, hPd]
  -- the integrand of the Duhamel term, pointwise on `(0,t)`
  have hpt : ∀ r ∈ Ioo (0 : ℝ) t,
      projectedHeatDuhamelOrbit (ν := ν) (s := t) hc
          (tensorH3StressPath hc1 (extendCompactPath hT.le u)) r =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * (t - r)) hc
          (ν • hLap c 3 (extendCompactPath hT.le ub r) - R0 (extendCompactPath hT.le ub r)) := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, le_trans hr.2.le ht.2⟩
    have hθ : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr hr.2)
    obtain ⟨A, hA, hRA⟩ := hRop (extendCompactPath hT.le ub r)
    have hsub : ν • hLap c 3 (extendCompactPath hT.le ub r) - R0 (extendCompactPath hT.le ub r) =
        P0H3CLM hc A := by
      rw [hRA]
      exact sub_sub_cancel _ _
    have hres : extendCompactPath hT.le u r =
        Sob.W.restrict (by norm_num : 3 ≤ 5) (extendCompactPath hT.le ub r) := by
      rw [extendCompactPath_apply_of_mem hT.le u hrI,
        extendCompactPath_apply_of_mem hT.le ub hrI, hub ⟨r, hrI⟩]
    have hPfix : P0H3CLM hc (Sob.W.restrict (by norm_num : 3 ≤ 5)
        (extendCompactPath hT.le ub r)) =
          Sob.W.restrict (by norm_num : 3 ≤ 5) (extendCompactPath hT.le ub r) := by
      rw [← hres, extendCompactPath_apply_of_mem hT.le u hrI]
      exact hP0 ⟨r, hrI⟩
    have hF : tensorH3StressPath hc1 (extendCompactPath hT.le u) r =
        tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) (extendCompactPath hT.le ub r))
          (Sob.W.restrict (by norm_num : 3 ≤ 5) (extendCompactPath hT.le ub r)) := by
      change tensorH3Bilinear hc1 (extendCompactPath hT.le u r)
        (extendCompactPath hT.le u r) = _
      rw [hres]
    unfold projectedHeatDuhamelOrbit
    rw [hF, h c hc hc1 (extendCompactPath hT.le ub r) A hPfix hA (ν * (t - r)) hθ, hsub]
  -- the Duhamel term as an interval integral
  have hI : projectedHeatNonlinearityIntegral (ν := ν) hc hc1 (extendCompactPath hT.le u) t =
      ∫ r in (0 : ℝ)..t, HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * (t - r)) hc
        (ν • hLap c 3 (extendCompactPath hT.le ub r) - R0 (extendCompactPath hT.le ub r)) := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    unfold projectedHeatNonlinearityIntegral
    exact setIntegral_congr_fun measurableSet_Ioo hpt
  -- assemble
  rw [hu0, hstep, hseed, hI]
  exact (sub_eq_add_neg _ _).symm

end UnforcedLeray.Short.PartI
