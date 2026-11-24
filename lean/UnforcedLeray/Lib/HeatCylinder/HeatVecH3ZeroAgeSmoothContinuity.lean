import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeComponentNorm
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2ZeroAge

/-!
# Strong continuity at zero on smooth H³ inputs

The exact component normalization identity reduces the centered H³ increment to a finite sum
of actual normalized-cell vector L² Gaussian increments.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The actual centered H³ Gaussian family converges strongly to the identity at zero on every
smooth compact-axial periodic vector field. -/
theorem tendsto_heatVecH3Semigroup_apply_zero_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    Tendsto
      (fun θ : ℝ => heatVecH3Semigroup (c := c) (θ := θ) hc
        (UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc T hT))
      (𝓝 0)
      (𝓝 (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT)) := by
  let x : UnforcedLeray.Cyl.H ℝ Vec c 0 3 := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT
  let component (α : UnforcedLeray.Sob.Idx 2 3) : Lp Vec 2
      (UnforcedLeray.B0284.cellMeasure c) :=
    (memLp_iterD_vec_cylSmooth_normalized hc hT
      ((UnforcedLeray.Sob.cylinder c).word α)).toLp
      (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)
  let sq (θ : ℝ) : ℝ := ∑ α : UnforcedLeray.Sob.Idx 2 3,
      c * ‖heatVecL2CLM hc θ (component α) - component α‖ ^ 2
  have hcomponent (α : UnforcedLeray.Sob.Idx 2 3) :
      Tendsto (fun θ : ℝ => c *
        ‖heatVecL2CLM hc θ (component α) - component α‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
    have hL2 := tendsto_heatVecL2CLM_apply_zero hc (component α)
    have hdiff : Tendsto (fun θ : ℝ =>
        heatVecL2CLM hc θ (component α) - component α) (𝓝[>] 0) (𝓝 0) := by
      simpa using hL2.sub_const (component α)
    have hnorm : Tendsto (fun θ : ℝ =>
        ‖heatVecL2CLM hc θ (component α) - component α‖) (𝓝[>] 0) (𝓝 0) :=
      by simpa using hdiff.norm
    have hsq := hnorm.pow 2
    simpa using (tendsto_const_nhds.mul hsq)
  have hsum : Tendsto sq (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (UnforcedLeray.Sob.Idx 2 3))
      (fun α _ => by simpa only [component] using hcomponent α)
    have hz : (∑ α : UnforcedLeray.Sob.Idx 2 3, (0 : ℝ)) = 0 := by simp
    rw [hz] at h
    simpa [sq] using h
  have hsqEq :
      (fun θ : ℝ => ‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2) =ᶠ[𝓝[>] 0] sq := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hpoint :
        ‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2 =
          ∑ α : UnforcedLeray.Sob.Idx 2 3,
            c * ‖heatVecL2CLM hc θ (component α) - component α‖ ^ 2 := by
      rw [heatVecH3Semigroup_apply_of_pos hc hθ]
      rw [UnforcedLeray.Sob.W.norm_sq]
      apply Finset.sum_congr rfl
      intro α hα
      exact norm_deriv_actualHeatVecH3_sub_ofCylSmooth_sq hc hθ hT α
    simpa [sq, hθ] using hpoint
  have hsqLimit : Tendsto
      (fun θ : ℝ => ‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := hsum.congr' hsqEq.symm
  have hnormLimit : Tendsto
      (fun θ : ℝ => ‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖)
      (𝓝[>] 0) (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsqLimit
    have hfun : (fun θ : ℝ => ‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖) =
        fun θ => Real.sqrt (‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2) := by
      funext θ
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hsqrt' : Tendsto (fun θ : ℝ =>
        Real.sqrt (‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2))
        (𝓝[>] 0) (𝓝 0) := by
      change Tendsto (fun θ : ℝ =>
        Real.sqrt (‖heatVecH3Semigroup (c := c) (θ := θ) hc x - x‖ ^ 2))
        (𝓝[>] 0) (𝓝 (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_zero] using hsqrt
    exact hsqrt'.congr (fun θ => congrFun hfun.symm θ)
  have hright : Tendsto (fun θ : ℝ =>
      heatVecH3Semigroup (c := c) (θ := θ) hc x) (𝓝[>] 0) (𝓝 x) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [x, norm_sub_rev] using hnormLimit
  have hleft : Tendsto (fun θ : ℝ =>
      heatVecH3Semigroup (c := c) (θ := θ) hc x) (𝓝[Set.Iic 0] 0) (𝓝 x) := by
    have hEq : (fun θ : ℝ =>
        heatVecH3Semigroup (c := c) (θ := θ) hc x) =ᶠ[𝓝[Set.Iic 0] 0] fun _ => x := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      rw [heatVecH3Semigroup_eq_id_of_nonpos hc hθ]
      simp
    exact (tendsto_const_nhds.congr' hEq.symm)
  have hcover : Set.Ioi (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext θ
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ]
    by_cases h : θ ≤ 0
    · simp [h]
    · simp [not_le.mp h]
  rw [← nhdsWithin_univ (0 : ℝ), ← hcover, nhdsWithin_union]
  exact hright.sup hleft

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecH3Semigroup_apply_zero_ofCylSmooth
