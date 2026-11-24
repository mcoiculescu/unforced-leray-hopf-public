import UnforcedLeray.Lib.HeatCylinder.HeatVecH3OrbitRealContinuity
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupContraction

/-!
# Joint continuity of the actual H³ heat action

Strong continuity of each orbit and the period-uniform contraction give continuity jointly in
age and H³ initial class.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- The actual centered H³ heat action is jointly continuous in real age and H³ input. -/
theorem continuous_heatVecH3Semigroup_joint {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 =>
      heatVecH3Semigroup (c := c) (θ := p.1) hc p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  let S : ℝ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ]
      UnforcedLeray.Cyl.H ℝ Vec c 0 3 := fun θ =>
    heatVecH3Semigroup (c := c) (θ := θ) hc
  have hfst : Tendsto Prod.fst (𝓝 p) (𝓝 p.1) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝 p) (𝓝 p.2) := by
    rw [nhds_prod_eq]
    exact tendsto_snd
  have hstate : Tendsto (fun q : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 =>
      dist q.2 p.2) (𝓝 p) (𝓝 0) := by
    have hd : Continuous (fun y : UnforcedLeray.Cyl.H ℝ Vec c 0 3 => dist y p.2) := by
      fun_prop
    have h := (hd.tendsto p.2).comp hsnd
    simpa only [Function.comp_def, dist_self] using h
  have hcont : Continuous (fun θ : ℝ => S θ p.2) := by
    simpa [S] using continuous_heatVecH3Semigroup_orbit hc p.2
  have hpath : Tendsto (fun q : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 => S q.1 p.2)
      (𝓝 p) (𝓝 (S p.1 p.2)) := (hcont.tendsto p.1).comp hfst
  have htime : Tendsto (fun q : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 =>
      dist (S q.1 p.2) (S p.1 p.2)) (𝓝 p) (𝓝 0) := by
    have hd : Continuous (fun y : UnforcedLeray.Cyl.H ℝ Vec c 0 3 =>
        dist y (S p.1 p.2)) := by fun_prop
    have h := (hd.tendsto (S p.1 p.2)).comp hpath
    simpa only [Function.comp_def, dist_self] using h
  have hupper : ∀ q : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3,
      dist (S q.1 q.2) (S p.1 p.2) ≤
        dist q.2 p.2 + dist (S q.1 p.2) (S p.1 p.2) := by
    intro q
    calc
      dist (S q.1 q.2) (S p.1 p.2) ≤
          dist (S q.1 q.2) (S q.1 p.2) + dist (S q.1 p.2) (S p.1 p.2) :=
        dist_triangle _ _ _
      _ ≤ dist q.2 p.2 + dist (S q.1 p.2) (S p.1 p.2) := by
        gcongr
        calc
          dist (S q.1 q.2) (S q.1 p.2) ≤ ‖S q.1‖ * dist q.2 p.2 :=
            (S q.1).dist_le_opNorm _ _
          _ ≤ 1 * dist q.2 p.2 :=
            mul_le_mul_of_nonneg_right (norm_heatVecH3Semigroup_le_one hc) dist_nonneg
          _ = dist q.2 p.2 := one_mul _
  have hsum : Tendsto
      (fun q : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 =>
        dist q.2 p.2 + dist (S q.1 p.2) (S p.1 p.2))
      (𝓝 p) (𝓝 0) := by simpa using hstate.add htime
  have hdist := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ × UnforcedLeray.Cyl.H ℝ Vec c 0 3 => (0 : ℝ))
      (𝓝 p) (𝓝 0)) hsum
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (Filter.Eventually.of_forall hupper)
  simpa [S] using hdist

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuous_heatVecH3Semigroup_joint
