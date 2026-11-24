import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeSmoothContinuity
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Density
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Strong continuity at zero of the actual centered H³ Gaussian family

Smooth density and the actual period-independent H³ contraction extend the smooth Gaussian
approximate-identity limit to every centered H³ class.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

private theorem norm_heatVecH3Semigroup_le_one {c θ : ℝ} (hc : 0 < c) :
    ‖heatVecH3Semigroup (c := c) (θ := θ) hc‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · simpa [heatVecH3Semigroup, hθ] using norm_actualHeatVecH3CLM_le_one hc hθ
  · simpa [heatVecH3Semigroup, hθ] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)
        (E := UnforcedLeray.Cyl.H ℝ Vec c 0 3))

/-- The actual centered H³ Gaussian heat family, with the identity convention at nonpositive
ages, is strongly continuous at zero on every H³ class. -/
theorem tendsto_heatVecH3Semigroup_apply_zero {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    Tendsto (fun θ : ℝ => heatVecH3Semigroup (c := c) (θ := θ) hc x)
      (𝓝 0) (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with θ
    exact lt_of_lt_of_le ha dist_nonneg
  · intro ε hε
    obtain ⟨y, T, hT, hy, hlim⟩ := exists_smoothVectorH3_sequence hc x
    have hclose : ∀ᶠ n : ℕ in atTop, dist (y n) x < ε / 4 := by
      exact hlim.eventually (Metric.ball_mem_nhds x (by linarith))
    obtain ⟨n, hn⟩ := hclose.exists
    have hsmooth : Tendsto
        (fun θ : ℝ => heatVecH3Semigroup (c := c) (θ := θ) hc (y n))
        (𝓝 0) (𝓝 (y n)) := by
      rw [hy n]
      exact tendsto_heatVecH3Semigroup_apply_zero_ofCylSmooth hc (hT n)
    have hnear : ∀ᶠ θ : ℝ in 𝓝 0,
        dist (heatVecH3Semigroup (c := c) (θ := θ) hc (y n)) (y n) < ε / 4 :=
      hsmooth.eventually (Metric.ball_mem_nhds (y n) (by linarith))
    filter_upwards [hnear] with θ hθ
    calc
      dist (heatVecH3Semigroup (c := c) (θ := θ) hc x) x ≤
          dist (heatVecH3Semigroup (c := c) (θ := θ) hc x)
              (heatVecH3Semigroup (c := c) (θ := θ) hc (y n)) +
            dist (heatVecH3Semigroup (c := c) (θ := θ) hc (y n)) x :=
        dist_triangle _ _ _
      _ ≤ dist x (y n) +
            (dist (heatVecH3Semigroup (c := c) (θ := θ) hc (y n)) (y n) +
              dist (y n) x) := by
        apply add_le_add
        · calc
            dist (heatVecH3Semigroup (c := c) (θ := θ) hc x)
                (heatVecH3Semigroup (c := c) (θ := θ) hc (y n)) ≤
                ‖heatVecH3Semigroup (c := c) (θ := θ) hc‖ * dist x (y n) :=
              (heatVecH3Semigroup (c := c) (θ := θ) hc).dist_le_opNorm x (y n)
            _ ≤ 1 * dist x (y n) :=
              mul_le_mul_of_nonneg_right (norm_heatVecH3Semigroup_le_one hc)
                dist_nonneg
            _ = dist x (y n) := one_mul _
        · exact dist_triangle _ _ _
      _ < ε := by
        have hn' : dist x (y n) < ε / 4 := by simpa only [dist_comm] using hn
        linarith

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecH3Semigroup_apply_zero
