import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0NonnegativeContinuity
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0AgeCongr
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatSemigroup

/-!
# Strong continuity throughout the actual short heat strip
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open Filter
open Set
open scoped Topology
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private noncomputable def s0At {c m : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (w : ActualVorticity (c := c) (m := m) hm) :
    ActualVorticity (c := c) (m := m) hm :=
  actualWeightedHeatS0 (c := c) hc1 hm hθ0 hθ1 w

private theorem norm_s0At_difference_le_modulus {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m)
    (t t₀ : Icc (0 : ℝ) 1) (w : ActualVorticity (c := c) (m := m) hm) :
    ‖s0At hc1 hm (t : ℝ) (Set.mem_Icc.mp t.property).1
        (Set.mem_Icc.mp t.property).2 w -
      s0At hc1 hm (t₀ : ℝ) (Set.mem_Icc.mp t₀.property).1
        (Set.mem_Icc.mp t₀.property).2 w‖ ≤
      max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * ∫ z : UnforcedLeray.GaussianVortex.Plane,
          axialHeatMomentDensity 1 m z)) *
        ‖s0At hc1 hm |(t : ℝ) - (t₀ : ℝ)| (abs_nonneg _) (by
          have ht := Set.mem_Icc.mp t.property
          have ht₀ := Set.mem_Icc.mp t₀.property
          rw [abs_le]
          constructor <;> linarith) w - w‖ := by
  let K : ℝ := max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : UnforcedLeray.GaussianVortex.Plane,
      axialHeatMomentDensity 1 m z))
  let δ : ℝ := |(t : ℝ) - (t₀ : ℝ)|
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    have ht := Set.mem_Icc.mp t.property
    have ht₀ := Set.mem_Icc.mp t₀.property
    rw [abs_le]
    constructor <;> linarith
  let St := actualWeightedHeatS0 (c := c) hc1 hm
    (Set.mem_Icc.mp t.property).1 (Set.mem_Icc.mp t.property).2
  let St₀ := actualWeightedHeatS0 (c := c) hc1 hm
    (Set.mem_Icc.mp t₀.property).1 (Set.mem_Icc.mp t₀.property).2
  let Sd := actualWeightedHeatS0 (c := c) hc1 hm hδ0 hδ1
  by_cases hleft : (t : ℝ) ≤ (t₀ : ℝ)
  · have hsum : (t : ℝ) + δ = (t₀ : ℝ) := by
      dsimp [δ]
      rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
      ring
    have hcomp := actualWeightedHeatS0_comp_of_nonneg (c := c) (m := m)
      hc1 hm (Set.mem_Icc.mp t.property).1 hδ0
      (Set.mem_Icc.mp t.property).2 hδ1 (by rw [hsum]; exact (Set.mem_Icc.mp t₀.property).2)
    have hcompAge := actualWeightedHeatS0_age_congr (c := c) (m := m)
      hc1 hm hsum (add_nonneg (Set.mem_Icc.mp t.property).1 hδ0)
      (by rw [hsum]; exact (Set.mem_Icc.mp t₀.property).2)
      (Set.mem_Icc.mp t₀.property).1 (Set.mem_Icc.mp t₀.property).2
    have hcompAt : St.comp Sd = St₀ := by
      exact hcomp.trans hcompAge
    have hcompw : St (Sd w) = St₀ w := congrArg (fun A => A w) hcompAt
    have hnormop := norm_actualWeightedHeatS0_le (c := c) (m := m) hc1 hm
      (Set.mem_Icc.mp t.property).1 (Set.mem_Icc.mp t.property).2
    change ‖St w - St₀ w‖ ≤ K * ‖s0At hc1 hm δ hδ0 hδ1 w - w‖
    calc
      ‖St w - St₀ w‖ = ‖St w - St (Sd w)‖ := by rw [hcompw]
      _ = ‖St (w - Sd w)‖ := by rw [map_sub]
      _ ≤ ‖St‖ * ‖w - Sd w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖w - Sd w‖ := by
        gcongr
      _ = K * ‖s0At hc1 hm δ hδ0 hδ1 w - w‖ := by
        simp [Sd, s0At, norm_sub_rev]
  · have hright : (t₀ : ℝ) ≤ (t : ℝ) := le_of_not_ge hleft
    have hsum : (t₀ : ℝ) + δ = (t : ℝ) := by
      dsimp [δ]
      rw [abs_of_nonneg (sub_nonneg.mpr hright)]
      ring
    have hcomp := actualWeightedHeatS0_comp_of_nonneg (c := c) (m := m)
      hc1 hm (Set.mem_Icc.mp t₀.property).1 hδ0
      (Set.mem_Icc.mp t₀.property).2 hδ1 (by rw [hsum]; exact (Set.mem_Icc.mp t.property).2)
    have hcompAge := actualWeightedHeatS0_age_congr (c := c) (m := m)
      hc1 hm hsum (add_nonneg (Set.mem_Icc.mp t₀.property).1 hδ0)
      (by rw [hsum]; exact (Set.mem_Icc.mp t.property).2)
      (Set.mem_Icc.mp t.property).1 (Set.mem_Icc.mp t.property).2
    have hcompAt : St₀.comp Sd = St := by
      exact hcomp.trans hcompAge
    have hcompw : St₀ (Sd w) = St w := congrArg (fun A => A w) hcompAt
    have hnormop := norm_actualWeightedHeatS0_le (c := c) (m := m) hc1 hm
      (Set.mem_Icc.mp t₀.property).1 (Set.mem_Icc.mp t₀.property).2
    change ‖St w - St₀ w‖ ≤ K * ‖s0At hc1 hm δ hδ0 hδ1 w - w‖
    calc
      ‖St w - St₀ w‖ = ‖St₀ (Sd w) - St₀ w‖ := by rw [hcompw]
      _ = ‖St₀ (Sd w - w)‖ := by rw [map_sub]
      _ ≤ ‖St₀‖ * ‖Sd w - w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖Sd w - w‖ := by
        gcongr
      _ = K * ‖s0At hc1 hm δ hδ0 hδ1 w - w‖ := by
        simp [Sd, s0At]

/-- The actual physical `S₀` orbit of every zero-circulation state is continuous on `[0,1]`. -/
theorem continuous_actualWeightedHeatS0_apply {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (w : ActualVorticity (c := c) (m := m) hm) :
    Continuous (fun t : Icc (0 : ℝ) 1 =>
      s0At hc1 hm (t : ℝ) (Set.mem_Icc.mp t.property).1
        (Set.mem_Icc.mp t.property).2 w) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  change Tendsto (fun t : Icc (0 : ℝ) 1 =>
    s0At hc1 hm (t : ℝ) (Set.mem_Icc.mp t.property).1
      (Set.mem_Icc.mp t.property).2 w) (𝓝 t₀)
    (𝓝 (s0At hc1 hm (t₀ : ℝ) (Set.mem_Icc.mp t₀.property).1
      (Set.mem_Icc.mp t₀.property).2 w))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcont : Continuous fun t : Icc (0 : ℝ) 1 => |(t : ℝ) - (t₀ : ℝ)| := by fun_prop
  have hδ : Tendsto (fun t : Icc (0 : ℝ) 1 => |(t : ℝ) - (t₀ : ℝ)|)
      (𝓝 t₀) (𝓝 0) := by
    have hAt : ContinuousAt (fun t : Icc (0 : ℝ) 1 => |(t : ℝ) - (t₀ : ℝ)|) t₀ :=
      hcont.continuousAt
    simpa only [sub_self, abs_zero] using hAt.tendsto
  have hδnonneg : Tendsto (fun t : Icc (0 : ℝ) 1 => |(t : ℝ) - (t₀ : ℝ)|)
      (𝓝 t₀) (nhdsWithin (0 : ℝ) (Ici 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hδ, ?_⟩
    exact Filter.Eventually.of_forall fun t => Set.mem_Ici.mpr (abs_nonneg _)
  let U : ℝ → ActualVorticity (c := c) (m := m) hm := fun δ =>
    if hδ : 0 < δ then
      if hδ1 : δ ≤ 1 then actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hδ) hδ1 w
      else w
    else actualWeightedHeatS0 (c := c) hc1 hm (θ := 0) le_rfl (by norm_num) w
  have hAge := tendsto_actualWeightedHeatS0_apply_zero_nonneg hc1 hm w
  have hmod := (tendsto_iff_norm_sub_tendsto_zero.mp (hAge.comp hδnonneg))
  have hsame : (fun t : Icc (0 : ℝ) 1 =>
      ‖s0At hc1 hm |(t : ℝ) - (t₀ : ℝ)| (abs_nonneg _)
        (by
          have ht := Set.mem_Icc.mp t.property
          have ht₀ := Set.mem_Icc.mp t₀.property
          rw [abs_le]
          constructor <;> linarith) w - w‖) =ᶠ[𝓝 t₀]
      (fun t => ‖U |(t : ℝ) - (t₀ : ℝ)| - w‖) := by
    filter_upwards [] with t
    have hd1 : |(t : ℝ) - (t₀ : ℝ)| ≤ 1 := by
      have ht := Set.mem_Icc.mp t.property
      have ht₀ := Set.mem_Icc.mp t₀.property
      rw [abs_le]
      constructor <;> linarith
    by_cases hdpos : 0 < |(t : ℝ) - (t₀ : ℝ)|
    · simp [U, s0At, hdpos, hd1]
    · have hdzero : |(t : ℝ) - (t₀ : ℝ)| = 0 := by
        apply le_antisymm (le_of_not_gt hdpos)
        positivity
      simp [U, s0At, hdzero]
  have hmod' := hmod.congr' hsame.symm
  let K : ℝ := max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : UnforcedLeray.GaussianVortex.Plane,
      axialHeatMomentDensity 1 m z))
  have hsmall := hmod'.mul_const K
  have hbound : ∀ t : Icc (0 : ℝ) 1,
      ‖s0At hc1 hm (t : ℝ) (Set.mem_Icc.mp t.property).1
          (Set.mem_Icc.mp t.property).2 w -
        s0At hc1 hm (t₀ : ℝ) (Set.mem_Icc.mp t₀.property).1
          (Set.mem_Icc.mp t₀.property).2 w‖ ≤
        K * ‖s0At hc1 hm |(t : ℝ) - (t₀ : ℝ)| (abs_nonneg _)
          (by
            have ht := Set.mem_Icc.mp t.property
            have ht₀ := Set.mem_Icc.mp t₀.property
            rw [abs_le]
            constructor <;> linarith) w - w‖ := by
    intro t
    exact norm_s0At_difference_le_modulus hc1 hm t t₀ w
  have hdist : Tendsto (fun t : Icc (0 : ℝ) 1 =>
      ‖s0At hc1 hm (t : ℝ) (Set.mem_Icc.mp t.property).1
          (Set.mem_Icc.mp t.property).2 w -
        s0At hc1 hm (t₀ : ℝ) (Set.mem_Icc.mp t₀.property).1
          (Set.mem_Icc.mp t₀.property).2 w‖)
      (𝓝 t₀) (𝓝 0) := by
    have hsmall0 : Tendsto (fun t : Icc (0 : ℝ) 1 =>
        ‖s0At hc1 hm |(t : ℝ) - (t₀ : ℝ)| (abs_nonneg _)
          (by
            have ht := Set.mem_Icc.mp t.property
            have ht₀ := Set.mem_Icc.mp t₀.property
            rw [abs_le]
            constructor <;> linarith) w - w‖ * K)
        (𝓝 t₀) (𝓝 0) := by simpa using hsmall
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall0 ?_ ?_
    · filter_upwards [] with t
      exact norm_nonneg _
    · filter_upwards [] with t
      simpa [mul_comm] using hbound t
  exact hdist

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuous_actualWeightedHeatS0_apply
