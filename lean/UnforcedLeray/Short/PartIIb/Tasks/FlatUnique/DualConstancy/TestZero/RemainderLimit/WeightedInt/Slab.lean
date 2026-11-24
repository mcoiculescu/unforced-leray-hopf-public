import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.SPeriodic

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/2`: slab comparison `SlabCompare`

Source: `the November 2 reference manuscript` lines 1923-1927.
On the slab `Icc a a' ×ˢ univ` with `0 < a ≤ a'`, the densities of `ageμ c 0` and
`ageμ c (r/2-5/2)` with respect to volume are `dens c 0` and `dens c p`, and
`x.1 ↦ x.1 ^ p` is bounded above and below by positive constants on `Icc a a'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- On `Icc a a'` with `0 < a ≤ a'`, `y ↦ y ^ p` has positive finite lower and upper bounds. -/
theorem slab_rpow_bounds {a a' : ℝ} (p : ℝ) (ha : 0 < a) (haa : a ≤ a') :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ y ∈ Icc a a', m ≤ y ^ p ∧ y ^ p ≤ M := by
  have hcont : ContinuousOn (fun y : ℝ => y ^ p) (Icc a a') := by
    refine ContinuousOn.rpow_const continuousOn_id ?_
    intro y hy
    left
    exact (lt_of_lt_of_le ha hy.1).ne'
  obtain ⟨m0, hm0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 haa) hcont
  obtain ⟨M0, hM0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 haa) hcont
  have hpos0 : 0 < m0 := lt_of_lt_of_le ha hm0.1
  have hposM : 0 < M0 := lt_of_lt_of_le ha hM0.1
  refine ⟨m0 ^ p, M0 ^ p, Real.rpow_pos_of_pos hpos0 p, Real.rpow_pos_of_pos hposM p,
    fun y hy => ⟨hmin hy, hmax hy⟩⟩

theorem slabCompare : UnforcedLeray.Short.IIb.SlabCompare := by
  intro c r a a' hc ha haa
  obtain ⟨m, M, hm, hM, hbd⟩ := slab_rpow_bounds (r / 2 - 5 / 2) ha haa
  have hcinv : 0 < c⁻¹ := inv_pos.2 hc
  have hSm : MeasurableSet (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  refine ⟨ENNReal.ofReal (1 / m), ENNReal.ofReal M, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top, ?_, ?_⟩
  · unfold hMeas
    rw [ageμ_eq_withDensity hc 0, ageμ_eq_withDensity hc (r / 2 - 5 / 2),
      restrict_withDensity hSm, restrict_withDensity hSm, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    refine withDensity_mono ?_
    filter_upwards [ae_restrict_mem hSm] with x hx
    show dens c 0 x ≤ ENNReal.ofReal (1 / m) * dens c (r / 2 - 5 / 2) x
    obtain ⟨h1, _⟩ := hbd x.1 hx.1
    unfold dens
    by_cases hI : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
    · simp only [Set.indicator_of_mem hI, Pi.one_apply, mul_one, Real.rpow_zero]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hy : 1 ≤ x.1 ^ (r / 2 - 5 / 2) / m := by
        rw [le_div_iff₀ hm]
        linarith
      rw [show 1 / m * (c⁻¹ * x.1 ^ (r / 2 - 5 / 2)) = c⁻¹ * (x.1 ^ (r / 2 - 5 / 2) / m) by ring]
      exact le_mul_of_one_le_right hcinv.le hy
    · simp [Set.indicator_of_notMem hI]
  · unfold hMeas
    rw [ageμ_eq_withDensity hc 0, ageμ_eq_withDensity hc (r / 2 - 5 / 2),
      restrict_withDensity hSm, restrict_withDensity hSm, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    refine withDensity_mono ?_
    filter_upwards [ae_restrict_mem hSm] with x hx
    show dens c (r / 2 - 5 / 2) x ≤ ENNReal.ofReal M * dens c 0 x
    obtain ⟨_, h2⟩ := hbd x.1 hx.1
    unfold dens
    by_cases hI : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
    · simp only [Set.indicator_of_mem hI, Pi.one_apply, mul_one, Real.rpow_zero]
      rw [← ENNReal.ofReal_mul hM.le]
      apply ENNReal.ofReal_le_ofReal
      calc c⁻¹ * x.1 ^ (r / 2 - 5 / 2) ≤ c⁻¹ * M := mul_le_mul_of_nonneg_left h2 hcinv.le
        _ = M * c⁻¹ := mul_comm _ _
    · simp [Set.indicator_of_notMem hI]

end UnforcedLeray.Short.IIb
