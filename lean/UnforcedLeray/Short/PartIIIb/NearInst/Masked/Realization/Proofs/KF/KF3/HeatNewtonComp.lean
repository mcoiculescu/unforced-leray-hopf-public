import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.HeatNewtonGrad

/-!
# `kf3HeatNewtonComp : KF3HeatNewtonComp` (source 3597-3601, 3617-3618)

For `θ > 0`, a spatial test `h` and `x`, `∫ G_θ(y) (∂_jN ⋆ h)(x - y) dy = ∫ ∂_j H_θ(x - z) h(z) dz`,
where `H_θ = heatTail θ` and `∂_jN ⋆ h = newtonComponent j h`.

Route: unfold `newtonComponent`; Fubini on `ℝ³ × ℝ³` for `(y, z) ↦ G_θ(y) ∂_jN(x - y - z) h(z)`.
Absolute integrability: `|h| ≤ M`, `|∂_jN(v)| ≤ (kf3hcLoc j v) + (4π)⁻¹` (local part plus a constant),
so the `z`-integral of the modulus is bounded uniformly in `y`, and `G_θ` is integrable.
The inner `y`-integral is `∫ G_θ((x - z) - y) ∂_jN(y) dy = ∂_j H_θ(x - z)` (`kf3HeatNewtonGrad`,
after `integral_sub_left_eq_self`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

/-- The Newtonian-gradient kernel `∂_jN`, abbreviated. -/
abbrev kf3hcK (j : Fin 3) : Space → ℝ := UnforcedLeray.PressureAnalysis.newtonGradientKernel j

/-- The norm of `∂_jN` on the closed unit ball, zero outside. -/
def kf3hcLoc (j : Fin 3) : Space → ℝ :=
  (Metric.closedBall (0 : Space) 1).indicator (fun w => ‖kf3hcK j w‖)

theorem kf3hcLoc_nonneg (j : Fin 3) (v : Space) : 0 ≤ kf3hcLoc j v :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) v

theorem kf3hcLoc_integrable (j : Fin 3) : Integrable (kf3hcLoc j) := by
  unfold kf3hcLoc
  have hKloc : IntegrableOn (kf3hcK j) (Metric.closedBall (0 : Space) 1) :=
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable j).integrableOn_isCompact
      (isCompact_closedBall 0 1)
  exact (integrable_indicator_iff measurableSet_closedBall).mpr hKloc.norm

/-- Pointwise bound: `|∂_jN(v)| ≤ kf3hcLoc j v + (4π)⁻¹` for every `v`. -/
theorem kf3hcK_le (j : Fin 3) (v : Space) :
    ‖kf3hcK j v‖ ≤ kf3hcLoc j v + (4 * Real.pi)⁻¹ := by
  unfold kf3hcLoc
  by_cases hv : ‖v‖ ≤ 1
  · have hmem : v ∈ Metric.closedBall (0 : Space) 1 := by
      rw [mem_closedBall_zero_iff]
      exact hv
    simp only [Set.indicator_of_mem hmem]
    have : (0:ℝ) ≤ (4 * Real.pi)⁻¹ := by positivity
    linarith
  · have hv' : 1 < ‖v‖ := lt_of_not_ge hv
    have hnot : v ∉ Metric.closedBall (0 : Space) 1 := by
      rw [mem_closedBall_zero_iff]
      exact not_le.mpr hv'
    simp only [Set.indicator_of_notMem hnot]
    have hb : ‖kf3hcK j v‖ ≤ (4 * Real.pi)⁻¹ := by
      calc ‖kf3hcK j v‖ ≤ (4 * Real.pi)⁻¹ * ‖v‖ ^ (-2 : ℝ) :=
            UnforcedLeray.PressureAnalysis.norm_newtonGradientKernel_le j v
        _ ≤ (4 * Real.pi)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos hv'.le (by norm_num)) (by positivity)
        _ = (4 * Real.pi)⁻¹ := mul_one _
    linarith

/-- The pointwise product bound used for the absolute integrability. -/
theorem kf3hc_pointwise {h : Space → ℝ} {M : ℝ} (hM : ∀ z, ‖h z‖ ≤ M) (j : Fin 3) (c z : Space) :
    ‖kf3hcK j (c - z)‖ * ‖h z‖ ≤ kf3hcLoc j (c - z) * M + (4 * Real.pi)⁻¹ * ‖h z‖ := by
  have h1 := kf3hcK_le j (c - z)
  have h2 : 0 ≤ ‖h z‖ := norm_nonneg _
  have h3 := hM z
  have h4 := kf3hcLoc_nonneg j (c - z)
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  calc ‖kf3hcK j (c - z)‖ * ‖h z‖
      ≤ (kf3hcLoc j (c - z) + (4 * Real.pi)⁻¹) * ‖h z‖ := mul_le_mul_of_nonneg_right h1 h2
    _ = kf3hcLoc j (c - z) * ‖h z‖ + (4 * Real.pi)⁻¹ * ‖h z‖ := by ring
    _ ≤ kf3hcLoc j (c - z) * M + (4 * Real.pi)⁻¹ * ‖h z‖ := by linarith

/-- The Fubini integrand `(y, z) ↦ G_θ(y) ∂_jN(x - y - z) h(z)`. -/
def kf3hcF (θ : ℝ) (x : Space) (j : Fin 3) (h : Space → ℝ) (y z : Space) : ℝ :=
  UnforcedLeray.Short.IIIa.heatG θ y * (kf3hcK j (x - y - z) * h z)

/-- **Leaf: the heat flow of a Newtonian convolution** (source 3597-3601, 3617-3618). -/
theorem kf3HeatNewtonComp : KF3HeatNewtonComp := by
  intro θ hθ h hh x j
  have hGm : Measurable (UnforcedLeray.Short.IIIa.heatG θ) :=
    (kf3hn_heatG_continuous θ).measurable
  have hGint : Integrable (UnforcedLeray.Short.IIIa.heatG θ) := kf3hc_integrable hθ
  have hGnn : ∀ y, 0 ≤ UnforcedLeray.Short.IIIa.heatG θ y :=
    fun y => kf3hn_heatG_nonneg hθ y
  have hKm : Measurable (kf3hcK j) :=
    UnforcedLeray.PressureAnalysis.newtonGradientKernel_measurable j
  have hhc : Continuous h := hh.smooth.continuous
  have hhm : Measurable h := hhc.measurable
  have hhI : Integrable h := hhc.integrable_of_hasCompactSupport hh.compact
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖h z‖ ≤ M := hhc.bounded_above_of_compact_support hh.compact
  -- integrability of `z ↦ ∂_jN(c - z) h(z)`
  have hint_z : ∀ c : Space, Integrable (fun z => kf3hcK j (c - z) * h z) := by
    intro c
    have hB : Integrable (fun z => kf3hcLoc j (c - z) * M + (4 * Real.pi)⁻¹ * ‖h z‖) :=
      (((kf3hcLoc_integrable j).comp_sub_left c).mul_const M).add (hhI.norm.const_mul _)
    refine Integrable.mono' hB
      ((hKm.comp (measurable_const.sub measurable_id)).mul hhm).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    exact kf3hc_pointwise hM j c z
  have hnorm_int : ∀ c : Space, Integrable (fun z => ‖kf3hcK j (c - z) * h z‖) :=
    fun c => (hint_z c).norm
  -- uniform bound on the `z`-integral of the modulus
  have hB0 : ∀ c : Space, ∫ z, ‖kf3hcK j (c - z) * h z‖ ≤
      (∫ v, kf3hcLoc j v) * M + (4 * Real.pi)⁻¹ * ∫ z, ‖h z‖ := by
    intro c
    have hB1 : Integrable (fun z => kf3hcLoc j (c - z) * M) :=
      ((kf3hcLoc_integrable j).comp_sub_left c).mul_const M
    have hB2 : Integrable (fun z => (4 * Real.pi)⁻¹ * ‖h z‖) := hhI.norm.const_mul _
    calc ∫ z, ‖kf3hcK j (c - z) * h z‖
        ≤ ∫ z, (kf3hcLoc j (c - z) * M + (4 * Real.pi)⁻¹ * ‖h z‖) := by
          refine integral_mono (hnorm_int c) (hB1.add hB2) (fun z => ?_)
          show ‖kf3hcK j (c - z) * h z‖ ≤ kf3hcLoc j (c - z) * M + (4 * Real.pi)⁻¹ * ‖h z‖
          rw [norm_mul]
          exact kf3hc_pointwise hM j c z
      _ = (∫ v, kf3hcLoc j v) * M + (4 * Real.pi)⁻¹ * ∫ z, ‖h z‖ := by
          rw [integral_add hB1 hB2, integral_mul_const, integral_const_mul,
            integral_sub_left_eq_self _ volume]
  -- joint measurability and absolute integrability of the Fubini integrand
  have hPm : Measurable (fun p : Space × Space => kf3hcF θ x j h p.1 p.2) := by
    unfold kf3hcF
    exact (hGm.comp measurable_fst).mul
      ((hKm.comp ((measurable_const.sub measurable_fst).sub measurable_snd)).mul
        (hhm.comp measurable_snd))
  have hPa : AEStronglyMeasurable (fun p : Space × Space => kf3hcF θ x j h p.1 p.2)
      (volume.prod volume) := hPm.aestronglyMeasurable
  have hPn : AEStronglyMeasurable (fun p : Space × Space => ‖kf3hcF θ x j h p.1 p.2‖)
      (volume.prod volume) := hPm.norm.aestronglyMeasurable
  have hPI : Integrable (fun p : Space × Space => kf3hcF θ x j h p.1 p.2)
      (volume.prod volume) := by
    rw [integrable_prod_iff hPa]
    constructor
    · refine ae_of_all _ (fun y => ?_)
      exact (hint_z (x - y)).const_mul (UnforcedLeray.Short.IIIa.heatG θ y)
    · have hm : AEStronglyMeasurable (fun y => ∫ z, ‖kf3hcF θ x j h y z‖) volume :=
        hPn.integral_prod_right'
      refine Integrable.mono' (hGint.mul_const ((∫ v, kf3hcLoc j v) * M
        + (4 * Real.pi)⁻¹ * ∫ z, ‖h z‖)) hm (ae_of_all _ (fun y => ?_))
      show ‖∫ z, ‖kf3hcF θ x j h y z‖‖ ≤
        UnforcedLeray.Short.IIIa.heatG θ y * ((∫ v, kf3hcLoc j v) * M
          + (4 * Real.pi)⁻¹ * ∫ z, ‖h z‖)
      have e1 : ∫ z, ‖kf3hcF θ x j h y z‖
          = UnforcedLeray.Short.IIIa.heatG θ y * ∫ z, ‖kf3hcK j (x - y - z) * h z‖ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ (fun z => ?_))
        show ‖UnforcedLeray.Short.IIIa.heatG θ y * (kf3hcK j (x - y - z) * h z)‖
          = UnforcedLeray.Short.IIIa.heatG θ y * ‖kf3hcK j (x - y - z) * h z‖
        rw [norm_mul, Real.norm_of_nonneg (hGnn y)]
      rw [e1, Real.norm_of_nonneg
        (mul_nonneg (hGnn y) (integral_nonneg (fun z => norm_nonneg _)))]
      exact mul_le_mul_of_nonneg_left (hB0 (x - y)) (hGnn y)
  -- the literal convolution, pointwise in `y`
  have hL : ∀ y, UnforcedLeray.Short.IIIa.heatG θ y
      * UnforcedLeray.PressureAnalysis.newtonComponent j h (x - y)
      = ∫ z, kf3hcF θ x j h y z := by
    intro y
    unfold kf3hcF
    rw [integral_const_mul]
    rfl
  -- the inner `y`-integral is the heat flow of the Newtonian gradient
  have hin : ∀ z, ∫ y, kf3hcF θ x j h y z
      = fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) (x - z)
          (UnforcedLeray.coordinateVector j) * h z := by
    intro z
    have e2 : ∫ y, kf3hcF θ x j h y z
        = (∫ y, UnforcedLeray.Short.IIIa.heatG θ y * kf3hcK j ((x - z) - y)) * h z := by
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ (fun y => ?_))
      show UnforcedLeray.Short.IIIa.heatG θ y * (kf3hcK j (x - y - z) * h z)
        = UnforcedLeray.Short.IIIa.heatG θ y * kf3hcK j (x - z - y) * h z
      rw [sub_right_comm x y z]
      ring
    have e3 : ∫ y, UnforcedLeray.Short.IIIa.heatG θ y * kf3hcK j ((x - z) - y)
        = ∫ y, UnforcedLeray.Short.IIIa.heatG θ ((x - z) - y) * kf3hcK j y := by
      have := integral_sub_left_eq_self
        (fun y => UnforcedLeray.Short.IIIa.heatG θ y * kf3hcK j ((x - z) - y)) volume (x - z)
      simp only [sub_sub_cancel] at this
      exact this.symm
    rw [e2, e3]
    congr 1
    exact (kf3HeatNewtonGrad θ hθ (x - z) j).2
  -- assembly
  refine ⟨?_, ?_⟩
  · exact hPI.integral_prod_left.congr (ae_of_all _ (fun y => (hL y).symm))
  · have hswap := integral_integral_swap (f := kf3hcF θ x j h) hPI
    calc ∫ y, UnforcedLeray.Short.IIIa.heatG θ y
          * UnforcedLeray.PressureAnalysis.newtonComponent j h (x - y)
        = ∫ y, ∫ z, kf3hcF θ x j h y z := integral_congr_ae (ae_of_all _ hL)
      _ = ∫ z, ∫ y, kf3hcF θ x j h y z := hswap
      _ = ∫ z, fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) (x - z)
            (UnforcedLeray.coordinateVector j) * h z :=
          integral_congr_ae (ae_of_all _ hin)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
