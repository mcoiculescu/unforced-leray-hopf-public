import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/4`: second-order Taylor bound for the heat flow

Source of record: `the November 2 reference manuscript`, lines 1363-1370 (the heat
part of `S(t)`). This file proves the Prop `HeatTaylor2` of `Sub/F02.lean`: for `1 ≤ p ≠ ⊤`,
`w ∈ C_c^∞`, `σ ≥ 0`,
`‖e^{σΔ}w - w - σΔw‖_p ≤ (σ²/2) ‖Δ²w‖_p`.

Route. `B0418.flow_sub_eq_integral` for `w` gives `e^{σΔ}w - w - σΔw = ∫_0^σ (e^{sΔ}Δw - Δw) ds`.
The first-order estimate `‖e^{sΔ}g - g‖_p ≤ s ‖Δg‖_p` (`hT2_flow_sub_bound`, applied to `g = Δw`)
then gives the bound. Minkowski's integral inequality (`NonUniqueEuler.Conv.eLpNorm_integral_le`)
is used once in the outer variable `s` and once inside the first-order estimate; joint
measurability is `B0418.measurable_flow_uncurry`, the contraction is `B0418.eLpNorm_flow_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The vector Laplacian of a `C^∞` field is `C^∞`. -/
theorem hT2_contDiff_vecLaplacian {w : SpatialField} (hs : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (B0418.vecLaplacian w) := by
  unfold B0418.vecLaplacian
  exact ContDiff.sum fun i _ => B0418.contDiff_dirDeriv (B0418.contDiff_dirDeriv hs _) _

/-- Interval integrability in time of `s ↦ e^{sΔ}g(x)` on `[0, τ]`, for continuous compactly
supported `g`. -/
theorem hT2_intervalIntegrable_flow {g : SpatialField} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (x : Space) {τ : ℝ} (hτ : 0 ≤ τ) :
    IntervalIntegrable (fun s => Heat.flow g s x) volume 0 τ := by
  apply ContinuousOn.intervalIntegrable
  intro s hs'
  rw [uIcc_of_le hτ] at hs'
  rcases hs'.1.eq_or_lt with h0' | hpos
  · rw [← h0']
    have h' : ContinuousAt (fun s => Heat.flow g s x) 0 := by
      rw [ContinuousAt, Heat.flow_zero]
      exact B0418.tendsto_flow_apply hgc hgs x
    exact h'.continuousWithinAt
  · have hL2 : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
    have hca : ContinuousAt (fun s => Heat.average s g x) s :=
      (Heat.average_time_continuousOn hL2 x).continuousAt (Ioi_mem_nhds hpos)
    have : ContinuousAt (fun s => Heat.flow g s x) s := by
      apply hca.congr
      filter_upwards [lt_mem_nhds hpos] with s' hs''
      rw [Heat.flow_pos _ hs'']
    exact this.continuousWithinAt

/-- First-order bound for the heat flow of a `C_c^∞` field: `‖e^{τΔ}g - g‖_p ≤ τ ‖Δg‖_p` for
`τ ≥ 0`, `1 ≤ p ≠ ⊤`. -/
theorem hT2_flow_sub_bound {g : SpatialField} (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {τ : ℝ} (hτ : 0 ≤ τ) :
    eLpNorm (fun y => Heat.flow g τ y - g y) p volume ≤
      ENNReal.ofReal τ * eLpNorm (B0418.vecLaplacian g) p volume := by
  rcases hτ.eq_or_lt with h0 | hτpos
  · rw [← h0]
    simp [Heat.flow_zero]
  have hLc : Continuous (B0418.vecLaplacian g) := B0418.continuous_vecLaplacian hs
  have hLs : HasCompactSupport (B0418.vecLaplacian g) := B0418.hasCompactSupport_vecLaplacian hc
  have hgL : MemLp (B0418.vecLaplacian g) p volume := hLc.memLp_of_hasCompactSupport hLs
  have hrep : ∀ y, Heat.flow g τ y - g y =
      ∫ s in Ioc (0:ℝ) τ, Heat.flow (B0418.vecLaplacian g) s y := by
    intro y
    rw [B0418.flow_sub_eq_integral hτpos hs hc y, intervalIntegral.integral_of_le hτpos.le]
  have hGm : Measurable (fun q : Space × ℝ => Heat.flow (B0418.vecLaplacian g) q.2 q.1) :=
    B0418.measurable_flow_uncurry hLc
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun y s => Heat.flow (B0418.vecLaplacian g) s y)
      ((volume : Measure Space).prod (volume.restrict (Ioc (0:ℝ) τ))) :=
    hGm.aestronglyMeasurable
  calc eLpNorm (fun y => Heat.flow g τ y - g y) p volume
      = eLpNorm (fun y => ∫ s in Ioc (0:ℝ) τ, Heat.flow (B0418.vecLaplacian g) s y) p volume := by
        congr 1
        funext y
        exact hrep y
    _ ≤ ∫⁻ s in Ioc (0:ℝ) τ, eLpNorm (fun y => Heat.flow (B0418.vecLaplacian g) s y) p volume :=
        NonUniqueEuler.Conv.eLpNorm_integral_le
          (F := fun y s => Heat.flow (B0418.vecLaplacian g) s y) hjoint hp1 hp
    _ ≤ ∫⁻ _s in Ioc (0:ℝ) τ, eLpNorm (B0418.vecLaplacian g) p volume :=
        lintegral_mono fun s => B0418.eLpNorm_flow_le hp1 hp hgL s
    _ = ENNReal.ofReal τ * eLpNorm (B0418.vecLaplacian g) p volume := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

/-- **Second-order Taylor bound for the heat flow of a `C_c^∞` field** (task `PartII-a:F02/4`):
the Prop `HeatTaylor2` of `Sub/F02.lean`. -/
theorem heatTaylor2 : HeatTaylor2 := by
  intro p hp1 hp w hs hc σ hσ
  rcases hσ.eq_or_lt with h0 | hσpos
  · rw [← h0]
    simp [Heat.flow_zero]
  have hLc : Continuous (B0418.vecLaplacian w) := B0418.continuous_vecLaplacian hs
  have hLs : ContDiff ℝ ∞ (B0418.vecLaplacian w) := hT2_contDiff_vecLaplacian hs
  have hLcs : HasCompactSupport (B0418.vecLaplacian w) :=
    B0418.hasCompactSupport_vecLaplacian hc
  -- pointwise: `e^{σΔ}w - w - σΔw = ∫_0^σ (e^{sΔ}Δw - Δw) ds`
  have hrep : ∀ y, Heat.flow w σ y - w y - σ • B0418.vecLaplacian w y =
      ∫ s in Ioc (0:ℝ) σ, (Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y) := by
    intro y
    have h1 := B0418.flow_sub_eq_integral hσpos hs hc y
    have h2 : ∫ _s in (0:ℝ)..σ, B0418.vecLaplacian w y = σ • B0418.vecLaplacian w y := by
      rw [intervalIntegral.integral_const, sub_zero]
    rw [← intervalIntegral.integral_of_le hσpos.le,
      intervalIntegral.integral_sub (hT2_intervalIntegrable_flow hLc hLcs y hσpos.le)
        intervalIntegrable_const,
      h2, ← h1]
  have hGm : Measurable (fun q : Space × ℝ =>
      Heat.flow (B0418.vecLaplacian w) q.2 q.1 - B0418.vecLaplacian w q.1) :=
    (B0418.measurable_flow_uncurry hLc).sub (hLc.measurable.comp measurable_fst)
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun y s => Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y)
      ((volume : Measure Space).prod (volume.restrict (Ioc (0:ℝ) σ))) :=
    hGm.aestronglyMeasurable
  have hpt : ∀ s ∈ Ioc (0:ℝ) σ,
      eLpNorm (fun y => Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y) p volume ≤
        ENNReal.ofReal s * eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian w)) p volume :=
    fun s hs' => hT2_flow_sub_bound hLs hLcs hp1 hp hs'.1.le
  have hlint : ∫⁻ s in Ioc (0:ℝ) σ, ENNReal.ofReal s = ENNReal.ofReal (σ ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le hσpos.le, integral_id]
      ring
    · exact continuous_id.integrableOn_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun s hs' => hs'.1.le
  calc eLpNorm (fun y => Heat.flow w σ y - w y - σ • B0418.vecLaplacian w y) p volume
      = eLpNorm (fun y => ∫ s in Ioc (0:ℝ) σ,
          (Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y)) p volume := by
        congr 1
        funext y
        exact hrep y
    _ ≤ ∫⁻ s in Ioc (0:ℝ) σ,
          eLpNorm (fun y => Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y) p volume :=
        NonUniqueEuler.Conv.eLpNorm_integral_le
          (F := fun y s => Heat.flow (B0418.vecLaplacian w) s y - B0418.vecLaplacian w y)
          hjoint hp1 hp
    _ ≤ ∫⁻ s in Ioc (0:ℝ) σ,
          ENNReal.ofReal s * eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian w)) p volume :=
        setLIntegral_mono ((ENNReal.measurable_ofReal).mul_const _) hpt
    _ = (∫⁻ s in Ioc (0:ℝ) σ, ENNReal.ofReal s) *
          eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian w)) p volume :=
        lintegral_mul_const _ ENNReal.measurable_ofReal
    _ = ENNReal.ofReal (σ ^ 2 / 2) *
          eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian w)) p volume := by
        rw [hlint]

end UnforcedLeray.Short.PartIIa
