import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2_2
import UnforcedLeray.Loc.L14Realization.TestCalculus

/-!
# `PartIII-b:IIIb-D5/2/2/2`: integrability of the weak mode integrand

Source `the November 2 reference manuscript` 167-182.
For `b_* = modeBstar L b` with `IsH1Periodic` (its `MemLp` slab part comes from
`modeBstar_memL2`) and a periodic test `φ` (smooth, space-compact), each of the four
pairings `⟨b_*, φ⟩`, `⟨b_*, ∂_τ φ⟩`, `⟨b_*, (y·∇)φ⟩`, `⟨b_*, Δφ⟩` is integrable on the period
slab: an `L²` field against a bounded continuous integrand vanishing outside a compact set
of space (`integrable_inner_slab`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace WeakModeIntegrableAux

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L14

/-- An `L²` field against a continuous integrand vanishing outside a compact set of space is
integrable on the period slab. -/
theorem integrable_inner_slab {P : ℝ} {K : Set Space} (hK : IsCompact K)
    {F : SpaceTime → Space} (hF : MemLp F 2 (volume.restrict (periodSlab P)))
    {g : SpaceTime → Space} (hg : Continuous g)
    (hg0 : ∀ z : SpaceTime, z.2 ∉ K → g z = 0) :
    Integrable (fun z : SpaceTime => inner ℝ (F z) (g z)) (volume.restrict (periodSlab P)) := by
  have hA : IsCompact (Icc (0 : ℝ) P ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hg.continuousOn
  have hBA : Ioc (0 : ℝ) P ×ˢ K ⊆ Icc (0 : ℝ) P ×ˢ K := prod_mono Ioc_subset_Icc_self subset_rfl
  have hBS : Ioc (0 : ℝ) P ×ˢ K ⊆ periodSlab P := by
    intro z hz
    exact ⟨hz.1, trivial⟩
  have hBm : MeasurableSet (Ioc (0 : ℝ) P ×ˢ K) :=
    measurableSet_Ioc.prod hK.isClosed.measurableSet
  have hSm : MeasurableSet (periodSlab P) := measurableSet_Ioc.prod MeasurableSet.univ
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P ×ˢ K)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hBA).trans_lt hA.measure_lt_top⟩
  have hF1 : Integrable F (volume.restrict (Ioc (0 : ℝ) P ×ˢ K)) := by
    have h := hF.restrict (Ioc (0 : ℝ) P ×ˢ K)
    rw [Measure.restrict_restrict_of_subset hBS] at h
    exact h.integrable one_le_two
  have hmeas : AEStronglyMeasurable (fun z : SpaceTime => inner ℝ (F z) (g z))
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ K)) :=
    hF1.aestronglyMeasurable.inner hg.aestronglyMeasurable
  have hint : Integrable (fun z : SpaceTime => C * ‖F z‖) (volume.restrict (Ioc (0 : ℝ) P ×ˢ K)) :=
    hF1.norm.const_mul C
  have hbound : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) P ×ˢ K)),
      ‖inner ℝ (F z) (g z)‖ ≤ C * ‖F z‖ := by
    refine ae_restrict_of_forall_mem hBm (fun z hz => ?_)
    have hgz : ‖g z‖ ≤ C := hC z (hBA hz)
    calc ‖inner ℝ (F z) (g z)‖ ≤ ‖F z‖ * ‖g z‖ := norm_inner_le_norm _ _
      _ ≤ ‖F z‖ * C := mul_le_mul_of_nonneg_left hgz (norm_nonneg _)
      _ = C * ‖F z‖ := mul_comm _ _
  have hBint : Integrable (fun z : SpaceTime => inner ℝ (F z) (g z))
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ K)) :=
    hint.mono' hmeas hbound
  have hae : (fun z : SpaceTime => inner ℝ (F z) (g z)) =ᵐ[volume.restrict (periodSlab P)]
      (Ioc (0 : ℝ) P ×ˢ K).indicator (fun z : SpaceTime => inner ℝ (F z) (g z)) := by
    refine ae_restrict_of_forall_mem hSm (fun z hz => ?_)
    by_cases hzB : z ∈ Ioc (0 : ℝ) P ×ˢ K
    · rw [Set.indicator_of_mem hzB]
    · have hg' : g z = 0 := hg0 z (fun hz2 => hzB ⟨hz.1, hz2⟩)
      rw [Set.indicator_of_notMem hzB]
      show inner ℝ (F z) (g z) = 0
      rw [hg', inner_zero_right]
  refine Integrable.congr ?_ hae.symm
  refine (integrable_indicator_iff hBm).2 ?_
  show Integrable _ ((volume.restrict (periodSlab P)).restrict (Ioc (0 : ℝ) P ×ˢ K))
  rw [Measure.restrict_restrict_of_subset hBS]
  exact hBint

/-- A test vanishing outside a compact set of space has vanishing spatial gradient there. -/
theorem fderiv_eq_zero_of_outside {φ : SpaceTime → Space} {K : Set Space} (hK : IsCompact K)
    (hφ0 : ∀ z : SpaceTime, z.2 ∉ K → φ z = 0) {w : SpaceTime} (hw : w.2 ∉ K) :
    fderiv ℝ φ w = 0 := by
  have hU : {z : SpaceTime | z.2 ∉ K} ∈ 𝓝 w :=
    (hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hw
  have hev : φ =ᶠ[𝓝 w] (fun _ => (0 : Space)) :=
    Filter.eventually_of_mem hU (fun z hz => hφ0 z hz)
  rw [hev.fderiv_eq]
  simp

/-- The Laplacian of a test vanishing outside a compact set of space vanishes there. -/
theorem lap_eq_zero_of_outside {φ : SpaceTime → Space} {K : Set Space} (hK : IsCompact K)
    (hφ0 : ∀ z : SpaceTime, z.2 ∉ K → φ z = 0) {z : SpaceTime} (hz : z.2 ∉ K) :
    Lap φ z = 0 := by
  unfold Lap
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hU : {w : SpaceTime | w.2 ∉ K} ∈ 𝓝 z :=
    (hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hz
  have hev : Ds φ i =ᶠ[𝓝 z] (fun _ => (0 : Space)) :=
    Filter.eventually_of_mem hU (fun w hw => by
      unfold Ds
      rw [fderiv_eq_zero_of_outside hK hφ0 hw]
      simp)
  rw [hev.fderiv_eq]
  simp

end WeakModeIntegrableAux

open WeakModeIntegrableAux UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L14

theorem weakModeIntegrable_proved :
    UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.WeakModeIntegrable := by
  intro L Pl μ b _hH1 φ hφ
  obtain ⟨K, hK, hφ0⟩ := hφ.space_compact
  have hs := hφ.smooth
  have hmemL2 := UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.modeBstar_memL2 (Pl := Pl) L b
  -- the four pairings, each an `L²` field against a bounded continuous vanishing-outside-`K` test
  have I0 : Integrable (fun z : SpaceTime =>
      inner ℝ (UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.modeBstar L b z.1 z.2) (φ z))
      (volume.restrict (periodSlab (2 * L.ε * UnforcedLeray.Short.PartIIIb.Concrete.cOf L.ν))) :=
    integrable_inner_slab hK hmemL2 hs.continuous (fun z hz => hφ0 z hz)
  have I1 : Integrable (fun z : SpaceTime =>
      inner ℝ (UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.modeBstar L b z.1 z.2) (Dt φ z))
      (volume.restrict (periodSlab (2 * L.ε * UnforcedLeray.Short.PartIIIb.Concrete.cOf L.ν))) :=
    integrable_inner_slab hK hmemL2 (contDiff_Dt hs).continuous (fun z hz => by
      unfold Dt
      rw [fderiv_eq_zero_of_outside hK hφ0 hz]
      simp)
  have I2 : Integrable (fun z : SpaceTime =>
      inner ℝ (UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.modeBstar L b z.1 z.2)
        (fderiv ℝ φ z ((0 : ℝ), z.2)))
      (volume.restrict (periodSlab (2 * L.ε * UnforcedLeray.Short.PartIIIb.Concrete.cOf L.ν))) :=
    integrable_inner_slab hK hmemL2
      ((hs.continuous_fderiv (by simp)).clm_apply (continuous_const.prodMk continuous_snd))
      (fun z hz => by
        rw [fderiv_eq_zero_of_outside hK hφ0 hz]
        simp)
  have I3 : Integrable (fun z : SpaceTime =>
      inner ℝ (UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.modeBstar L b z.1 z.2) (Lap φ z))
      (volume.restrict (periodSlab (2 * L.ε * UnforcedLeray.Short.PartIIIb.Concrete.cOf L.ν))) :=
    integrable_inner_slab hK hmemL2 (contDiff_Lap hs).continuous
      (fun z hz => by rw [lap_eq_zero_of_outside hK hφ0 hz])
  refine Integrable.congr
    ((((I0.const_mul (μ - 1 / 2)).add (((I1.neg).add (I0.const_mul (3 / 2))).add
      (I2.const_mul (1 / 2)))).sub (I3.const_mul L.ν))) ?_
  refine ae_of_all _ (fun z => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, weakModeIntegrand, driftAdjointTerm,
    pairTerm, dilationTerm, diffusionTerm, UnforcedLeray.temporalTerm,
    UnforcedLeray.diffusionTerm, timeDerivative_eq_Dt hs, spatialDerivative_eq hs,
    spatialLaplacian_eq_Lap hs, Prod.mk.eta]
