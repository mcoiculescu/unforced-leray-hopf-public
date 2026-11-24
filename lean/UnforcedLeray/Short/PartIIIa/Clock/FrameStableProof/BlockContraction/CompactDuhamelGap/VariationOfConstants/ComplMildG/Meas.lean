import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Strong measurability of `L²_m`-valued paths from joint measurability

A path `σ ↦ [Φ(σ, ·)] ∈ L²_m` built from a jointly measurable `Φ` is strongly measurable:
`L²_m` is second countable (the weighted measure is `s`-finite on the countably generated `ℂ`),
so measurability suffices, and measurability follows from the measurability of the distances
`σ ↦ ‖[Φ(σ, ·)] - g‖ = (∫ |Φ(σ, z) - g(z)|² dμ)^{1/2}` (Tonelli).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplMildGAux

open ComplMildYAux

/-- In a separable pseudometric space with its Borel structure, a map is measurable as soon as
its distances to all points are measurable. -/
theorem measurable_of_measurable_dist {α X : Type*} [MeasurableSpace α] [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] {f : α → X} (hf : ∀ x : X, Measurable fun a => dist (f a) x) :
    Measurable f := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq X
  refine measurable_of_isOpen fun U hU => ?_
  have hrep : f ⁻¹' U = ⋃ (n : ℕ) (q : ℚ) (_ : 0 < q ∧ Metric.ball (e n) (q : ℝ) ⊆ U),
      {a | dist (f a) (e n) < (q : ℝ)} := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro ha
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f a) ha
      obtain ⟨q, hq0, hq⟩ : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < ε / 2 :=
        exists_rat_btwn (by linarith)
      obtain ⟨n, hn⟩ := he.exists_dist_lt (f a) hq0
      refine ⟨n, q, ⟨by exact_mod_cast hq0, ?_⟩, hn⟩
      intro z hz
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      calc dist z (f a) ≤ dist z (e n) + dist (e n) (f a) := dist_triangle _ _ _
        _ = dist z (e n) + dist (f a) (e n) := by rw [dist_comm (e n)]
        _ < ε := by linarith
    · rintro ⟨n, q, ⟨_, hsub⟩, hn⟩
      exact hsub (Metric.mem_ball.mpr hn)
  rw [hrep]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt (hf (e n)) measurable_const

/-- **Joint measurability gives strong measurability in `L²_m`.** -/
theorem stronglyMeasurable_toL2w {m : ℝ} {Φ : ℝ → ℂ → ℂ}
    (hΦ : Measurable (fun p : ℝ × ℂ => Φ p.1 p.2))
    (hmem : ∀ σ, MemLp (Φ σ) 2 (Planar.wMeasure m)) :
    StronglyMeasurable (fun σ => toL2w m (Φ σ)) := by
  letI : MeasurableSpace (Planar.L2w m) := borel _
  haveI : BorelSpace (Planar.L2w m) := ⟨rfl⟩
  haveI : SFinite (Planar.wMeasure m) := by unfold Planar.wMeasure; infer_instance
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  haveI : SecondCountableTopology (Planar.L2w m) := inferInstance
  refine Measurable.stronglyMeasurable ?_
  refine measurable_of_measurable_dist fun g => ?_
  have hg : MemLp (⇑g) 2 (Planar.wMeasure m) := Lp.memLp g
  have hgeq : toL2w m ⇑g = g := by
    rw [toL2w, dif_pos hg]
    exact Lp.toLp_coeFn g hg
  have hdist : ∀ σ, dist (toL2w m (Φ σ)) g =
      (eLpNorm (Φ σ - ⇑g) 2 (Planar.wMeasure m)).toReal := by
    intro σ
    calc dist (toL2w m (Φ σ)) g = ‖toL2w m (Φ σ) - toL2w m ⇑g‖ := by
          rw [dist_eq_norm, hgeq]
      _ = (eLpNorm (Φ σ - ⇑g) 2 (Planar.wMeasure m)).toReal := norm_toL2w_sub (hmem σ) hg
  simp_rw [hdist]
  refine Measurable.ennreal_toReal ?_
  have hrw : ∀ σ, eLpNorm (Φ σ - ⇑g) 2 (Planar.wMeasure m) =
      (∫⁻ z, ‖Φ σ z - g z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂Planar.wMeasure m) ^
        (1 / (2 : ℝ≥0∞).toReal) := fun σ =>
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)
  simp_rw [hrw]
  refine Measurable.pow_const ?_ _
  exact Measurable.lintegral_prod_right'
    (f := fun p : ℝ × ℂ => ‖Φ p.1 p.2 - g p.2‖ₑ ^ (2 : ℝ≥0∞).toReal)
    (((hΦ.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).enorm).pow_const _)

end ComplMildGAux

end UnforcedLeray.Short.IIIa
