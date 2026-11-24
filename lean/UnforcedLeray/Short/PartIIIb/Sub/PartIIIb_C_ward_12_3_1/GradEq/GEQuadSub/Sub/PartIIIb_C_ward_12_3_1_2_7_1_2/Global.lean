import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.Contract
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Inv

/-!
# Global `L^p` convergence of the `y`-mollification (proof)

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`).

Route: density of continuous compactly supported functions in `L^p`, the contraction bound
`SpatMolContract` on the approximation error, and `SpatMolContCompact` on the continuous part.
The linearity `spatMol (g - h) = spatMol g - spatMol h` holds almost everywhere because for a.e.
`τ` the slices of `g` are locally integrable.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

/-- For a.e. `τ`, every truncation of the `y`-slice of `g` to a ball is integrable. -/
theorem spatMolGl_slice_ae (p : ENNReal) (hp1 : 1 ≤ p) (g : ℝ × UnforcedLeray.Space → ℂ)
    (hg : MemLp g p volume) :
    ∀ᵐ τ ∂(volume : Measure ℝ), ∀ N : ℕ,
      Integrable (fun z : UnforcedLeray.Space =>
        (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator g (τ, z)) := by
  have hint : ∀ N : ℕ, Integrable
      ((Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator g)
      (volume : Measure (ℝ × UnforcedLeray.Space)) := by
    intro N
    have hS : MeasurableSet (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)) :=
      Metric.isClosed_closedBall.measurableSet
    have : IsFiniteMeasure (volume.restrict
        (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
    rw [integrable_indicator_iff hS]
    exact (hg.restrict _).integrable hp1
  have hprod : ∀ N : ℕ, Integrable
      ((Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator g)
      ((volume : Measure ℝ).prod (volume : Measure UnforcedLeray.Space)) := by
    intro N
    rw [← Measure.volume_eq_prod]
    exact hint N
  exact ae_all_iff.2 fun N => (hprod N).prod_right_ae

/-- The `y`-slice integrand `y' ↦ ρ y' * g(τ, y - y')` is integrable when all truncated slices
of `g` at `τ` are integrable and `ρ` is bounded, continuous, supported in the unit ball. -/
theorem spatMolGl_fiber (ρ : UnforcedLeray.Space → ℝ) (hρc : Continuous ρ)
    (hρb : ∃ C, ∀ y, ‖ρ y‖ ≤ C) (hρs : tsupport ρ ⊆ Metric.closedBall 0 1)
    (g : ℝ × UnforcedLeray.Space → ℂ) (τ : ℝ)
    (hτ : ∀ N : ℕ, Integrable (fun z : UnforcedLeray.Space =>
      (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator g (τ, z)))
    (y : UnforcedLeray.Space) :
    Integrable (fun y' : UnforcedLeray.Space => (ρ y' : ℂ) * g (τ, y - y')) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|τ| + ‖y‖ + 1)
  have hφt : Integrable (fun y' : UnforcedLeray.Space =>
      (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator g (τ, y - y')) :=
    (hτ N).comp_sub_left y
  obtain ⟨C, hC⟩ := hρb
  have hmeas : AEStronglyMeasurable (fun y' : UnforcedLeray.Space => ((ρ y' : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hρc).aestronglyMeasurable
  have key : (fun y' : UnforcedLeray.Space => (ρ y' : ℂ) * g (τ, y - y')) =
      fun y' => (ρ y' : ℂ) * (Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ)).indicator
        g (τ, y - y') := by
    funext y'
    by_cases h0 : ρ y' = 0
    · simp [h0]
    · have hy' : y' ∈ tsupport ρ := subset_tsupport _ (Function.mem_support.2 h0)
      have hb : ‖y'‖ ≤ 1 := by
        have := hρs hy'
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hmem : (τ, y - y') ∈ Metric.closedBall (0 : ℝ × UnforcedLeray.Space) (N : ℝ) := by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        refine max_le ?_ ?_
        · show ‖τ‖ ≤ (N : ℝ)
          rw [Real.norm_eq_abs]
          linarith [norm_nonneg y, abs_nonneg τ]
        · show ‖y - y'‖ ≤ (N : ℝ)
          linarith [norm_sub_le y y', norm_nonneg y, abs_nonneg τ]
      rw [Set.indicator_of_mem hmem]
  rw [key]
  have hbd : ∀ᵐ y' ∂(volume : Measure UnforcedLeray.Space), ‖((ρ y' : ℝ) : ℂ)‖ ≤ C :=
    Filter.Eventually.of_forall fun y' => by
      rw [Complex.norm_real]
      exact hC y'
  exact hφt.bdd_mul (c := C) hmeas hbd

/-- `spatMol` preserves almost everywhere strong measurability. -/
theorem spatMolGl_aesm (ρ : UnforcedLeray.Space → ℝ) (hρc : Continuous ρ)
    (f : ℝ × UnforcedLeray.Space → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (spatMol ρ f) volume := by
  obtain ⟨f', hf'm, hff'⟩ := hf
  have hF := spatMolC_ae ρ f f' hff'
  have hm : StronglyMeasurable (fun p : (ℝ × UnforcedLeray.Space) × UnforcedLeray.Space =>
      ((ρ p.2 : ℝ) : ℂ) * f' (p.1.1, p.1.2 - p.2)) := by
    refine StronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp (hρc.comp continuous_snd)).stronglyMeasurable
    · exact hf'm.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub measurable_snd))
  have hf'' : AEStronglyMeasurable (spatMol ρ f') volume :=
    (hm.integral_prod_right' (ν := (volume : Measure UnforcedLeray.Space))).aestronglyMeasurable
  exact hf''.congr hF.symm

theorem spatMolGlobalLp_holds (h1 : SpatMolContract) (h2 : SpatMolContCompact) :
    SpatMolGlobalLp := by
  intro p hp1 hpt ρ hρ g hg
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hεne : η / 3 ≠ 0 := (ENNReal.div_pos hη.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨h, hhc, hgh, hhcont, hhmem⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le hpt hεne
  have hev := ENNReal.tendsto_nhds_zero.1 (h2 p hp1 hpt ρ hρ h hhcont hhc) (η / 3)
    (pos_iff_ne_zero.2 hεne)
  filter_upwards [hev] with n hn
  obtain ⟨hρC, hρsupp, hρ0, hρ1, hρtsup⟩ := hρ n
  have hρcont : Continuous (ρ n) := hρC.continuous
  have hρs : tsupport (ρ n) ⊆ Metric.closedBall 0 1 := by
    refine hρtsup.trans (Metric.closedBall_subset_closedBall ?_)
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hρb : ∃ C, ∀ y, ‖ρ n y‖ ≤ C := hρcont.bounded_above_of_compact_support hρsupp
  have hρcs : HasCompactSupport (fun y' : UnforcedLeray.Space => ((ρ n y' : ℝ) : ℂ)) :=
    hρsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hgh_mem : MemLp (g - h) p volume := hg.sub hhmem
  have hhint : ∀ (τ : ℝ) (z : UnforcedLeray.Space),
      Integrable (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ) * h (τ, z - y')) := by
    intro τ z
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hρcont).mul
        (hhcont.comp (continuous_const.prodMk (continuous_const.sub continuous_id)))
    · exact hρcs.mul_right
  have hfib : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : UnforcedLeray.Space,
      Integrable (fun y' : UnforcedLeray.Space => (ρ n y' : ℂ) * g (τ, y - y')) := by
    filter_upwards [spatMolGl_slice_ae p hp1 g hg] with τ hτ' y
    exact spatMolGl_fiber (ρ n) hρcont hρb hρs g τ hτ' y
  have hq : Measure.QuasiMeasurePreserving (Prod.fst : ℝ × UnforcedLeray.Space → ℝ)
      (volume : Measure (ℝ × UnforcedLeray.Space)) (volume : Measure ℝ) := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst
  have hxgood := hq.ae hfib
  have heq : spatMol (ρ n) g - g =ᵐ[volume]
      (spatMol (ρ n) (g - h) + (spatMol (ρ n) h - h)) - (g - h) := by
    filter_upwards [hxgood] with x hx
    have hlinx : spatMol (ρ n) (g - h) x = spatMol (ρ n) g x - spatMol (ρ n) h x := by
      show (∫ y', (ρ n y' : ℂ) * (g (x.1, x.2 - y') - h (x.1, x.2 - y'))) =
        (∫ y', (ρ n y' : ℂ) * g (x.1, x.2 - y')) - ∫ y', (ρ n y' : ℂ) * h (x.1, x.2 - y')
      rw [← integral_sub (hx x.2) (hhint x.1 x.2)]
      congr 1
      funext y'
      ring
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [hlinx]
    ring
  have hB : AEStronglyMeasurable (spatMol (ρ n) (g - h)) volume :=
    spatMolGl_aesm (ρ n) hρcont (g - h) hgh_mem.aestronglyMeasurable
  have hC : AEStronglyMeasurable (spatMol (ρ n) h - h) volume :=
    (spatMolGl_aesm (ρ n) hρcont h hhmem.aestronglyMeasurable).sub hhcont.aestronglyMeasurable
  have hD : AEStronglyMeasurable (g - h) volume := hgh_mem.aestronglyMeasurable
  have hB1 : eLpNorm (spatMol (ρ n) (g - h)) p volume ≤ eLpNorm (g - h) p volume :=
    h1 p hp1 hpt (ρ n) (hρC) hρsupp hρ0 hρ1 (g - h) hgh_mem
  calc eLpNorm (spatMol (ρ n) g - g) p volume
      = eLpNorm ((spatMol (ρ n) (g - h) + (spatMol (ρ n) h - h)) - (g - h)) p volume :=
        eLpNorm_congr_ae heq
    _ ≤ eLpNorm (spatMol (ρ n) (g - h) + (spatMol (ρ n) h - h)) p volume
          + eLpNorm (g - h) p volume := eLpNorm_sub_le (hB.add hC) hD hp1
    _ ≤ (eLpNorm (spatMol (ρ n) (g - h)) p volume + eLpNorm (spatMol (ρ n) h - h) p volume)
          + eLpNorm (g - h) p volume := add_le_add (eLpNorm_add_le hB hC hp1) le_rfl
    _ ≤ (η / 3 + η / 3) + η / 3 :=
        add_le_add (add_le_add (hB1.trans hgh) hn) hgh
    _ = η := ENNReal.add_thirds η

end UnforcedLeray.Short.PartIIIb.Concrete
