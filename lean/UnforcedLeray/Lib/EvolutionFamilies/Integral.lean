import UnforcedLeray.Lib.EvolutionFamilies.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong measurability and integrals over the time triangle (INF08 T8.2, auxiliary)

Auxiliary results for the Dyson construction of `scoping/INF07-INF08-INF09-Evolution.md`, §5,
T8.2 (`paper/main.tex`, lines 1594-1617; blueprint B0104, B0106).

* `aestronglyMeasurable_clm_apply`: if `a ↦ L a x` is a.e. strongly measurable for every `x`
  (strong measurability of an operator family) and `g` is a.e. strongly measurable, then
  `a ↦ L a (g a)` is a.e. strongly measurable. Proof by simple-function approximation of `g`.
  This is what lets the Dyson iteration use the manuscript's hypothesis "strongly measurable
  interactions" (line 1594) instead of operator-norm measurability.
* `intervalIntegrable_of_bound`: a bounded a.e. strongly measurable function is interval
  integrable.
* `continuousOn_integral_triangle`: `(s,t) ↦ ∫ r in s..t, Ψ (s,t) r` is continuous on the
  triangle `a ≤ s ≤ t ≤ b`, for a uniformly bounded integrand that is continuous in `(s,t)` for
  each fixed `s < r < t` (dominated convergence with indicator functions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

/-- `r ≠ c` for almost every `r`. -/
theorem ae_ne_real (c : ℝ) : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ c := by
  rw [ae_iff]
  simp

/-- **Strong measurability of an operator family applied to a measurable vector.** If
`a ↦ L a x` is a.e. strongly measurable for every `x` and `g` is a.e. strongly measurable, then
`a ↦ L a (g a)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_clm_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {L : α → E →L[ℂ] F} (hL : ∀ x, AEStronglyMeasurable (fun a => L a x) μ)
    {g : α → E} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun a => L a (g a)) μ := by
  have hg' : StronglyMeasurable (hg.mk g) := hg.stronglyMeasurable_mk
  have hsimple : ∀ φ : SimpleFunc α E, AEStronglyMeasurable (fun a => L a (φ a)) μ := by
    intro φ
    have heq : (fun a => L a (φ a)) =
        fun a => ∑ c ∈ φ.range, (φ ⁻¹' {c}).indicator (fun a => L a c) a := by
      funext a
      rw [Finset.sum_eq_single (φ a)]
      · rw [Set.indicator_of_mem (by simp)]
      · intro c _ hc
        rw [Set.indicator_of_notMem]
        simpa [eq_comm] using hc
      · intro h
        exact absurd (φ.mem_range_self a) h
    rw [heq]
    exact Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
      (hL c).indicator (φ.measurableSet_fiber c)
  have hlim : AEStronglyMeasurable (fun a => L a (hg.mk g a)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hsimple (hg'.approx n))
      (ae_of_all _ fun a => ((L a).continuous.tendsto _).comp (hg'.tendsto_approx a))
  exact hlim.congr (hg.ae_eq_mk.mono fun a ha => by simp only [ha])

/-- A bounded a.e. strongly measurable function on `(s,t]` is interval integrable on `[s,t]`. -/
theorem intervalIntegrable_of_bound {X : Type*} [NormedAddCommGroup X] {f : ℝ → X} {s t K : ℝ}
    (hst : s ≤ t) (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc s t)))
    (hb : ∀ r ∈ Ioc s t, ‖f r‖ ≤ K) : IntervalIntegrable f volume s t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  exact ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioc_lt_top
    (ae_restrict_of_forall_mem measurableSet_Ioc hb)⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **Continuity of integrals over the time triangle.** Let `Ψ (s,t) r` be a.e. strongly
measurable in `r ∈ (s,t]`, bounded by `K`, and, for each fixed `r`, continuous in `(s,t)` within
`{(s,t) ∈ triangle | s ≤ r ≤ t}`. Then `(s,t) ↦ ∫ r in s..t, Ψ (s,t) r` is continuous on the
triangle `a ≤ s ≤ t ≤ b`. -/
theorem continuousOn_integral_triangle {a b K : ℝ} {Ψ : ℝ × ℝ → ℝ → X}
    (hmeas : ∀ p ∈ triangle a b, AEStronglyMeasurable (Ψ p) (volume.restrict (Ioc p.1 p.2)))
    (hbound : ∀ p ∈ triangle a b, ∀ r ∈ Ioc p.1 p.2, ‖Ψ p r‖ ≤ K)
    (hcont : ∀ p ∈ triangle a b, ∀ r, p.1 < r → r < p.2 →
      ContinuousWithinAt (fun q => Ψ q r) {q | q ∈ triangle a b ∧ q.1 ≤ r ∧ r ≤ q.2} p) :
    ContinuousOn (fun p => ∫ r in p.1..p.2, Ψ p r) (triangle a b) := by
  intro p₀ hp₀
  set T := triangle a b with hT
  have hrepr : ∀ p ∈ T, ∫ r in p.1..p.2, Ψ p r =
      ∫ r in Ioc a b, (Ioc p.1 p.2).indicator (Ψ p) r := by
    intro p hp
    rw [intervalIntegral.integral_of_le hp.2.1, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioc hp.1 hp.2.2)]
  have hfst : Tendsto Prod.fst (𝓝[T] p₀) (𝓝 p₀.1) := continuous_fst.continuousWithinAt
  have hsnd : Tendsto Prod.snd (𝓝[T] p₀) (𝓝 p₀.2) := continuous_snd.continuousWithinAt
  have hlim : Tendsto (fun p => ∫ r in Ioc a b, (Ioc p.1 p.2).indicator (Ψ p) r) (𝓝[T] p₀)
      (𝓝 (∫ r in Ioc a b, (Ioc p₀.1 p₀.2).indicator (Ψ p₀) r)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => max K 0) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact ((aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr (hmeas p hp)).restrict
    · filter_upwards [self_mem_nhdsWithin] with p hp
      refine ae_of_all _ fun r => ?_
      by_cases hr : r ∈ Ioc p.1 p.2
      · rw [indicator_of_mem hr]
        exact (hbound p hp r hr).trans (le_max_left _ _)
      · rw [indicator_of_notMem hr, norm_zero]
        exact le_max_right _ _
    · exact integrable_const _
    · refine ae_restrict_of_ae ?_
      filter_upwards [ae_ne_real p₀.1, ae_ne_real p₀.2] with r h1 h2
      rcases lt_or_gt_of_ne h1 with hr1 | hr1
      · have hev : ∀ᶠ p in 𝓝[T] p₀, r < p.1 := hfst.eventually (lt_mem_nhds hr1)
        rw [indicator_of_notMem (s := Ioc p₀.1 p₀.2) (fun h => absurd h.1 (not_lt.mpr hr1.le))]
        refine tendsto_const_nhds.congr' (hev.mono fun p hp => ?_)
        exact (indicator_of_notMem (s := Ioc p.1 p.2) (fun h => absurd h.1 (not_lt.mpr hp.le))
          _).symm
      · rcases lt_or_gt_of_ne h2 with hr2 | hr2
        · have hev1 : ∀ᶠ p in 𝓝[T] p₀, p.1 < r := hfst.eventually (gt_mem_nhds hr1)
          have hev2 : ∀ᶠ p in 𝓝[T] p₀, r < p.2 := hsnd.eventually (lt_mem_nhds hr2)
          rw [indicator_of_mem (s := Ioc p₀.1 p₀.2) ⟨hr1, hr2.le⟩]
          have hS : {q | q ∈ T ∧ q.1 ≤ r ∧ r ≤ q.2} ∈ 𝓝[T] p₀ := by
            filter_upwards [self_mem_nhdsWithin, hev1, hev2] with q hq h1 h2
            exact ⟨hq, h1.le, h2.le⟩
          have hc : Tendsto (fun q => Ψ q r) (𝓝[T] p₀) (𝓝 (Ψ p₀ r)) :=
            (hcont p₀ hp₀ r hr1 hr2).mono_of_mem_nhdsWithin hS
          refine hc.congr' ?_
          filter_upwards [hev1, hev2] with q h1 h2
          exact (indicator_of_mem (s := Ioc q.1 q.2) ⟨h1, h2.le⟩ _).symm
        · have hev : ∀ᶠ p in 𝓝[T] p₀, p.2 < r := hsnd.eventually (gt_mem_nhds hr2)
          rw [indicator_of_notMem (s := Ioc p₀.1 p₀.2) (fun h => absurd h.2 (not_le.mpr hr2))]
          refine tendsto_const_nhds.congr' (hev.mono fun p hp => ?_)
          exact (indicator_of_notMem (s := Ioc p.1 p.2) (fun h => absurd h.2 (not_le.mpr hp))
            _).symm
  have := hlim.congr' (eventually_nhdsWithin_of_forall fun p hp => (hrepr p hp).symm)
  rw [ContinuousWithinAt, hrepr p₀ hp₀]
  exact this

end UnforcedLeray.Evolution
