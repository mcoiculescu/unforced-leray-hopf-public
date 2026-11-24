import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Time slices of `L^q` functions on a product (INF14 target T5, slice part)


target T5 (`stronglyMeasurable_toPath_Lq`) and bypass B7: the graph spaces `Y_q` (blueprint units
B0005, B0411, B0412, B0429) need only the product → Bochner direction of
`L^q(ν × μ; F) ≃ L^q(ν; L^q(μ; F))`: the time slices of a product `L^q` function form an a.e.
strongly measurable path in `L^q(μ; F)` whose `L^q(ν)` norm is the product norm. The full
isometric isomorphism is not built (bypass B7).

The proof follows the NonUniqueEuler `stronglyMeasurable_toPath`
(`NonUniqueEuler/P/Infra/JointRep/Measurable.lean`, proved there for `L²` through inner
products), with distances in place of inner products, so that it applies to every
`1 ≤ q < ∞`: `L^q(μ; F)` is separable when `α` is countably generated, `μ` is s-finite and `F` is
separable (Mathlib `Lp.SecondCountableTopology`), and `t ↦ dist (slice t) g` is measurable for
every `g` by Tonelli. `eq_iUnion_ball_of_isOpen` is copied from the same NonUniqueEuler file.

## Main results

* `toPathLq q μ f t`: the class in `L^q(μ)` of the slice `x ↦ f (t, x)` (zero when the slice is
  not in `L^q`);
* `stronglyMeasurable_toPathLq`: strong measurability for strongly measurable `f`;
* `stronglyMeasurable_toPath_Lq`: for `f ∈ L^q(ν × μ)`, the slice path is a.e. strongly
  measurable and `∫ ‖f(t, ·)‖_q^q dν = ‖f‖_q^q`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.BochnerTime

/-- In a separable pseudo-metric space with a dense sequence `z`, every open set is the union of
the balls `B(z k, 1/(n+1))` it contains. Copied from NonUniqueEuler
`P/Infra/JointRep/Measurable.lean` (`MeasurableAux.eq_iUnion_ball_of_isOpen`). -/
theorem eq_iUnion_ball_of_isOpen {X : Type*} [PseudoMetricSpace X] {z : ℕ → X}
    (hz : DenseRange z) {U : Set X} (hU : IsOpen U) :
    U = ⋃ k : ℕ, ⋃ n : ℕ, ⋃ (_ : Metric.ball (z k) (1 / ((n : ℝ) + 1)) ⊆ U),
      Metric.ball (z k) (1 / ((n : ℝ) + 1)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := hz.exists_dist_lt x hpos
    simp only [mem_iUnion]
    refine ⟨k, n, ?_, ?_⟩
    · intro y hy
      apply hball
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y (z k) + dist (z k) x := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy (by rwa [dist_comm])
        _ < ε := by linarith
    · rw [Metric.mem_ball]
      exact hk
  · simp only [iUnion_subset_iff]
    exact fun _ _ h => h

variable {τ α F : Type*} [MeasurableSpace τ] [MeasurableSpace α] {ν : Measure τ} {μ : Measure α}
  [NormedAddCommGroup F] {q : ℝ≥0∞}

open Classical in
/-- The class in `L^q(μ)` of the time slice `x ↦ f (t, x)`; zero when the slice is not in
`L^q(μ)`. -/
noncomputable def toPathLq (q : ℝ≥0∞) (μ : Measure α) (f : τ × α → F) (t : τ) : Lp F q μ :=
  if h : MemLp (fun x => f (t, x)) q μ then h.toLp _ else 0

theorem toPathLq_of_memLp {f : τ × α → F} {t : τ} (h : MemLp (fun x => f (t, x)) q μ) :
    toPathLq q μ f t = h.toLp _ := by
  rw [toPathLq, dif_pos h]

theorem toPathLq_of_not_memLp {f : τ × α → F} {t : τ} (h : ¬ MemLp (fun x => f (t, x)) q μ) :
    toPathLq q μ f t = 0 := by
  rw [toPathLq, dif_neg h]

/-- `toPathLq` only depends on the a.e. class of the slice. -/
theorem toPathLq_congr_ae {f g : τ × α → F} {t : τ}
    (h : (fun x => f (t, x)) =ᵐ[μ] fun x => g (t, x)) : toPathLq q μ f t = toPathLq q μ g t := by
  by_cases hm : MemLp (fun x => f (t, x)) q μ
  · have hm' : MemLp (fun x => g (t, x)) q μ := hm.ae_eq h
    rw [toPathLq_of_memLp hm, toPathLq_of_memLp hm']
    exact (MemLp.toLp_eq_toLp_iff _ _).2 h
  · have hm' : ¬ MemLp (fun x => g (t, x)) q μ := fun h' => hm (h'.ae_eq h.symm)
    rw [toPathLq_of_not_memLp hm, toPathLq_of_not_memLp hm']

/-- `‖g‖_q^q = ∫ ‖g‖^q` for `0 < q < ∞`. -/
theorem eLpNorm_rpow_eq_lintegral (hq0 : q ≠ 0) (hq : q ≠ ∞) (g : α → F) :
    eLpNorm g q μ ^ q.toReal = ∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_ne_zero.2 ⟨hq0, hq⟩)]

/-- For strongly measurable `f`, the distance from the slice path to a fixed `g ∈ L^q(μ)` is
measurable in time (Tonelli). -/
theorem measurable_edist_toPathLq [SFinite μ] [Fact (1 ≤ q)] (hq0 : q ≠ 0) (hq : q ≠ ∞)
    {f : τ × α → F} (hf : StronglyMeasurable f) (g : Lp F q μ) :
    Measurable fun t => edist (toPathLq q μ f t) g := by
  classical
  have hslice : ∀ t, StronglyMeasurable fun x => f (t, x) := fun t =>
    hf.comp_measurable measurable_prodMk_left
  have hN : Measurable fun t => ∫⁻ x, ‖f (t, x)‖ₑ ^ q.toReal ∂μ :=
    (hf.enorm.pow_const _).lintegral_prod_right'
  set G : Set τ := {t | MemLp (fun x => f (t, x)) q μ} with hG_def
  have hG : MeasurableSet G := by
    have : G = {t | ∫⁻ x, ‖f (t, x)‖ₑ ^ q.toReal ∂μ < ∞} := by
      ext t
      exact ⟨fun h => (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq).1 h.2,
        fun h => ⟨(hslice t).aestronglyMeasurable,
          (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq).2 h⟩⟩
    rw [this]
    exact measurableSet_lt hN measurable_const
  have hg : StronglyMeasurable (g : α → F) := Lp.stronglyMeasurable g
  have hD : Measurable fun t => (∫⁻ x, ‖f (t, x) - g x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
    have hm : Measurable fun z : τ × α => ‖f z - g z.2‖ₑ ^ q.toReal :=
      ((hf.sub (hg.comp_measurable measurable_snd)).enorm).pow_const _
    exact hm.lintegral_prod_right'.pow_const _
  have heq : (fun t => edist (toPathLq q μ f t) g) = G.piecewise
      (fun t => (∫⁻ x, ‖f (t, x) - g x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal))
      (fun _ => edist 0 g) := by
    funext t
    by_cases ht : t ∈ G
    · rw [piecewise_eq_of_mem _ _ _ ht, toPathLq_of_memLp ht, Lp.edist_def,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp ht] with x hx
      simp only [Pi.sub_apply, hx]
    · rw [piecewise_eq_of_notMem _ _ _ ht, toPathLq_of_not_memLp ht]
  rw [heq]
  exact hD.piecewise hG measurable_const

/-- **Strong measurability of the slice path** for a strongly measurable `f` (countably generated
`α`, s-finite `μ`, separable `F`, `1 ≤ q < ∞`). -/
theorem stronglyMeasurable_toPathLq [MeasurableSpace.CountablyGenerated α] [SFinite μ]
    [TopologicalSpace.SeparableSpace F] [Fact (1 ≤ q)] [hq : Fact (q ≠ ∞)] {f : τ × α → F}
    (hf : StronglyMeasurable f) : StronglyMeasurable (toPathLq q μ f) := by
  borelize ↥(Lp F q μ)
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq (Lp F q μ)
  have hdist : ∀ g, Measurable fun t => dist (toPathLq q μ f t) g := fun g => by
    simp_rw [dist_edist]
    exact (measurable_edist_toPathLq hq0 hq.out hf g).ennreal_toReal
  refine Measurable.stronglyMeasurable (measurable_of_isOpen fun U hU => ?_)
  rw [eq_iUnion_ball_of_isOpen hz hU]
  simp only [preimage_iUnion]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt (hdist _) measurable_const

/-- **Slices of a product `L^q` function** (T5; scoping signature
`stronglyMeasurable_toPath_Lq`). For `f ∈ L^q(ν × μ; F)`, `1 ≤ q < ∞`, the slice path
`t ↦ f(t, ·) ∈ L^q(μ; F)` is a.e. strongly measurable and
`∫ ‖f(t, ·)‖_q^q dν(t) = ‖f‖_{L^q(ν × μ)}^q`. -/
theorem stronglyMeasurable_toPath_Lq [MeasurableSpace.CountablyGenerated α] [SFinite μ]
    [SFinite ν] [TopologicalSpace.SeparableSpace F] [Fact (1 ≤ q)] [hq : Fact (q ≠ ∞)]
    {f : τ × α → F} (hf : MemLp f q (ν.prod μ)) :
    AEStronglyMeasurable (toPathLq q μ f) ν ∧
      ∫⁻ t, ‖toPathLq q μ f t‖ₑ ^ q.toReal ∂ν = eLpNorm f q (ν.prod μ) ^ q.toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  set f' : τ × α → F := hf.1.mk f with hf'_def
  have hf' : StronglyMeasurable f' := hf.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[ν.prod μ] f' := hf.1.ae_eq_mk
  have hslices : ∀ᵐ t ∂ν, (fun x => f (t, x)) =ᵐ[μ] fun x => f' (t, x) :=
    Measure.ae_ae_of_ae_prod hff'
  have hpath : toPathLq q μ f =ᵐ[ν] toPathLq q μ f' := by
    filter_upwards [hslices] with t ht using toPathLq_congr_ae ht
  refine ⟨(stronglyMeasurable_toPathLq hf').aestronglyMeasurable.congr hpath.symm, ?_⟩
  have hm : Measurable fun z : τ × α => ‖f' z‖ₑ ^ q.toReal := hf'.enorm.pow_const _
  have hR : eLpNorm f q (ν.prod μ) ^ q.toReal = ∫⁻ t, ∫⁻ x, ‖f' (t, x)‖ₑ ^ q.toReal ∂μ ∂ν := by
    rw [eLpNorm_congr_ae hff', eLpNorm_rpow_eq_lintegral hq0 hq.out,
      lintegral_prod _ hm.aemeasurable]
  rw [hR]
  have hfin : ∀ᵐ t ∂ν, ∫⁻ x, ‖f' (t, x)‖ₑ ^ q.toReal ∂μ < ∞ := by
    refine ae_lt_top hm.lintegral_prod_right' ?_
    rw [← hR]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hf.eLpNorm_ne_top
  refine lintegral_congr_ae ?_
  filter_upwards [hpath, hfin] with t ht htf
  rw [ht]
  have hmem : MemLp (fun x => f' (t, x)) q μ :=
    ⟨(hf'.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq.out).2 htf⟩
  rw [toPathLq_of_memLp hmem, Lp.enorm_def, eLpNorm_congr_ae hmem.coeFn_toLp,
    eLpNorm_rpow_eq_lintegral hq0 hq.out]

end UnforcedLeray.BochnerTime
