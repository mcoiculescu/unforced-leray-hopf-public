import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Jointly measurable representatives of `Lp`-valued paths

Let `(α, μ)` be a measure space, `E` a Banach space and `1 ≤ p ≤ ∞`. A path
`u : τ → Lp E p μ` is a family of a.e. classes; to integrate over `τ × α` one needs a single
function `F : τ × α → E` that is jointly strongly measurable and represents `u t` for **every**
time `t` (not merely almost every `t`). This file constructs such representatives.

## Main results

* `exists_stronglyMeasurable_rep`: a strongly measurable path `u : τ → Lp E p μ`, on an
  arbitrary measurable space `τ`, has a strongly measurable `F : τ × α → E` with
  `(fun x => F (t, x)) =ᵐ[μ] u t` for every `t`.
* `stronglyMeasurable_indicator_of_continuousOn`: a function continuous on a measurable set `s`
  of a second-countable space, extended by zero, is strongly measurable.
* `exists_stronglyMeasurable_rep_of_continuousOn`: a path `f : τ → Lp E p μ` continuous on a
  measurable set `s` of a second-countable space `τ` has a strongly measurable
  `F : τ × α → E` with `(fun x => F (t, x)) =ᵐ[μ] f t` for every `t ∈ s`.
* `exists_stronglyMeasurable_rep_of_continuousOn_ordConnected`, and the `Icc`, `Ico`, `Ioc`,
  `Ioo` versions: the same for an interval `s ⊆ ℝ`.

No σ-finiteness of `μ`, no separability of `E` and no finiteness of `p` is needed: the
hypotheses are `[CompleteSpace E]` and `[Fact (1 ≤ p)]` only.

## Construction

1. A simple path `f : SimpleFunc τ (Lp E p μ)` gives a jointly strongly measurable function
   `(t, x) ↦ f t x` (a finite sum over the range of `f`).
2. For `ε > 0`, `ψ t := hu.approx (n t) t` with `n t` the least index that is `ε`-close to
   `u t` (`Nat.find`) is `ε`-close to `u` at every `t` and jointly strongly measurable.
3. With `ε = 2^{-N}` one gets `ψ N`. For each fixed `t`, the sequence `ψ N t` is Cauchy in
   `Lp` with summable rates, so it converges a.e. (`Lp.ae_tendsto_of_cauchy_eLpNorm`); a
   subsequence converges a.e. to `u t` (convergence in measure), so the a.e. limit is `u t`.
   `F (t, x) := limUnder atTop (fun N => ψ N t x)` is strongly measurable
   (`StronglyMeasurable.limUnder`).
4. A path continuous on a measurable set `s` of a second-countable space, extended by zero, is
   strongly measurable (it is Borel measurable and has separable range).

The construction follows `NonUniqueEuler/P/Infra/JointRep/Representative.lean` and
`NonUniqueEuler/P/Infra/JointRep/Measurable.lean` of the reference formalization, generalized
from `Lp ℝ 2` to `Lp E p` (the real `limsup` is replaced by `limUnder` in the Banach space `E`),
and with Pettis' theorem replaced by the direct continuity argument of step 4.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace UnforcedLeray.Infra.JointMeasurableRep

section Abstract

variable {τ α E : Type*} [MeasurableSpace τ] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- A simple path into `Lp E p μ` is jointly strongly measurable: `(t, x) ↦ f t x` is a finite
sum of products of indicators of the measurable fibres of `f` with representatives of its
finitely many values. -/
theorem stronglyMeasurable_uncurry_simpleFunc (f : SimpleFunc τ (Lp E p μ)) :
    StronglyMeasurable fun q : τ × α => (f q.1 : α → E) q.2 := by
  classical
  have key : (fun q : τ × α => (f q.1 : α → E) q.2) =
      fun q => ∑ v ∈ f.range, if f q.1 = v then (v : α → E) q.2 else 0 := by
    funext q
    rw [Finset.sum_ite_eq, ite_eq_left (f.mem_range_self q.1)]
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun v _ => ?_
  refine StronglyMeasurable.ite ?_ ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)
    stronglyMeasurable_const
  exact measurable_fst (f.measurableSet_fiber v)

/-- An `ε`-approximation of a strongly measurable `Lp`-valued path, uniform in time, whose
representatives are jointly strongly measurable. -/
theorem exists_stronglyMeasurable_uncurry_approx [Fact (1 ≤ p)] {u : τ → Lp E p μ}
    (hu : StronglyMeasurable u) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : τ → Lp E p μ, StronglyMeasurable (fun q : τ × α => (ψ q.1 : α → E) q.2) ∧
      ∀ t, dist (ψ t) (u t) < ε := by
  classical
  set f := hu.approx
  have h : ∀ t, ∃ n, dist (f n t) (u t) < ε := fun t =>
    (Metric.tendsto_nhds.1 (hu.tendsto_approx t) ε hε).exists
  refine ⟨fun t => f (Nat.find (h t)) t, ?_, fun t => Nat.find_spec (h t)⟩
  have hp : ∀ n, MeasurableSet {q : τ × α | dist (f n q.1) (u q.1) < ε} := fun n =>
    measurable_fst (measurableSet_lt ((f n).stronglyMeasurable.dist hu).measurable
      measurable_const)
  have hfm : ∀ n, StronglyMeasurable fun q : τ × α => (f n q.1 : α → E) q.2 := fun n =>
    stronglyMeasurable_uncurry_simpleFunc (f n)
  borelize E
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · exact Measurable.find (f := fun n (q : τ × α) => (f n q.1 : α → E) q.2)
      (p := fun n (q : τ × α) => dist (f n q.1) (u q.1) < ε)
      (fun n => (hfm n).measurable) hp (fun q => h q.1)
  · have hsep : IsSeparable (⋃ n, range (fun q : τ × α => (f n q.1 : α → E) q.2)) :=
      .iUnion fun n => (hfm n).isSeparable_range
    refine hsep.mono ?_
    rintro _ ⟨q, rfl⟩
    exact mem_iUnion.2 ⟨Nat.find (h q.1), q, rfl⟩

/-- The Cauchy bound for a sequence that is `2^{-N}`-close to a fixed point. -/
theorem dist_lt_two_mul_of_geometric_close {X : Type*} [PseudoMetricSpace X] {ψ : ℕ → X}
    {v : X} (hd : ∀ N, dist (ψ N) v < (1 / 2 : ℝ) ^ N) {N n m : ℕ} (hn : N ≤ n) (hm : N ≤ m) :
    dist (ψ n) (ψ m) < 2 * (1 / 2 : ℝ) ^ N := by
  have h1 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h2 : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  calc dist (ψ n) (ψ m) ≤ dist (ψ n) v + dist (ψ m) v := dist_triangle_right _ _ _
    _ < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ m := add_lt_add (hd n) (hd m)
    _ ≤ 2 * (1 / 2 : ℝ) ^ N := by linarith

/-- **The limit step.** If `ψ N t` is `2^{-N}`-close to `u t` in `Lp` for every `N` and every
`t`, then for every `t` the pointwise limit of the representatives of `ψ N t` exists a.e. and
represents `u t`. -/
theorem limUnder_ae_eq_of_geometric [CompleteSpace E] [Fact (1 ≤ p)]
    {ψ : ℕ → Lp E p μ} {v : Lp E p μ} (hd : ∀ N, dist (ψ N) v < (1 / 2 : ℝ) ^ N) :
    (fun x => limUnder atTop (fun N => (ψ N : α → E) x)) =ᵐ[μ] v := by
  have hB : ∑' N : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
      (summable_geometric_two.mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have h1 : ∀ᵐ x ∂μ, ∃ l : E, Tendsto (fun N => (ψ N : α → E) x) atTop (𝓝 l) := by
    refine Lp.ae_tendsto_of_cauchy_eLpNorm (p := p) (fun n => Lp.aestronglyMeasurable _)
      (Fact.out : 1 ≤ p) hB fun N n m hn hm => ?_
    rw [← Lp.edist_def, edist_lt_ofReal]
    exact dist_lt_two_mul_of_geometric_close hd hn hm
  have hlim : Tendsto ψ atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun N => (hd N).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨ns, hns, h2⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [h1, h2] with x ⟨l, hl⟩ hx
  rw [hl.limUnder_eq]
  exact tendsto_nhds_unique (hl.comp hns.tendsto_atTop) hx

/-- **Jointly measurable representative of a strongly measurable path.** A strongly measurable
path `u : τ → Lp E p μ` (on an arbitrary measurable space `τ`) has a strongly measurable
`F : τ × α → E` whose slice at **every** time `t` represents `u t`. -/
theorem exists_stronglyMeasurable_rep [CompleteSpace E] [Fact (1 ≤ p)] {u : τ → Lp E p μ}
    (hu : StronglyMeasurable u) :
    ∃ F : τ × α → E, StronglyMeasurable F ∧ ∀ t, (fun x => F (t, x)) =ᵐ[μ] u t := by
  have hex : ∀ N : ℕ, ∃ ψ : τ → Lp E p μ,
      StronglyMeasurable (fun q : τ × α => (ψ q.1 : α → E) q.2) ∧
        ∀ t, dist (ψ t) (u t) < (1 / 2 : ℝ) ^ N := fun N =>
    exists_stronglyMeasurable_uncurry_approx hu (pow_pos (by norm_num) N)
  choose ψ hψm hψd using hex
  have hF : StronglyMeasurable
      (fun q : τ × α => limUnder atTop (fun N => (ψ N q.1 : α → E) q.2)) :=
    StronglyMeasurable.limUnder (f := fun N (q : τ × α) => (ψ N q.1 : α → E) q.2) hψm
  refine ⟨fun q => limUnder atTop (fun N => (ψ N q.1 : α → E) q.2), hF, fun t => ?_⟩
  have ht : (fun x => limUnder atTop (fun N => (ψ N t : α → E) x)) =ᵐ[μ] u t :=
    limUnder_ae_eq_of_geometric (fun N => hψd N t)
  exact ht

/-- A function continuous on a measurable set `s`, extended by zero off `s`, is strongly
measurable, when either the source or the target space is second-countable. -/
theorem stronglyMeasurable_indicator_of_continuousOn [TopologicalSpace τ]
    [OpensMeasurableSpace τ] {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [Zero β] [h : SecondCountableTopologyEither τ β] {f : τ → β} {s : Set τ}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : StronglyMeasurable (s.indicator f) := by
  classical
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · have hpw : s.indicator f = s.piecewise f 0 := by
      funext t
      by_cases ht : t ∈ s <;> simp [ht, Set.piecewise]
    rw [hpw]
    exact hf.measurable_piecewise continuousOn_const hs
  · have himg : IsSeparable (f '' s) := by
      cases h.out
      · rw [image_eq_range]
        exact isSeparable_range <| continuousOn_iff_continuous_domRestrict.1 hf
      · exact .of_separableSpace _
    refine (himg.union (Set.finite_singleton (0 : β)).isSeparable).mono ?_
    rintro _ ⟨t, rfl⟩
    by_cases ht : t ∈ s
    · left
      rw [indicator_of_mem ht]
      exact mem_image_of_mem f ht
    · right
      rw [indicator_of_notMem ht]
      rfl

/-- **Jointly measurable representative of a path continuous on a measurable set.** Let `τ` be
a second-countable space with its Borel σ-algebra (or a finer one making opens measurable), `s`
a measurable subset, and `f : τ → Lp E p μ` continuous on `s`. Then there is a strongly
measurable `F : τ × α → E` with `(fun x => F (t, x)) =ᵐ[μ] f t` for **every** `t ∈ s`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn [TopologicalSpace τ]
    [SecondCountableTopology τ] [OpensMeasurableSpace τ] [CompleteSpace E] [Fact (1 ≤ p)]
    {f : τ → Lp E p μ} {s : Set τ} (hs : MeasurableSet s) (hf : ContinuousOn f s) :
    ∃ F : τ × α → E, StronglyMeasurable F ∧ ∀ t ∈ s, (fun x => F (t, x)) =ᵐ[μ] f t := by
  obtain ⟨F, hFm, hF⟩ :=
    exists_stronglyMeasurable_rep (μ := μ) (stronglyMeasurable_indicator_of_continuousOn hf hs)
  refine ⟨F, hFm, fun t ht => ?_⟩
  have := hF t
  rwa [indicator_of_mem ht] at this

end Abstract

section Uniqueness

variable {τ α E : Type*} [MeasurableSpace τ] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

/-- Two jointly strongly measurable functions whose time slices agree `μ`-a.e. for `ν`-a.e.
time agree a.e. for the product measure `ν.prod μ` (Tonelli for the measurable set where they
differ). -/
theorem ae_eq_prod_of_ae_ae_eq {ν : Measure τ} [SFinite μ] {F F' : τ × α → E}
    (hF : StronglyMeasurable F) (hF' : StronglyMeasurable F')
    (h : ∀ᵐ t ∂ν, (fun x => F (t, x)) =ᵐ[μ] fun x => F' (t, x)) : F =ᵐ[ν.prod μ] F' :=
  (Measure.ae_prod_iff_ae_ae (hF.measurableSet_eq_fun hF')).2 h

/-- **Uniqueness.** Two jointly strongly measurable representatives of the same path
`f : τ → Lp E p μ` at the times of a measurable set `s` agree a.e. for `(ν.restrict s).prod μ`,
for every measure `ν` on the times. -/
theorem ae_eq_prod_of_isRep {p : ℝ≥0∞} {ν : Measure τ} [SFinite μ] {s : Set τ}
    (hs : MeasurableSet s) {f : τ → Lp E p μ} {F F' : τ × α → E}
    (hF : StronglyMeasurable F) (hF' : StronglyMeasurable F')
    (hFf : ∀ t ∈ s, (fun x => F (t, x)) =ᵐ[μ] f t)
    (hF'f : ∀ t ∈ s, (fun x => F' (t, x)) =ᵐ[μ] f t) :
    F =ᵐ[(ν.restrict s).prod μ] F' :=
  ae_eq_prod_of_ae_ae_eq hF hF'
    (ae_restrict_of_forall_mem hs fun t ht => (hFf t ht).trans (hF'f t ht).symm)

end Uniqueness

section Real

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Intervals of times.** A path `f : ℝ → Lp E p μ` continuous on an order-connected set
`s ⊆ ℝ` (any interval) has a strongly measurable `F : ℝ × α → E` with
`(fun x => F (t, x)) =ᵐ[μ] f t` for every `t ∈ s`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn_ordConnected {f : ℝ → Lp E p μ}
    {s : Set ℝ} (hs : s.OrdConnected) (hf : ContinuousOn f s) :
    ∃ F : ℝ × α → E, StronglyMeasurable F ∧ ∀ t ∈ s, (fun x => F (t, x)) =ᵐ[μ] f t :=
  exists_stronglyMeasurable_rep_of_continuousOn hs.measurableSet hf

/-- The closed-interval case of `exists_stronglyMeasurable_rep_of_continuousOn_ordConnected`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn_Icc {f : ℝ → Lp E p μ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ F : ℝ × α → E, StronglyMeasurable F ∧ ∀ t ∈ Icc a b, (fun x => F (t, x)) =ᵐ[μ] f t :=
  exists_stronglyMeasurable_rep_of_continuousOn measurableSet_Icc hf

/-- The `Ico` case of `exists_stronglyMeasurable_rep_of_continuousOn_ordConnected`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn_Ico {f : ℝ → Lp E p μ} {a b : ℝ}
    (hf : ContinuousOn f (Ico a b)) :
    ∃ F : ℝ × α → E, StronglyMeasurable F ∧ ∀ t ∈ Ico a b, (fun x => F (t, x)) =ᵐ[μ] f t :=
  exists_stronglyMeasurable_rep_of_continuousOn measurableSet_Ico hf

/-- The `Ioc` case of `exists_stronglyMeasurable_rep_of_continuousOn_ordConnected`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn_Ioc {f : ℝ → Lp E p μ} {a b : ℝ}
    (hf : ContinuousOn f (Ioc a b)) :
    ∃ F : ℝ × α → E, StronglyMeasurable F ∧ ∀ t ∈ Ioc a b, (fun x => F (t, x)) =ᵐ[μ] f t :=
  exists_stronglyMeasurable_rep_of_continuousOn measurableSet_Ioc hf

/-- The open-interval case of `exists_stronglyMeasurable_rep_of_continuousOn_ordConnected`. -/
theorem exists_stronglyMeasurable_rep_of_continuousOn_Ioo {f : ℝ → Lp E p μ} {a b : ℝ}
    (hf : ContinuousOn f (Ioo a b)) :
    ∃ F : ℝ × α → E, StronglyMeasurable F ∧ ∀ t ∈ Ioo a b, (fun x => F (t, x)) =ᵐ[μ] f t :=
  exists_stronglyMeasurable_rep_of_continuousOn measurableSet_Ioo hf

end Real

end UnforcedLeray.Infra.JointMeasurableRep
