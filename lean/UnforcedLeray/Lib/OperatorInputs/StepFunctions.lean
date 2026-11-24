import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Step functions with disjoint finite-measure steps (helpers for ExternalInputs E10)

Helpers for the Riesz–Thorin interpolation bound `norm_le_of_rieszThorin` (scoping note

*Classical Fourier Analysis*, Thm. 1.3.4; blueprint units B0529, B0534, B0544, `paper/main.tex`
3827–3856). The proof of Riesz–Thorin tests an operator on *step functions*
`Σᵢ 1_{Aᵢ} vᵢ` with finitely many pairwise disjoint measurable steps `Aᵢ` of finite measure,
the simple functions with finite-measure support. This file collects what is used about them:

* `stepFun A v = Σᵢ 1_{Aᵢ} vᵢ`, its values (`stepFun_apply_of_mem`), and the transfer of a map
  `Φ` with `Φ 0 = 0` through it (`map_stepFun`);
* `lintegral_enorm_rpow_stepFun`: `∫ ‖Σᵢ 1_{Aᵢ} vᵢ‖^r = Σᵢ ‖vᵢ‖^r μ(Aᵢ)`;
* `integral_inner_stepFun`: `∫ ⟪Σᵢ 1_{Aᵢ} wᵢ, φ⟫ = Σᵢ ∫_{Aᵢ} ⟪wᵢ, φ⟫`;
* `enorm_integral_inner_stepFun_le`: Hölder's inequality against a step function,
  `|∫ ⟪Σᵢ 1_{Aᵢ} wᵢ, φ⟫| ≤ (Σᵢ ‖wᵢ‖^Q μ(Aᵢ))^{1/Q} ‖φ‖_{L^P}`;
* `stepLp p A hA hAμ c v = Σᵢ cᵢ • 1_{Aᵢ} vᵢ ∈ Lp F p μ` and its representative
  (`coeFn_stepLp`), and the representative of `Σᵢ cᵢ • uᵢ` in `Lp` (`coeFn_sum_smul`);
* `exists_stepFun_ae_eq`: every element of `Lp.simpleFunc F p μ` (`0 < p < ∞`) is a.e. a step
  function with nonzero values.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.ExternalInputs

variable {α : Type*} {ι : Type*} [Fintype ι]

/-- The step function `Σᵢ 1_{Aᵢ} vᵢ`. -/
def stepFun {E : Type*} [AddCommMonoid E] (A : ι → Set α) (v : ι → E) (x : α) : E :=
  ∑ i, (A i).indicator (fun _ => v i) x

theorem stepFun_apply_of_mem {E : Type*} [AddCommMonoid E] {A : ι → Set α}
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → E) {x : α} {j : ι} (hx : x ∈ A j) :
    stepFun A v x = v j := by
  unfold stepFun
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro i _ hij
    exact Set.indicator_of_notMem (fun hxi => Set.disjoint_left.mp (hAd hij) hxi hx) _
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem stepFun_apply_of_forall_notMem {E : Type*} [AddCommMonoid E] {A : ι → Set α}
    (v : ι → E) {x : α} (hx : ∀ i, x ∉ A i) : stepFun A v x = 0 := by
  unfold stepFun
  exact Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hx i) _

/-- A map `Φ` with `Φ 0 = 0` passes through a step function with disjoint steps. -/
theorem map_stepFun {E G : Type*} [AddCommMonoid E] [AddCommMonoid G] {A : ι → Set α}
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → E) (Φ : E → G) (hΦ : Φ 0 = 0)
    (x : α) : Φ (stepFun A v x) = stepFun A (fun i => Φ (v i)) x := by
  by_cases h : ∃ j, x ∈ A j
  · obtain ⟨j, hj⟩ := h
    rw [stepFun_apply_of_mem hAd v hj, stepFun_apply_of_mem hAd _ hj]
  · push Not at h
    rw [stepFun_apply_of_forall_notMem v h, stepFun_apply_of_forall_notMem _ h, hΦ]

theorem stepFun_smul {E : Type*} [AddCommMonoid E] [Module ℂ E] (A : ι → Set α) (c : ι → ℂ)
    (v : ι → E) (x : α) :
    stepFun A (fun i => c i • v i) x = ∑ i, c i • (A i).indicator (fun _ => v i) x := by
  unfold stepFun
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : x ∈ A i <;> simp [hx]

variable [MeasurableSpace α] {μ : Measure α}

theorem stronglyMeasurable_stepFun {E : Type*} [NormedAddCommGroup E] {A : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i)) (v : ι → E) : StronglyMeasurable (stepFun A v) := by
  unfold stepFun
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ => stronglyMeasurable_const.indicator (hA i)

theorem lintegral_stepFun {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞) :
    ∫⁻ x, stepFun A c x ∂μ = ∑ i, c i * μ (A i) := by
  unfold stepFun
  rw [lintegral_finsetSum' _ fun i _ => aemeasurable_const.indicator (hA i)]
  exact Finset.sum_congr rfl fun i _ => lintegral_indicator_const (hA i) _

/-- `∫ ‖Σᵢ 1_{Aᵢ} vᵢ‖^r = Σᵢ ‖vᵢ‖^r μ(Aᵢ)` for disjoint steps and `r > 0`. -/
theorem lintegral_enorm_rpow_stepFun {E : Type*} [NormedAddCommGroup E] {A : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → E)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖stepFun A v x‖ₑ ^ r ∂μ = ∑ i, ‖v i‖ₑ ^ r * μ (A i) := by
  have h : ∀ x, ‖stepFun A v x‖ₑ ^ r = stepFun A (fun i => ‖v i‖ₑ ^ r) x := fun x =>
    map_stepFun hAd v (fun y => ‖y‖ₑ ^ r) (by simp [hr]) x
  simp_rw [h]
  exact lintegral_stepFun hA _

/-- `‖Σᵢ 1_{Aᵢ} vᵢ‖_{L^p} = (Σᵢ ‖vᵢ‖^P μ(Aᵢ))^{1/P}`, `P = p.toReal`, for `0 < p < ∞`. -/
theorem eLpNorm_stepFun {E : Type*} [NormedAddCommGroup E] {A : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → E)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (stepFun A v) p μ = (∑ i, ‖v i‖ₑ ^ p.toReal * μ (A i)) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    lintegral_enorm_rpow_stepFun hA hAd v (ENNReal.toReal_pos hp0 hpt)]

/-- Cauchy–Schwarz in `ℝ≥0∞`. -/
theorem enorm_inner_le_enorm_mul_enorm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (a b : F) : ‖⟪a, b⟫_ℂ‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm a b)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_indicator_const (B : Set α) (w : F) (φ : α → F) (x : α) :
    ⟪B.indicator (fun _ => w) x, φ x⟫_ℂ = B.indicator (fun y => ⟪w, φ y⟫_ℂ) x := by
  by_cases hx : x ∈ B <;> simp [hx]

/-- `∫ ⟪Σᵢ 1_{Aᵢ} wᵢ, φ⟫ = Σᵢ ∫_{Aᵢ} ⟪wᵢ, φ⟫`, when `φ` is integrable on every step. -/
theorem integral_inner_stepFun {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (w : ι → F)
    {φ : α → F} (hφ : ∀ i, IntegrableOn φ (A i) μ) :
    ∫ x, ⟪stepFun A w x, φ x⟫_ℂ ∂μ = ∑ i, ∫ x in A i, ⟪w i, φ x⟫_ℂ ∂μ := by
  have h : ∀ x, ⟪stepFun A w x, φ x⟫_ℂ = ∑ i, (A i).indicator (fun y => ⟪w i, φ y⟫_ℂ) x := by
    intro x
    unfold stepFun
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => inner_indicator_const _ _ _ _
  simp_rw [h]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_indicator_iff (hA i)).2 (Integrable.const_inner (𝕜 := ℂ) (w i) (hφ i))]
  exact Finset.sum_congr rfl fun i _ => integral_indicator (hA i)

/-- **Hölder against a step function**: for conjugate exponents `P, Q`,
`‖∫ ⟪Σᵢ 1_{Aᵢ} wᵢ, φ⟫‖ ≤ (Σᵢ ‖wᵢ‖^Q μ(Aᵢ))^{1/Q} ‖φ‖_{L^P}`. -/
theorem enorm_integral_inner_stepFun_le {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Function.onFun Disjoint A)) (w : ι → F) {φ : α → F}
    (hφ : AEStronglyMeasurable φ μ) {P Q : ℝ} (hPQ : P.HolderConjugate Q) :
    ‖∫ x, ⟪stepFun A w x, φ x⟫_ℂ ∂μ‖ₑ ≤
      (∑ i, ‖w i‖ₑ ^ Q * μ (A i)) ^ (1 / Q) * eLpNorm φ (ENNReal.ofReal P) μ := by
  have hP0 : (ENNReal.ofReal P) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hPQ.pos
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hPQ.nonneg, ← lintegral_enorm_rpow_stepFun hA hAd w hPQ.symm.pos]
  calc ‖∫ x, ⟪stepFun A w x, φ x⟫_ℂ ∂μ‖ₑ
      ≤ ∫⁻ x, ‖⟪stepFun A w x, φ x⟫_ℂ‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖stepFun A w x‖ₑ * ‖φ x‖ₑ ∂μ :=
        lintegral_mono fun x => enorm_inner_le_enorm_mul_enorm _ _
    _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hPQ.symm
        (stronglyMeasurable_stepFun hA w).aestronglyMeasurable.enorm hφ.enorm

/-- The representative of a finite linear combination in `Lp`. -/
theorem coeFn_sum_smul {p : ℝ≥0∞} (c : ι → ℂ) (u : ι → Lp F p μ) :
    ⇑(∑ i, c i • u i) =ᵐ[μ] fun x => ∑ i, c i • u i x := by
  classical
  have key : ∀ s : Finset ι, ⇑(∑ i ∈ s, c i • u i) =ᵐ[μ] fun x => ∑ i ∈ s, c i • u i x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero (E := F) (p := p) (μ := μ)] with x hx
      simp only [Finset.sum_empty] at hx ⊢
      exact hx
    | insert j s hj ih =>
      filter_upwards [Lp.coeFn_add (c j • u j) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c j) (u j),
        ih] with x h1 h2 h3
      rw [Finset.sum_insert hj, h1, Pi.add_apply, h2, h3, Finset.sum_insert hj, Pi.smul_apply]
  exact key Finset.univ

/-- The `Lp` step element `Σᵢ cᵢ • 1_{Aᵢ} vᵢ`. -/
def stepLp (p : ℝ≥0∞) (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hAμ : ∀ i, μ (A i) ≠ ∞) (c : ι → ℂ) (v : ι → F) : Lp F p μ :=
  ∑ i, c i • indicatorConstLp p (hA i) (hAμ i) (v i)

theorem coeFn_stepLp (p : ℝ≥0∞) {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i))
    (hAμ : ∀ i, μ (A i) ≠ ∞) (c : ι → ℂ) (v : ι → F) :
    ⇑(stepLp p A hA hAμ c v) =ᵐ[μ] stepFun A (fun i => c i • v i) := by
  have hall : ∀ᵐ x ∂μ, ∀ i, indicatorConstLp p (hA i) (hAμ i) (v i) x =
      (A i).indicator (fun _ => v i) x :=
    ae_all_iff.2 fun i => indicatorConstLp_coeFn
  filter_upwards [coeFn_sum_smul c (fun i => indicatorConstLp p (hA i) (hAμ i) (v i)), hall]
    with x h1 h2
  rw [stepLp, h1, stepFun_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [h2 i]

theorem enorm_stepLp {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) {A : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i)) (hAμ : ∀ i, μ (A i) ≠ ∞)
    (hAd : Pairwise (Function.onFun Disjoint A)) (c : ι → ℂ) (v : ι → F) :
    ‖stepLp p A hA hAμ c v‖ₑ =
      (∑ i, ‖c i • v i‖ₑ ^ p.toReal * μ (A i)) ^ (1 / p.toReal) := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (coeFn_stepLp p hA hAμ c v),
    eLpNorm_stepFun hA hAd _ hp0 hpt]

/-- The image of a step element under a bounded operator, as a combination of the images of the
atoms. -/
theorem coeFn_apply_stepLp {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (S : Lp F p μ →L[ℂ] Lp F q μ) {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i))
    (hAμ : ∀ i, μ (A i) ≠ ∞) (c : ι → ℂ) (v : ι → F) :
    ⇑(S (stepLp p A hA hAμ c v)) =ᵐ[μ]
      fun x => ∑ i, c i • S (indicatorConstLp p (hA i) (hAμ i) (v i)) x := by
  have h : S (stepLp p A hA hAμ c v) =
      ∑ i, c i • S (indicatorConstLp p (hA i) (hAμ i) (v i)) := by
    simp only [stepLp, map_sum, map_smul]
  rw [h]
  exact coeFn_sum_smul _ _

/-- A function in `L^p`, `1 ≤ p`, is integrable on every set of finite measure. -/
theorem integrableOn_of_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) {φ : α → F} (hφ : MemLp φ p μ)
    {B : Set α} (hB : μ B ≠ ∞) : IntegrableOn φ B μ := by
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hB
  exact (hφ.restrict B).integrable hp

/-- Every simple function in `L^p` (`0 < p < ∞`) is a.e. a step function with nonzero values on
pairwise disjoint measurable steps of finite measure. The index type is a subtype of a finset
of values, in the universe of `F`. -/
theorem exists_stepFun_ae_eq {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (s : Lp.simpleFunc F p μ) :
    ∃ (K : Finset F) (B : K → Set α) (_ : ∀ k, MeasurableSet (B k))
      (_ : ∀ k, μ (B k) ≠ ∞) (_ : Pairwise (Function.onFun Disjoint B)),
      (∀ k : K, (k : F) ≠ 0) ∧
        ((s : Lp F p μ) : α → F) =ᵐ[μ] stepFun B (fun k => (k : F)) := by
  classical
  set f := Lp.simpleFunc.toSimpleFunc s with hf_def
  have hf : MemLp f p μ := Lp.simpleFunc.memLp s
  have hd : Pairwise (Function.onFun Disjoint
      (fun k : (f.range.erase 0 : Finset F) => f ⁻¹' {(k : F)})) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj => hij ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hj
    exact Subtype.ext (hi.symm.trans hj)
  refine ⟨f.range.erase 0, fun k => f ⁻¹' {(k : F)}, fun k => f.measurableSet_preimage _,
    fun k => (SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hpt f hf k
      (Finset.ne_of_mem_erase k.2)).ne, hd, fun k => Finset.ne_of_mem_erase k.2, ?_⟩
  filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun s] with x hx
  rw [← hx]
  by_cases h0 : f x = 0
  · rw [h0, stepFun_apply_of_forall_notMem]
    intro k hk
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
    exact Finset.ne_of_mem_erase k.2 (hk.symm.trans h0)
  · have hmem : f x ∈ f.range.erase 0 := Finset.mem_erase.2 ⟨h0, f.mem_range_self x⟩
    rw [stepFun_apply_of_mem hd _ (j := ⟨f x, hmem⟩) rfl]

end UnforcedLeray.ExternalInputs
