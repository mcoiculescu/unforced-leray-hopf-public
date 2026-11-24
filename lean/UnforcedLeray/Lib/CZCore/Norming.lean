import UnforcedLeray.Lib.CZCore.Density
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.ConjExponents

/-!
# Converse Hölder by smooth test functions (INF01 T11)


target T11 (the duality step of the Calderón–Zygmund core, decision D4 of the scoping README).

The norming argument is copied and adapted from the NonUniqueEuler formalization,
`NonUniqueEuler/P/Infra/LpDual/WeakBounded.lean` (private lemma
`eLpNorm_le_of_forall_abs_integral_mul_le`, lines 47–115, and its two pointwise helpers),
with the namespace renamed. The adaptation: the core lemma
`eLpNorm_le_of_abs_integral_mul_norming_le` only asks the pairing bound for the norming
function `ψ = f |f|^{p-2}` itself, so it can be applied to truncations.

## Main results

* `eLpNorm_le_of_forall_abs_integral_mul_le` (public form of the NonUniqueEuler lemma):
  `f ∈ L^p`, `|∫ f ψ| ≤ C ‖ψ‖_{p'}` for all `ψ ∈ L^{p'}` ⟹ `‖f‖_p ≤ C`.
* `eLpNorm_le_of_forall_test_pairing` (**T11**, scoping signature): the same with smooth
  compactly supported tests `ψ`, on a finite-dimensional space with a Haar measure.
* `eLpNorm_le_of_forall_test_pairing_of_memLp_two` (**T11, `L²` form**): `f ∈ L²` (not assumed
  in `L^p`), smooth compactly supported tests; conclusion `f ∈ L^p` with `‖f‖_p ≤ C`. This is the
  form used for `p > 2` in `lp_bound` (T12), where `T f` is a priori only in `L²`.
* `ofReal_abs_integral_mul_le`: Hölder `|∫ f g| ≤ ‖f‖_p ‖g‖_q` in `ℝ≥0∞`, no integrability
  hypotheses.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.CZ

set_option autoImplicit false

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Copied from NonUniqueEuler `P/Infra/LpDual/WeakBounded.lean:39`.
`|t |t|^{p-2}| = |t|^{p-1}` for `1 < p`. -/
theorem abs_mul_abs_rpow_sub_two {p : ℝ} (hp : 1 < p) (t : ℝ) :
    |t * |t| ^ (p - 2)| = |t| ^ (p - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have ht' : 0 < |t| := abs_pos.mpr ht
    have h : |t| ^ (p - 1) = |t| ^ (1 : ℝ) * |t| ^ (p - 2) := by
      rw [← Real.rpow_add ht']; congr 1; ring
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), h, Real.rpow_one]

/-- Copied from NonUniqueEuler `P/Infra/LpDual/WeakBounded.lean:49`.
`t (t |t|^{p-2}) = |t|^p` for `1 < p`. -/
theorem mul_mul_abs_rpow_sub_two {p : ℝ} (hp : 1 < p) (t : ℝ) :
    t * (t * |t| ^ (p - 2)) = |t| ^ p := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have ht' : 0 < |t| := abs_pos.mpr ht
    have h : |t| ^ p = |t| ^ (2 : ℝ) * |t| ^ (p - 2) := by
      rw [← Real.rpow_add ht']; congr 1; ring
    rw [h, Real.rpow_two, sq_abs, ← mul_assoc, sq]

/-- The norming function `ψ = f ‖f‖^{p-2}` of `f ∈ L^p` lies in `L^{p'}`. -/
theorem memLp_norming {p : ℝ} (hp : 1 < p) {f : α → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => f x * ‖f x‖ ^ (p - 2)) (ENNReal.ofReal p.conjExponent) μ := by
  have hp1 : 0 < p - 1 := by linarith
  have hψ_norm : ∀ x, ‖‖f x‖ ^ (p - 1)‖ = ‖f x * ‖f x‖ ^ (p - 2)‖ := fun x => by
    simp only [Real.norm_eq_abs]
    rw [abs_mul_abs_rpow_sub_two hp (f x), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hψ_meas : AEStronglyMeasurable (fun x => f x * ‖f x‖ ^ (p - 2)) μ :=
    hf.1.mul (hf.1.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hnorm_rpow : MemLp (fun x => ‖f x‖ ^ (p - 1)) (ENNReal.ofReal p.conjExponent) μ := by
    have h := hf.norm_rpow_div (ENNReal.ofReal (p - 1))
    rwa [ENNReal.toReal_ofReal hp1.le, ← ENNReal.ofReal_div_of_pos hp1] at h
  exact hnorm_rpow.congr_norm hψ_meas (Eventually.of_forall hψ_norm)

/-- **Norming, adapted from NonUniqueEuler** (`P/Infra/LpDual/WeakBounded.lean:58`): for
`f ∈ L^p`, `1 < p`, if the pairing bound `|∫ f ψ| ≤ C ‖ψ‖_{p'}` holds for the norming function
`ψ = f ‖f‖^{p-2}`, then `‖f‖_p ≤ C`. -/
theorem eLpNorm_le_of_abs_integral_mul_norming_le {p : ℝ} (hp : 1 < p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) {C : ℝ}
    (hC : |∫ x, f x * (f x * ‖f x‖ ^ (p - 2)) ∂μ| ≤
      C * (eLpNorm (fun x => f x * ‖f x‖ ^ (p - 2)) (ENNReal.ofReal p.conjExponent) μ).toReal) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hqp : p.conjExponent * (p - 1) = p := by rw [mul_comm]; exact hpq.sub_one_mul_conj
  set ψ : α → ℝ := fun x => f x * ‖f x‖ ^ (p - 2) with hψ_def
  have hψ_norm : ∀ x, ‖‖f x‖ ^ (p - 1)‖ = ‖ψ x‖ := fun x => by
    simp only [ψ, Real.norm_eq_abs]
    rw [abs_mul_abs_rpow_sub_two hp (f x), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hψ_eLpNorm : eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
    rw [← eLpNorm_congr_norm_ae (Eventually.of_forall hψ_norm), eLpNorm_norm_rpow f hp1,
      ← ENNReal.ofReal_mul (by linarith [hpq.symm.lt]), hqp]
  have hint : ∫ x, f x * ψ x ∂μ = ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only [ψ, Real.norm_eq_abs]; exact mul_mul_abs_rpow_sub_two hp (f x))
  have hI : eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂μ) ^ p⁻¹) := by
    have h := hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  set I : ℝ := ∫ x, ‖f x‖ ^ p ∂μ with hI_def
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hfin : eLpNorm f (ENNReal.ofReal p) μ ≠ ⊤ := hf.2.ne
  set a : ℝ := (eLpNorm f (ENNReal.ofReal p) μ).toReal with ha_def
  have ha : a = I ^ p⁻¹ := by
    rw [ha_def, hI, ENNReal.toReal_ofReal (by positivity)]
  have haI : a ^ p = I := by
    rw [ha, ← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have key : a ^ p ≤ C * a ^ (p - 1) := by
    have h1 := hC
    rw [hint, abs_of_nonneg hI0, hψ_eLpNorm, ← ENNReal.toReal_rpow] at h1
    rw [haI]; exact h1
  rw [← ENNReal.ofReal_toReal hfin]
  rcases (ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal p) μ)).eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero]; exact bot_le
  · apply ENNReal.ofReal_le_ofReal
    rw [← ha_def] at hpos ⊢
    have hsplit : a ^ p = a * a ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add hpos, Real.rpow_one]
    rw [hsplit] at key
    exact le_of_mul_le_mul_right key (Real.rpow_pos_of_pos hpos _)

/-- **Norming** (public form of NonUniqueEuler `P/Infra/LpDual/WeakBounded.lean:58`): if
`|∫ f ψ| ≤ C ‖ψ‖_{p'}` for every `ψ ∈ L^{p'}`, then `‖f‖_p ≤ C`. -/
theorem eLpNorm_le_of_forall_abs_integral_mul_le {p : ℝ} (hp : 1 < p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) {C : ℝ}
    (hC : ∀ ψ : α → ℝ, MemLp ψ (ENNReal.ofReal p.conjExponent) μ →
      |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C :=
  eLpNorm_le_of_abs_integral_mul_norming_le hp hf (hC _ (memLp_norming hp hf))

/-- **Hölder** in `ℝ≥0∞`: `|∫ f g| ≤ ‖f‖_p ‖g‖_q` for a Hölder triple `(p, q, 1)`. No
integrability is assumed (if `f g` is not integrable the left side is `0`). -/
theorem ofReal_abs_integral_mul_le {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1] {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have h1 : ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  refine h1.trans ?_
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 1) hg hf
  rw [eLpNorm_one_eq_lintegral_enorm] at h2
  simpa [smul_eq_mul] using h2

end General

section Tests

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- Real-number form of the triangle inequality for `eLpNorm` (finite values). -/
private theorem toReal_eLpNorm_le_add {r : ℝ≥0∞} (hr : 1 ≤ r) {φ ψ : E → ℝ}
    (hφ : MemLp φ r μ) (hψ : MemLp ψ r μ) :
    (eLpNorm φ r μ).toReal ≤ (eLpNorm ψ r μ).toReal + (eLpNorm (φ - ψ) r μ).toReal := by
  have h : eLpNorm φ r μ ≤ eLpNorm ψ r μ + eLpNorm (φ - ψ) r μ := by
    have := eLpNorm_add_le hψ.1 (hφ.1.sub hψ.1) hr
    simpa using this
  rw [← ENNReal.toReal_add hψ.2.ne (hφ.sub hψ).2.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hψ.2.ne, (hφ.sub hψ).2.ne⟩) h

/-- Extension of a test-pairing bound by simultaneous approximation: if
`|∫ f φ| ≤ C ‖φ‖_{q}` for smooth compactly supported `φ`, and `f` pairs continuously with an
exponent `s` (Hölder `(s', s, 1)` with `f ∈ L^{s'}`), then the bound holds for every
`ψ ∈ L^{q} ∩ L^{s}`. -/
theorem abs_integral_mul_le_of_forall_test {q s s' : ℝ≥0∞} [ENNReal.HolderTriple s' s 1]
    (hq1 : 1 ≤ q) (hs1 : 1 ≤ s) (hq : q ≠ ⊤) (hs : s ≠ ⊤) {f : E → ℝ} (hf : MemLp f s' μ)
    {C : ℝ}
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      |∫ x, f x * φ x ∂μ| ≤ C * (eLpNorm φ q μ).toReal)
    {ψ : E → ℝ} (hψq : MemLp ψ q μ) (hψs : MemLp ψ s μ) :
    |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ q μ).toReal := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- choose δ with (|C| + ‖f‖) δ ≤ ε
  set Fn : ℝ := (eLpNorm f s' μ).toReal with hFn
  have hFn0 : 0 ≤ Fn := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (|C| + Fn + 1) with hδ
  have hden : 0 < |C| + Fn + 1 := by positivity
  have hδpos : 0 < δ := div_pos hε hden
  obtain ⟨φ, hφc, hφs, hφq, hφs'⟩ := exists_contDiff_eLpNorm_sub_le_two (μ := μ) hq1 hs1 hq hs
    hψq hψs (ENNReal.ofReal_pos.2 hδpos).ne'
  have hφmq : MemLp φ q μ := hφc.continuous.memLp_of_hasCompactSupport hφs
  have hφms : MemLp φ s μ := hφc.continuous.memLp_of_hasCompactSupport hφs
  -- the error term
  have herr : |∫ x, f x * (ψ - φ) x ∂μ| ≤ Fn * δ := by
    have h1 := ofReal_abs_integral_mul_le (μ := μ) (p := s') (q := s) hf.1 (hψs.1.sub hφms.1)
    have h2 : eLpNorm f s' μ * eLpNorm (ψ - φ) s μ ≤ ENNReal.ofReal (Fn * δ) := by
      rw [ENNReal.ofReal_mul hFn0, hFn, ENNReal.ofReal_toReal hf.2.ne]
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  have hint_f_φ : Integrable (fun x => f x * φ x) μ :=
    memLp_one_iff_integrable.1 (hφms.smul (p := s') (r := 1) hf)
  have hint_err : Integrable (fun x => f x * (ψ - φ) x) μ :=
    memLp_one_iff_integrable.1 ((hψs.sub hφms).smul (p := s') (r := 1) hf)
  have hsplit : ∫ x, f x * ψ x ∂μ = ∫ x, f x * φ x ∂μ + ∫ x, f x * (ψ - φ) x ∂μ := by
    rw [← integral_add hint_f_φ hint_err]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  -- the norm of the approximant
  have hnorm : |C * (eLpNorm φ q μ).toReal - C * (eLpNorm ψ q μ).toReal| ≤ |C| * δ := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hδ' : (eLpNorm (ψ - φ) q μ).toReal ≤ δ := by
      refine ENNReal.toReal_le_of_le_ofReal hδpos.le hφq
    have hφψ : (eLpNorm (φ - ψ) q μ).toReal ≤ δ := by
      rw [eLpNorm_sub_comm]; exact hδ'
    rw [abs_le]
    constructor
    · have := toReal_eLpNorm_le_add hq1 hψq hφmq
      linarith
    · have := toReal_eLpNorm_le_add hq1 hφmq hψq
      linarith
  have hmain := h φ hφc hφs
  calc |∫ x, f x * ψ x ∂μ|
      ≤ |∫ x, f x * φ x ∂μ| + |∫ x, f x * (ψ - φ) x ∂μ| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ C * (eLpNorm φ q μ).toReal + Fn * δ := add_le_add hmain herr
    _ ≤ C * (eLpNorm ψ q μ).toReal + |C| * δ + Fn * δ := by
        have := (abs_le.1 hnorm).2; linarith
    _ = C * (eLpNorm ψ q μ).toReal + (|C| + Fn) * δ := by ring
    _ ≤ C * (eLpNorm ψ q μ).toReal + ε := by
        have : (|C| + Fn) * δ ≤ ε := by
          rw [hδ, mul_div_assoc']
          rw [div_le_iff₀ hden]
          nlinarith [abs_nonneg C]
        linarith

/-- **T11 (INF01 §5, Level 1), scoping signature.** For `1 < p` and `f ∈ L^p`: if
`|∫ f ψ| ≤ C ‖ψ‖_{p'}` for every smooth compactly supported `ψ`, then `‖f‖_p ≤ C`. -/
theorem eLpNorm_le_of_forall_test_pairing {p : ℝ} (hp : 1 < p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) {C : ℝ}
    (h : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) :=
    hpq.ennrealOfReal
  have hq1 : 1 ≤ ENNReal.ofReal p.conjExponent := ENNReal.one_le_ofReal.2 hpq.symm.lt.le
  refine eLpNorm_le_of_forall_abs_integral_mul_le hp hf fun ψ hψ => ?_
  exact abs_integral_mul_le_of_forall_test (s' := ENNReal.ofReal p) hq1 hq1 ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hf h hψ hψ

/-- The truncation used in the `L²` form of T11. -/
private theorem norming_truncation {p : ℝ} (hp : 1 < p) {f : E → ℝ} (hfm : StronglyMeasurable f)
    {C : ℝ}
    (hext : ∀ ψ : E → ℝ, MemLp ψ (ENNReal.ofReal p.conjExponent) μ → MemLp ψ 2 μ →
      |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal)
    (n : ℕ) :
    eLpNorm ((closedBall (0 : E) n ∩ {x | |f x| ≤ n}).indicator f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C := by
  set S : Set E := closedBall (0 : E) n ∩ {x | |f x| ≤ n} with hS
  have hSm : MeasurableSet S :=
    measurableSet_closedBall.inter (measurableSet_le (continuous_abs.measurable.comp hfm.measurable) measurable_const)
  set fn : E → ℝ := S.indicator f with hfn
  have hfnm : StronglyMeasurable fn := hfm.indicator hSm
  have hp1 : 0 < p - 1 := by linarith
  -- domination by a bounded function with bounded support
  have hball : μ (closedBall (0 : E) n) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hdom : ∀ (c : ℝ) (r : ℝ≥0∞) (g : E → ℝ), AEStronglyMeasurable g μ →
      (∀ x, ‖g x‖ ≤ ‖(closedBall (0 : E) n).indicator (fun _ => c) x‖) → MemLp g r μ := by
    intro c r g hg hb
    exact (memLp_indicator_const r measurableSet_closedBall c (Or.inr hball)).mono hg
      (Eventually.of_forall hb)
  have hfn_bd : ∀ x, ‖fn x‖ ≤ ‖(closedBall (0 : E) n).indicator (fun _ => (n : ℝ)) x‖ := by
    intro x
    by_cases hx : x ∈ S
    · rw [hfn, indicator_of_mem hx, indicator_of_mem hx.1, Real.norm_eq_abs, Real.norm_eq_abs,
        Nat.abs_cast]
      exact hx.2
    · rw [hfn, indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  have hfnp : MemLp fn (ENNReal.ofReal p) μ := hdom _ _ _ hfnm.aestronglyMeasurable hfn_bd
  set ψ : E → ℝ := fun x => fn x * ‖fn x‖ ^ (p - 2) with hψ
  have hψm : AEStronglyMeasurable ψ μ :=
    hfnm.aestronglyMeasurable.mul
      ((hfnm.measurable.norm.pow_const _).aestronglyMeasurable)
  have hψ_bd : ∀ x, ‖ψ x‖ ≤
      ‖(closedBall (0 : E) n).indicator (fun _ => ((n : ℝ) ^ (p - 1))) x‖ := by
    intro x
    have habs : ‖ψ x‖ = |fn x| ^ (p - 1) := by
      simp only [ψ, Real.norm_eq_abs]; exact abs_mul_abs_rpow_sub_two hp (fn x)
    rw [habs]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx.1, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      have : |fn x| ≤ n := by rw [hfn, indicator_of_mem hx]; exact hx.2
      exact Real.rpow_le_rpow (abs_nonneg _) this hp1.le
    · rw [hfn, indicator_of_notMem hx, abs_zero, Real.zero_rpow hp1.ne']
      exact norm_nonneg _
  have hψ2 : MemLp ψ 2 μ := hdom _ _ _ hψm hψ_bd
  have hψq : MemLp ψ (ENNReal.ofReal p.conjExponent) μ := hdom _ _ _ hψm hψ_bd
  refine eLpNorm_le_of_abs_integral_mul_norming_le hp hfnp ?_
  have heq : ∫ x, fn x * (fn x * ‖fn x‖ ^ (p - 2)) ∂μ = ∫ x, f x * ψ x ∂μ := by
    congr 1; funext x
    by_cases hx : x ∈ S
    · simp [ψ, hfn, indicator_of_mem hx]
    · simp [ψ, hfn, indicator_of_notMem hx]
  rw [heq]
  exact hext ψ hψq hψ2

/-- **T11 (INF01 §5, Level 1), `L²` form.** For `1 < p` and `f ∈ L²` (not assumed in `L^p`):
if `|∫ f ψ| ≤ C ‖ψ‖_{p'}` for every smooth compactly supported `ψ`, then `‖f‖_p ≤ C`; in
particular `f ∈ L^p`. -/
theorem eLpNorm_le_of_forall_test_pairing_of_memLp_two {p : ℝ} (hp : 1 < p) {f : E → ℝ}
    (hf : MemLp f 2 μ) {C : ℝ}
    (h : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hq1 : 1 ≤ ENNReal.ofReal p.conjExponent := ENNReal.one_le_ofReal.2 hpq.symm.lt.le
  -- pass to a strongly measurable representative
  set g : E → ℝ := hf.1.mk f with hg
  have hfg : f =ᵐ[μ] g := hf.1.ae_eq_mk
  have hgm : StronglyMeasurable g := hf.1.stronglyMeasurable_mk
  have hg2 : MemLp g 2 μ := hf.ae_eq hfg
  have hpair : ∀ ψ : E → ℝ, ∫ x, f x * ψ x ∂μ = ∫ x, g x * ψ x ∂μ := fun ψ =>
    integral_congr_ae (hfg.mono fun x hx => by simp [hx])
  rw [eLpNorm_congr_ae hfg]
  have hextg : ∀ ψ : E → ℝ, MemLp ψ (ENNReal.ofReal p.conjExponent) μ → MemLp ψ 2 μ →
      |∫ x, g x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal := by
    intro ψ hψq hψ2
    have : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
    exact abs_integral_mul_le_of_forall_test (s' := 2) (s := 2) hq1 (by norm_num)
      ENNReal.ofReal_ne_top (by norm_num) hg2
      (fun φ hφc hφs => by rw [← hpair]; exact h φ hφc hφs) hψq hψ2
  -- truncations and Fatou
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n : ℕ => (closedBall (0 : E) n ∩ {x | |g x| ≤ n}).indicator g)
    (Eventually.of_forall fun n => norming_truncation hp hgm hextg n)
    (fun n => (hgm.indicator (measurableSet_closedBall.inter
      (measurableSet_le (continuous_abs.measurable.comp hgm.measurable) measurable_const))).aestronglyMeasurable)
    (Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop ⌈max ‖x‖ |g x|⌉₊] with n hn
  have hmax : max ‖x‖ |g x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hx : x ∈ closedBall (0 : E) n ∩ {x | |g x| ≤ n} :=
    ⟨by rw [mem_closedBall, dist_zero_right]; exact (le_max_left _ _).trans hmax,
      (le_max_right _ _).trans hmax⟩
  rw [indicator_of_mem hx]

end Tests

end UnforcedLeray.CZ
