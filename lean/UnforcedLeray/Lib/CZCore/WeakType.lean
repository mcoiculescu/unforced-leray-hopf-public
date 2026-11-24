import UnforcedLeray.Lib.CZCore.Density
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Weak type (1,1) and its density extension (INF01 T6)


target T6; decision D4 of `scoping/README.md` §3 ("weak (1,1) by density"); critic §4.9 ("the
weak (1,1) bound passes to `L¹ ∩ L²` through convergence in measure").

* `HasWeakType11 μ T A`: for every `f ∈ L² ∩ L¹` and `t > 0`,
  `t · μ{|T f| > t} ≤ A ‖f‖₁`. The operator is a bounded operator on `L²`; the weak bound is
  asked only on `L¹ ∩ L²`.
* `hasWeakType11_of_dense`: on a finite-dimensional space with a Haar measure, the weak bound
  on continuous compactly supported functions implies `HasWeakType11`. Proof: for `s > t`,
  approximate `f` in `L¹` and `L²` at once (`exists_continuous_eLpNorm_sub_le_two`), split
  `{|Tf| > s} ⊆ {|Tg| > t} ∪ {|T(f-g)| ≥ s - t}`, bound the second set by Chebyshev in `L²`,
  let the error go to `0`, then let `s ↓ t`.

Also two small tools reused by T7 and T10: `ofReal_rpow_two_mul_meas_le` (Chebyshev in `L²`
with real thresholds) and `eLpNorm_apply_le` (operator bound in `eLpNorm` form).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

section General

variable {α : Type*} [MeasurableSpace α]

/-- **T6 (INF01 §5, Level 1).** Weak type `(1,1)` for a bounded operator on `L²(μ)`: for every
`f ∈ L² ∩ L¹` and every `t > 0`, `t · μ{x | t < |T f x|} ≤ A ‖f‖_{L¹}`. -/
def HasWeakType11 (μ : Measure α) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (A : ℝ≥0) : Prop :=
  ∀ f : Lp ℝ 2 μ, MemLp f 1 μ → ∀ t : ℝ, 0 < t →
    ENNReal.ofReal t * μ {x | t < |T f x|} ≤ A * eLpNorm f 1 μ

variable {μ : Measure α}

/-- Chebyshev in `L²` with a real threshold. -/
theorem ofReal_rpow_two_mul_meas_le {H : α → ℝ} (hH : AEStronglyMeasurable H μ) (η : ℝ) :
    ENNReal.ofReal η ^ (2 : ℝ) * μ {x | η ≤ |H x|} ≤ eLpNorm H 2 μ ^ (2 : ℝ) := by
  have h := mul_meas_ge_le_pow_eLpNorm' μ (p := 2) (by norm_num) (by norm_num) hH
    (ENNReal.ofReal η)
  have hset : {x | ENNReal.ofReal η ≤ ‖H x‖ₑ} = {x | η ≤ |H x|} := by
    ext x
    simp only [mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  rw [hset] at h
  simpa using h

/-- Operator bound in `eLpNorm` form. -/
theorem eLpNorm_apply_le (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (u : Lp ℝ 2 μ) :
    eLpNorm (T u) 2 μ ≤ ‖T‖₊ * eLpNorm u 2 μ := by
  rw [← Lp.enorm_def, ← Lp.enorm_def, enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact_mod_cast T.le_opNNNorm u

/-- Pointwise splitting of a level set: if `s = t + η` and `|F| ≤ |G| + |H|`, then
`s < |F|` forces `t < |G|` or `η ≤ |H|`. -/
theorem lt_abs_or_le_abs_of_le {F G H t η : ℝ} (hF : |F| ≤ |G| + |H|) (h : t + η < |F|) :
    t < |G| ∨ η ≤ |H| := by
  by_contra hc
  push Not at hc
  linarith [hc.1, hc.2]

end General

section Dense

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The density step at a fixed level `s > t`. -/
private theorem weak_bound_of_dense_lt {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {A : ℝ≥0}
    (h : ∀ g : E → ℝ, ∀ hg : MemLp g 2 μ, Continuous g → HasCompactSupport g →
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < |T (hg.toLp g) x|} ≤ A * eLpNorm g 1 μ)
    (f : Lp ℝ 2 μ) (hf1 : MemLp f 1 μ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ENNReal.ofReal t * μ {x | t + η < |T f x|} ≤ A * eLpNorm f 1 μ := by
  set c : ℝ≥0∞ := ENNReal.ofReal t * (ENNReal.ofReal η ^ (2 : ℝ))⁻¹ * (‖T‖₊ : ℝ≥0∞) ^ (2 : ℝ)
    with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) ?_
    · rw [ENNReal.inv_ne_top]
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη) ENNReal.ofReal_ne_top).ne'
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top
  have hf1' : eLpNorm f 1 μ ≠ ⊤ := hf1.2.ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- choose the approximation error δ
  have hlim : Tendsto (fun δ : ℝ => (A : ℝ≥0∞) * ENNReal.ofReal δ + c * ENNReal.ofReal δ ^ (2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((A : ℝ≥0∞) * 0 + c * 0 ^ (2 : ℝ))) := by
    have h0 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact (ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.coe_ne_top)).add
      (ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const.tendsto 0).comp h0)
        (Or.inr hcfin))
  rw [mul_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero, add_zero] at hlim
  obtain ⟨δ, hδε, hδpos⟩ := ((hlim.eventually (ge_mem_nhds
    (by exact_mod_cast hε : (0 : ℝ≥0∞) < ε))).and self_mem_nhdsWithin).exists
  have hδpos' : (0 : ℝ) < δ := hδpos
  -- the approximant
  obtain ⟨g, hgc, hgs, hg1, hg2⟩ := exists_continuous_eLpNorm_sub_le_two (μ := μ) le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.one_ne_top (by norm_num) hf1 (Lp.memLp f)
    (ENNReal.ofReal_pos.2 hδpos').ne'
  have hg2m : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport hgs
  have hg1m : MemLp g 1 μ := hgc.memLp_of_hasCompactSupport hgs
  set G : Lp ℝ 2 μ := hg2m.toLp g
  set u : Lp ℝ 2 μ := f - G
  -- a.e. splitting
  have hsplit : ∀ᵐ x ∂μ, |T f x| ≤ |T G x| + |T u x| := by
    have hTu : (T u : E → ℝ) =ᵐ[μ] (T f : E → ℝ) - T G := by
      rw [show T u = T f - T G by simp [u, map_sub]]
      exact Lp.coeFn_sub _ _
    filter_upwards [hTu] with x hx
    have : T u x = T f x - T G x := by rw [hx, Pi.sub_apply]
    calc |T f x| = |T G x + T u x| := by rw [this]; congr 1; ring
      _ ≤ |T G x| + |T u x| := abs_add_le _ _
  have hmeas : μ {x | t + η < |T f x|} ≤ μ {x | t < |T G x|} + μ {x | η ≤ |T u x|} := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hsplit] with x hx hxs
    exact lt_abs_or_le_abs_of_le hx hxs
  -- the two pieces
  have hgood : ENNReal.ofReal t * μ {x | t < |T G x|} ≤ A * (eLpNorm f 1 μ + ENNReal.ofReal δ) := by
    refine (h g hg2m hgc hgs t ht).trans ?_
    gcongr
    calc eLpNorm g 1 μ = eLpNorm ((f : E → ℝ) - ((f : E → ℝ) - g)) 1 μ := by
          rw [sub_sub_cancel]
      _ ≤ eLpNorm f 1 μ + eLpNorm ((f : E → ℝ) - g) 1 μ :=
          eLpNorm_sub_le hf1.1 (hf1.1.sub hgc.aestronglyMeasurable) le_rfl
      _ ≤ eLpNorm f 1 μ + ENNReal.ofReal δ := by gcongr
  have hu2 : eLpNorm u 2 μ ≤ ENNReal.ofReal δ := by
    have : (u : E → ℝ) =ᵐ[μ] (f : E → ℝ) - g := by
      filter_upwards [Lp.coeFn_sub f G, hg2m.coeFn_toLp] with x hx hx'
      rw [hx, Pi.sub_apply, Pi.sub_apply, hx']
    rw [eLpNorm_congr_ae this]; exact hg2
  have hbad : μ {x | η ≤ |T u x|} ≤
      (ENNReal.ofReal η ^ (2 : ℝ))⁻¹ * ((‖T‖₊ : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2 : ℝ) := by
    have hcheb := ofReal_rpow_two_mul_meas_le (μ := μ) (Lp.aestronglyMeasurable (T u)) η
    have hpos : ENNReal.ofReal η ^ (2 : ℝ) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη) ENNReal.ofReal_ne_top).ne'
    have hfin : ENNReal.ofReal η ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    rw [← ENNReal.mul_le_iff_le_inv hpos hfin]
    refine hcheb.trans ?_
    gcongr
    exact (eLpNorm_apply_le T u).trans (by gcongr)
  calc ENNReal.ofReal t * μ {x | t + η < |T f x|}
      ≤ ENNReal.ofReal t * (μ {x | t < |T G x|} + μ {x | η ≤ |T u x|}) := by gcongr
    _ = ENNReal.ofReal t * μ {x | t < |T G x|} + ENNReal.ofReal t * μ {x | η ≤ |T u x|} :=
        mul_add _ _ _
    _ ≤ A * (eLpNorm f 1 μ + ENNReal.ofReal δ) + ENNReal.ofReal t *
          ((ENNReal.ofReal η ^ (2 : ℝ))⁻¹ * ((‖T‖₊ : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2 : ℝ)) := by
        gcongr
    _ = A * eLpNorm f 1 μ + ((A : ℝ≥0∞) * ENNReal.ofReal δ + c * ENNReal.ofReal δ ^ (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hc]
        ring
    _ ≤ A * eLpNorm f 1 μ + ε := by gcongr

/-- **T6 (INF01 §5, Level 1), density extension.** On a finite-dimensional space with a Haar
measure, the weak `(1,1)` bound for continuous compactly supported functions implies
`HasWeakType11`. -/
theorem hasWeakType11_of_dense {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {A : ℝ≥0}
    (h : ∀ g : E → ℝ, ∀ hg : MemLp g 2 μ, Continuous g → HasCompactSupport g →
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < |T (hg.toLp g) x|} ≤ A * eLpNorm g 1 μ) :
    HasWeakType11 μ T A := by
  intro f hf1 t ht
  have hU : {x | t < |T f x|} = ⋃ n : ℕ, {x | t + 1 / ((n : ℝ) + 1) < |T f x|} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ => {x | t + 1 / ((n : ℝ) + 1) < |T f x|} := by
    intro m n hmn x hx
    simp only [mem_ofPred_eq] at hx ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n => weak_bound_of_dense_lt h f hf1 ht (by positivity)

end Dense

end UnforcedLeray.CZ
