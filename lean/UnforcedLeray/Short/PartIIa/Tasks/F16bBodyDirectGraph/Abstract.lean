import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.RealDeriv

/-!


A unitary group `U t` on a Hilbert space with a dense set `S` of vectors that is `U`-invariant and
on which `t ↦ U t Ψ` is differentiable at `0` with derivative `D Ψ` (commuting with `U`), and a
vector `w` weakly differentiable against `S` (`⟪D Ψ, w⟫ = -⟪Ψ, y⟫`), has strong derivative `y`:
`t⁻¹ (U t w - w) → y`.  Proof: scalar FTC for `t ↦ ⟪U t Ψ, w⟫`, exchange of the interval integral
with the inner product, density, and continuity of `s ↦ U (-s) y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.F16b

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem generator_of_weak
    (U : ℝ → H →ₗᵢ[ℂ] H)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x)) (hzero : ∀ x, U 0 x = x)
    {ι : Type*} (e Dι : ι → H) (hS : Dense (range e))
    (hinvar : ∀ i t, ∃ j, e j = U t (e i) ∧ Dι j = U t (Dι i))
    (hder : ∀ i, Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (U h (e i) - e i)) (𝓝[≠] 0) (𝓝 (Dι i)))
    (w y : H) (hweak : ∀ i, ⟪Dι i, w⟫_ℂ = -⟪e i, y⟫_ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (U t w - w)) (𝓝[≠] 0) (𝓝 y) := by
  -- strong continuity at 0 on `S`
  have hcontS : ∀ i, Tendsto (fun h : ℝ => U h (e i)) (𝓝 0) (𝓝 (e i)) := by
    intro i
    set Ψ := e i with hΨdef
    have h1 := hder i
    have h2 : Tendsto (fun h : ℝ => (h : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => (h : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have h3 := h2.smul h1
    simp only [zero_smul] at h3
    have h4 : Tendsto (fun h : ℝ => U h Ψ - Ψ) (𝓝[≠] 0) (𝓝 0) := by
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      rw [smul_smul, mul_inv_cancel₀ hh', one_smul]
    have h5 : Tendsto (fun h : ℝ => U h Ψ) (𝓝[≠] 0) (𝓝 Ψ) := by
      simpa using h4.add_const Ψ
    have h6 : Tendsto (fun h : ℝ => U h Ψ) (pure 0) (𝓝 Ψ) := by
      rw [tendsto_pure_left]
      intro s hs
      rw [hzero]
      exact mem_of_mem_nhds hs
    rw [← nhdsNE_sup_pure]
    exact h5.sup h6
  -- strong continuity at 0 everywhere
  have hcont0 : ∀ x, Tendsto (fun h : ℝ => U h x) (𝓝 0) (𝓝 x) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Ψ, hxΨ, i, hi⟩ := Metric.dense_iff.1 hS x (ε / 3) (by positivity)
    have hxΨ' : ‖Ψ - x‖ < ε / 3 := by
      have := Metric.mem_ball.1 hxΨ
      rwa [dist_eq_norm] at this
    have := (Metric.tendsto_nhds.1 (hcontS i)) (ε / 3) (by positivity)
    rw [hi] at this
    filter_upwards [this] with h hh
    rw [dist_eq_norm] at hh ⊢
    have e : U h x - x = U h (x - Ψ) + (U h Ψ - Ψ) + (Ψ - x) := by
      rw [map_sub]; abel
    rw [e]
    calc ‖U h (x - Ψ) + (U h Ψ - Ψ) + (Ψ - x)‖
        ≤ ‖U h (x - Ψ)‖ + ‖U h Ψ - Ψ‖ + ‖Ψ - x‖ := norm_add₃_le
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [LinearIsometry.norm_map, norm_sub_rev x Ψ]
          linarith
      _ = ε := by ring
  have hcont : ∀ x, Continuous fun t : ℝ => U t x := by
    intro x
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : Tendsto (fun t' : ℝ => t' - t) (𝓝 t) (𝓝 0) := by
      have hc : Continuous (fun t' : ℝ => t' - t) := by fun_prop
      simpa using hc.tendsto t
    have h2 := (hcont0 (U t x)).comp h1
    have h3 : (fun h : ℝ => U h (U t x)) ∘ (fun t' : ℝ => t' - t) = fun t' => U t' x := by
      funext t'
      simp only [Function.comp_apply]
      rw [← hadd]; congr 1; ring
    rw [h3] at h2
    exact h2
  -- derivative of `t ↦ ⟪U t Ψ, w⟫`
  have hderiv : ∀ i, ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => ⟪U t (e i), w⟫_ℂ) (-⟪U t (e i), y⟫_ℂ) t := by
    intro i t
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h1 := hder i
    have hc : Continuous fun v : H => ⟪U t v, w⟫_ℂ :=
      (continuous_inner.comp ((U t).continuous.prodMk continuous_const))
    have h2 := (hc.tendsto (Dι i)).comp h1
    have h3 : ⟪U t (Dι i), w⟫_ℂ = -⟪U t (e i), y⟫_ℂ := by
      obtain ⟨j, hj1, hj2⟩ := hinvar i t
      have := hweak j
      rwa [hj2, hj1] at this
    rw [h3] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    simp only [Function.comp_apply]
    have hee : U t (U h (e i)) - U t (e i) = U t (U h (e i) - (e i)) := by rw [map_sub]
    rw [Complex.real_smul, ← inner_sub_left, hadd t h, hee, map_smul, inner_smul_left]
    simp [Complex.conj_ofReal]
  have hinv : ∀ (s : ℝ) (x : H), U s (U (-s) x) = x := by
    intro s x
    rw [← hadd, add_neg_cancel, hzero]
  have hinner : ∀ (s : ℝ) (Ψ x : H), ⟪U s Ψ, x⟫_ℂ = ⟪Ψ, U (-s) x⟫_ℂ := by
    intro s Ψ x
    conv_lhs => rw [← hinv s x]
    exact (U s).inner_map_map Ψ (U (-s) x)
  have hI : ∀ t : ℝ, U (-t) w - w + ∫ s in (0 : ℝ)..t, U (-s) y = 0 := by
    intro t
    have hc : Continuous fun s : ℝ => U (-s) y := (hcont y).comp continuous_neg
    have hint : IntervalIntegrable (fun s : ℝ => U (-s) y) MeasureTheory.volume 0 t :=
      hc.intervalIntegrable _ _
    set z := U (-t) w - w + ∫ s in (0 : ℝ)..t, U (-s) y with hz
    have hort : ∀ i, ⟪e i, z⟫_ℂ = 0 := by
      intro i
      have hf : IntervalIntegrable (fun s : ℝ => -⟪U s (e i), y⟫_ℂ) MeasureTheory.volume 0 t :=
        (continuous_neg.comp (continuous_inner.comp
          ((hcont (e i)).prodMk continuous_const))).intervalIntegrable _ _
      have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
        (f := fun t : ℝ => ⟪U t (e i), w⟫_ℂ) (f' := fun s => -⟪U s (e i), y⟫_ℂ)
        (fun s _ => hderiv i s) hf
      rw [intervalIntegral.integral_neg] at hF
      have hcomm := (innerSL ℂ (e i)).intervalIntegral_comp_comm hint
      simp only [innerSL_apply_apply] at hcomm
      simp only [hinner _ (e i), hzero, neg_zero] at hF
      rw [hz, inner_add_right, inner_sub_right, ← hcomm]
      linear_combination -hF
    have hcl : IsClosed {v : H | ⟪v, z⟫_ℂ = 0} :=
      isClosed_eq (continuous_inner.comp (continuous_id.prodMk continuous_const)) continuous_const
    have hsub : range e ⊆ {v : H | ⟪v, z⟫_ℂ = 0} := by
      rintro _ ⟨i, rfl⟩; exact hort i
    have hz0 : ⟪z, z⟫_ℂ = 0 := by
      have := closure_minimal hsub hcl
      rw [hS.closure_eq] at this
      exact this (mem_univ z)
    exact inner_self_eq_zero.1 hz0
  have hIcont : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, U (-s) y) (U (-0) y) 0 := by
    have hc : Continuous fun s : ℝ => U (-s) y := (hcont y).comp continuous_neg
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hIcont
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have h3 := hslope.comp hneg
  simp only [neg_zero, hzero, zero_add, intervalIntegral.integral_same, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have e := hI (-t)
  rw [neg_neg] at e
  have e' : U t w - w = -∫ s in (0 : ℝ)..(-t), U (-s) y := by
    rw [eq_neg_iff_add_eq_zero]; exact e
  simp only [Function.comp_apply]
  rw [e', RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  rw [inv_neg, neg_smul, smul_neg]
  simp only [neg_inj]
  rfl

end UnforcedLeray.Short.PartIIa.F16b
