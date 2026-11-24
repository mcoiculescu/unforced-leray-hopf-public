import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.LhsCont.Pair

/-!


Source: `the November 2 reference manuscript`,
lines 2074-2105 (approximation of a time-dependent test by separated sums).

Route: `cylTdLhs c t₀ t₁ f ω ψ = ∫_cell ω t₁ ψ t₁ - ∫_cell ω t₀ ψ t₀` (the initial datum is
`ω t₀` a.e. on the cell). For each age `r ∈ [t₀,t₁]`, the weight-`N = 0` part of `CylTdConv` gives
uniform convergence on the cell, and the weighted Cauchy-Schwarz bound of `Pair.lean` (with `memX`,
`m > 8`) gives convergence of `∫_cell ω r · φs n r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- One pairing converges under uniform convergence on the cell and an `L²` weight `ω`. -/
theorem cylLhs_tendsto_pair {m : ℝ} (hm : 8 < m) {c : ℝ} (hc : 0 < c)
    (ω : B0579.Plane → ℝ) (hω : MemLp ω 2 (B0579.cellMeasure c m))
    (ψs : ℕ → B0579.Plane → ℝ) (ψ : B0579.Plane → ℝ)
    (hsc : ∀ n, Continuous (ψs n)) (hsm : ∀ n, MemLp (ψs n) 2 (B0579.cellMeasure c (-m)))
    (hψc : Continuous ψ) (hψm : MemLp ψ 2 (B0579.cellMeasure c (-m)))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x ∈ B0579.cell c, |ψs n x - ψ x| ≤ ε) :
    Tendsto (fun n => ∫ x in B0579.cell c, ω x * ψs n x) atTop
      (𝓝 (∫ x in B0579.cell c, ω x * ψ x)) := by
  have hm1 : (1 : ℝ) < m := by linarith
  have hK : 0 ≤ cylLhsK c m := ENNReal.toReal_nonneg
  have hN : 0 ≤ (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal := ENNReal.toReal_nonneg
  have hpos : 0 < cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1 := by
    linarith [mul_nonneg hK hN]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1) :=
    div_pos hε hpos
  obtain ⟨n₀, hn₀⟩ := hconv _ hδ
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hint : (∫ x in B0579.cell c, ω x * ψs n x) - ∫ x in B0579.cell c, ω x * ψ x
      = ∫ x in B0579.cell c, ω x * (ψs n x - ψ x) := by
    rw [← integral_sub (cylLhs_integrableOn ω (ψs n) hω (hsm n))
      (cylLhs_integrableOn ω ψ hω hψm)]
    congr 1
    funext x
    ring
  have hb := cylLhs_pair hm1 hc ω (fun x => ψs n x - ψ x)
    (ε / (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1))
    hω ((hsc n).sub hψc).aestronglyMeasurable (fun x hx => hn₀ n hn x hx)
  have hlt : cylLhsK c m * (ε / (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1))
      * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal < ε := by
    have heq : cylLhsK c m * (ε / (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1))
        * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal
        = (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal) * ε /
          (cylLhsK c m * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal + 1) := by ring
    rw [heq, div_lt_iff₀ hpos]
    nlinarith
  rw [Real.dist_eq, hint]
  exact lt_of_le_of_lt hb hlt

set_option maxHeartbeats 1600000 in
theorem cylTdLhsCont : UnforcedLeray.Short.IIb.CylTdLhsCont := by
  intro m hm ν c tr t₀ f ω hc hfl t₁ φ φs ht hφ hs hconv
  have hm1 : (1 : ℝ) < m := by linarith
  have hL : ∀ ψ : ℝ → B0579.Plane → ℝ, cylTdLhs c t₀ t₁ f ω ψ =
      (∫ x in B0579.cell c, ω t₁ x * ψ t₁ x) - ∫ x in B0579.cell c, ω t₀ x * ψ t₀ x := by
    intro ψ
    have hI : (∫ x in B0579.cell c, f x * ψ t₀ x) = ∫ x in B0579.cell c, ω t₀ x * ψ t₀ x := by
      refine integral_congr_ae ?_
      filter_upwards [hfl.initial] with x hx
      simp only [hx]
    unfold cylTdLhs
    rw [hI]
  have key : ∀ r ∈ Icc t₀ t₁, Tendsto (fun n => ∫ x in B0579.cell c, ω r x * φs n r x) atTop
      (𝓝 (∫ x in B0579.cell c, ω r x * φ r x)) := by
    intro r hr
    have hsc : ∀ n, Continuous (fun x => φs n r x) := by
      intro n
      obtain ⟨k, χ, ψ, -, hψ, hrep⟩ := hs n
      have hfun : (fun x => φs n r x) = fun x => ∑ i : Fin k, χ i r * ψ i x :=
        funext fun x => hrep r x
      rw [hfun]
      exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψ i).continuous
    have hsm : ∀ n, MemLp (fun x => φs n r x) 2 (B0579.cellMeasure c (-m)) := by
      intro n
      obtain ⟨k, χ, ψ, -, hψ, hrep⟩ := hs n
      have hfun : (fun x => φs n r x) = fun x => ∑ i : Fin k, χ i r * ψ i x :=
        funext fun x => hrep r x
      rw [hfun]
      exact memLp_finsetSum _ fun i _ => ((hψ i).memLp (-m)).const_mul (χ i r)
    have hφc : Continuous (fun x => φ r x) := by
      have h1 : ContinuousOn (fun z : ℝ × B0579.Plane => φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ) :=
        hφ.smooth.continuousOn
      have hcont : ContinuousOn (fun x : B0579.Plane => ((r, x) : ℝ × B0579.Plane)) univ :=
        (continuous_const.prodMk continuous_id).continuousOn
      have h2 : ContinuousOn (fun x : B0579.Plane => φ r x) univ :=
        h1.comp hcont (fun x _ => (⟨hr, mem_univ _⟩ : (r, x) ∈ Icc t₀ t₁ ×ˢ univ))
      exact continuousOn_univ.1 h2
    obtain ⟨C, hC⟩ := hφ.decay 0
    have hφbd : ∀ x, |φ r x| ≤ C := by
      intro x
      have h := hC r hr x
      simp only [Real.rpow_zero, mul_one] at h
      linarith [abs_nonneg (B0579.pd 0 (φ r) x), abs_nonneg (B0579.pd 1 (φ r) x),
        abs_nonneg (lapP (φ r) x)]
    have hφm : MemLp (fun x => φ r x) 2 (B0579.cellMeasure c (-m)) :=
      cylLhs_memLp_neg hm1 c hφc hφbd
    have hωr : MemLp (ω r) 2 (B0579.cellMeasure c m) := hfl.memX r hr.1
    refine cylLhs_tendsto_pair hm hc (ω r) hωr (fun n => φs n r) (φ r) hsc hsm hφc hφm ?_
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hconv 0 ε hε
    refine ⟨n₀, fun n hn x hx => ?_⟩
    have h := (hn₀ n hn).1 r hr x
    simp only [Real.rpow_zero, mul_one] at h
    show |φs n r x - φ r x| ≤ ε
    linarith [abs_nonneg (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x),
      abs_nonneg (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x),
      abs_nonneg (lapP (φs n r) x - lapP (φ r) x)]
  simp only [hL]
  exact (key t₁ ⟨ht, le_rfl⟩).sub (key t₀ ⟨le_rfl, ht⟩)

end UnforcedLeray.Short.IIb
