import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackRealIdentity.AdjTest

/-!


Source `the November 2 reference manuscript`
lines 1431-1441 (reversed window).  Analogue of `WinBack.integrable_lambda_real`.  For
`D = Σ_i D2 c i i ∈ L^r` and the transported test `adjLapTest τ₀ a`
(`BackRealIdentity/AdjTest.lean`), `D · adjLapTest` is integrable (Hölder, compact support); the
reversed chart (`integrable_adjChart_iff`) turns this into integrability of
`e^{-5t/2} D(chart) φ(chart) = e^{-t} D(chart) a(τ₀ - t, y)`, and the flip `t ↦ -t` with the shift
`τ = τ₀ + t` gives `p ↦ adjWindowLap(p)_c a(p)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.Short.PartIIa.WinBack

theorem adjBackLambdaInt : AdjBackLambdaInt := by
  intro r _ hrt τ₀ ν c D2 hmem a ha hsup
  have hMemD : MemLp (fun X => ∑ i, D2 c i i X) r volume :=
    memLp_finsetSum Finset.univ fun i _ => hmem i
  have hφ : IsSTTest (adjLapTest τ₀ a : PS 3 → ℝ) := isSTTest_adjLapTest ha hsup
  have hf : Integrable (fun X => (∑ i, D2 c i i X) * ((adjLapTest τ₀ a X : ℝ) : ℂ)) :=
    integrable_of_memLp_mul hMemD (Complex.continuous_ofReal.comp hφ.continuous)
      (hφ.2.comp_left Complex.ofReal_zero)
  have hG : ∀ X : PS 3, 1 ≤ X.1 →
      (∑ i, D2 c i i X) * ((adjLapTest τ₀ a X : ℝ) : ℂ) = 0 := by
    intro X hX
    simp [adjLapTest_eq_zero τ₀ a hX]
  have h1 := (integrable_adjChart_iff _ hG).1 hf
  have h2 := h1.const_mul (ν : ℂ)
  have h3 : Integrable (fun q : ℝ × Space =>
      (fun p : ℝ × Space => adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
        ((a p : ℝ) : ℂ)) (τ₀ + (adjcNeg q).1, (adjcNeg q).2)) := by
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    exact (adjWindowLap_chart_eq (D := fun c X => ∑ i, D2 c i i X) hsup c q).symm
  have h4 := (adjcNeg_mp.integrable_comp_emb adjcNeg.measurableEmbedding
    (g := fun q : ℝ × Space => (fun p : ℝ × Space =>
      adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ))
        (τ₀ + q.1, q.2))).1 h3
  exact (integrable_shift_iff τ₀ (fun p : ℝ × Space => adjWindowLap ν τ₀
    (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ))).1 h4

end UnforcedLeray.Short.PartIIa
