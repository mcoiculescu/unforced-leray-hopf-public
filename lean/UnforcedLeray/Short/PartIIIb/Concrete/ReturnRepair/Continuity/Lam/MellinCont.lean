import UnforcedLeray.Blueprint.Construction.Planar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# Continuity of the planar Mellin function `𝒥` on `(-3/2, ∞)` (source 4703, 5919)

Dominated convergence: `𝒥(μ) = ∫₀^∞ θ^{μ+1/2} 𝔐(V_can(θ)) dθ`, and for `μ ∈ [a, b] ⊂ (-3/2, ∞)`,
`θ^{μ+1/2} ≤ θ^{a+1/2} + θ^{b+1/2}`, both integrable against `𝔐(V_can)` by `mellin_integrable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar

theorem rpow_le_add_of_mem {θ a b x : ℝ} (hθ : 0 < θ) (ha : a ≤ x) (hb : x ≤ b) :
    θ ^ x ≤ θ ^ a + θ ^ b := by
  have h1 : 0 ≤ θ ^ a := Real.rpow_nonneg hθ.le _
  have h2 : 0 ≤ θ ^ b := Real.rpow_nonneg hθ.le _
  rcases le_total θ 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hθ h ha
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hb
    linarith

theorem planar_continuousAt_mellinJ {P : PlanarData} (hP : IsPlanarReference P) {μ0 : ℝ}
    (h : -(3 / 2) < μ0) : ContinuousAt P.mellinJ μ0 := by
  set δ : ℝ := (μ0 + 3 / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set G : ℝ → ℝ → ℂ := fun μ θ => ((θ ^ (μ + 1 / 2) : ℝ) : ℂ) * quadrupole (P.canonical θ)
    with hG
  have hint : ∀ μ, -(3 / 2) < μ → Integrable (G μ) (volume.restrict (Ioi 0)) := fun μ hμ =>
    hP.mellin_integrable μ hμ
  have hlow : -(3 / 2) < μ0 - δ := by rw [hδ]; linarith
  have hbd : Integrable (fun θ => ‖G (μ0 - δ) θ‖ + ‖G (μ0 + δ) θ‖)
      (volume.restrict (Ioi 0)) :=
    (hint _ hlow).norm.add (hint _ (by linarith)).norm
  have hnear : ∀ᶠ μ in 𝓝 μ0, μ ∈ Ioo (μ0 - δ) (μ0 + δ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have key : ContinuousAt (fun μ => ∫ θ in Ioi (0 : ℝ), G μ θ) μ0 := by
    refine continuousAt_of_dominated (bound := fun θ => ‖G (μ0 - δ) θ‖ + ‖G (μ0 + δ) θ‖)
      ?_ ?_ hbd ?_
    · filter_upwards [hnear] with μ hμ
      exact (hint μ (by linarith [hμ.1])).aestronglyMeasurable
    · filter_upwards [hnear] with μ hμ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      have hθ' : 0 < θ := hθ
      have e : ∀ x : ℝ, ‖G x θ‖ = θ ^ (x + 1 / 2) * ‖quadrupole (P.canonical θ)‖ := by
        intro x
        simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.rpow_nonneg hθ'.le _)]
      rw [e, e, e]
      have := rpow_le_add_of_mem hθ' (a := μ0 - δ + 1 / 2) (b := μ0 + δ + 1 / 2)
        (x := μ + 1 / 2) (by linarith [hμ.1]) (by linarith [hμ.2])
      nlinarith [norm_nonneg (quadrupole (P.canonical θ))]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      have hθ' : 0 < θ := hθ
      have hc : ContinuousAt (fun μ : ℝ => θ ^ (μ + 1 / 2)) μ0 :=
        continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inl hθ'.ne')
      exact (Complex.continuous_ofReal.continuousAt.comp hc).mul continuousAt_const
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
