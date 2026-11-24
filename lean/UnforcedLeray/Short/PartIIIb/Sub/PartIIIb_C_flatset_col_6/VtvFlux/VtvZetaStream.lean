import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpVanish
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvThetaFacts

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/7`: the cut-off stream function is a stream test

Target (`VtvFluxLemmas.lean`): `VtvZetaStream`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

`ζ_R(s,x) = Z(s,x) θ(x₂/R)` with `Z = vtvZp Φ R₀` and `θ = vtvTheta`.

* Smoothness: product of the jointly smooth `Z` (`VtvZpSmooth`) and the smooth `θ(x₂/R)`.
* Each slice is a cylinder test: periodic in `x₁` (`VtvZpVanish`), and vanishing for `|x₂| > max R₀ (2R)`
  (`θ(x₂/R) = 0` for `x₂/R ≥ 2`, and `Z = 0` for `x₂ < -R₀`).
* Support: `Z = 0` off the age band `[s₁,s₂]` (`VtvZpVanish`), and the band clause above.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvZetaStream`. `ζ_R = Z θ(·/R)` is a stream test for `R > 0`. -/
theorem vtvZetaStream : VtvZetaStream := by
  intro c Φ s₁ s₂ R₀ hS R hR
  have hΦ : IsFlatTest c Φ := hS.1
  have hs1 : 0 < s₁ := hS.2.1
  have hV := vtvZpVanish c Φ s₁ s₂ R₀ hS
  have hZ := vtvZpSmooth c Φ hΦ R₀
  -- joint smoothness of `ζ_R`
  have hDivR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => p.2.2 / R) :=
    (contDiff_snd.comp contDiff_snd).div_const R
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => vtvZeta Φ R₀ R p.1 p.2) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (ℝ × ℝ) => vtvZp Φ R₀ p.1 p.2 * vtvTheta (p.2.2 / R)) :=
      hZ.mul (vtvThetaFacts.1.comp hDivR)
    exact h1
  -- vanishing for `x₂ < -R₀` and for `|x₂| > max R₀ (2R)`
  have hband : ∀ s x, max R₀ (2 * R) < |x.2| → vtvZeta Φ R₀ R s x = 0 := by
    intro s x h
    show vtvZp Φ R₀ s x * vtvTheta (x.2 / R) = 0
    rcases lt_or_ge 0 x.2 with h0 | h0
    · rw [abs_of_pos h0] at h
      have h2 : 2 ≤ x.2 / R := (le_div_iff₀ hR).2 (by linarith [le_max_right R₀ (2 * R)])
      rw [vtvThetaFacts.2.2.1 _ h2, mul_zero]
    · rw [abs_of_nonpos h0] at h
      have h3 : x.2 < -R₀ := by linarith [le_max_left R₀ (2 * R)]
      rw [hV.2.2 s x h3, zero_mul]
  -- vanishing off the age band
  have hage : ∀ s x, (s < s₁ ∨ s₂ < s) → vtvZeta Φ R₀ R s x = 0 := by
    intro s x h
    show vtvZp Φ R₀ s x * vtvTheta (x.2 / R) = 0
    rw [hV.2.1 s x h, zero_mul]
  -- each slice is a cylinder test
  have hcyl : ∀ s, B0579.IsCylTest c (vtvZeta Φ R₀ R s) := by
    intro s
    refine ⟨?_, ?_, ?_⟩
    · have hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ => (s, y)) := by
        fun_prop
      exact hsm.comp hy
    · intro x
      unfold vtvZeta
      show vtvZp Φ R₀ s (x.1 + c, x.2) * vtvTheta (x.2 / R) = vtvZp Φ R₀ s x * vtvTheta (x.2 / R)
      rw [hV.1 s x]
    · exact ⟨max R₀ (2 * R), fun x hx => hband s x hx⟩
  unfold IsStreamTest
  refine ⟨hsm, hcyl, ⟨s₁, s₂, max R₀ (2 * R), hs1, ?_⟩⟩
  intro s x h
  rcases h with h | h | h
  · exact hage s x (Or.inl h)
  · exact hage s x (Or.inr h)
  · exact hband s x h

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
