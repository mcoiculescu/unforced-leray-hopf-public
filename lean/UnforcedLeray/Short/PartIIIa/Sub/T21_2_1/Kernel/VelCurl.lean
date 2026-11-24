import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2/9`: the curl clause of the kernel velocity

Source of record: `the November 2 reference manuscript` (SP), lines 2081-2084
(`K_d` is the cylindrical Biot-Savart kernel) and 3052-3057 (the adjoint and its duality).

Proof of `kerVelCurl_of`. Take the complex test field `F = (∂_η φ, -∂_q φ)` (real-valued,
cast to `ℂ`), which is integrable on the cell since `φ` and its derivatives are tests.
* `KerCurlPointwise` gives `kerAdj d F y = φ y` for every `y`.
* `KerAdjFubini` at the test `ψ` gives `∫ φ ψ = ∫ F · K_dψ`.
* The right side is the real integral `∫ (K_dψ)_q ∂_ηφ - (K_dψ)_η ∂_qφ`, and the left side is
  `∫ ψ φ`. Taking real parts (cast back from `ℂ`) gives `KerVelCurl`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerVelCurl_of (hF : UnforcedLeray.Short.IIIa.KerAdjFubini)
    (hP : UnforcedLeray.Short.IIIa.KerCurlPointwise) :
    UnforcedLeray.Short.IIIa.KerVelCurl := by
  intro d hd ψ hψ φ hφ
  let F : Fin 2 → ℝ × ℝ → ℂ :=
    ![fun x => ((B0579.pd 1 φ x : ℝ) : ℂ), fun x => ((-B0579.pd 0 φ x : ℝ) : ℂ)]
  have hF0 : ∀ x, F 0 x = ((B0579.pd 1 φ x : ℝ) : ℂ) := fun x => by simp [F]
  have hF1 : ∀ x, F 1 x = ((-B0579.pd 0 φ x : ℝ) : ℂ) := fun x => by simp [F]
  have hint0 : IntegrableOn (F 0) (B0579.cell d) := by
    have hfun : F 0 = fun x => ((B0579.pd 1 φ x : ℝ) : ℂ) := funext hF0
    rw [hfun]
    exact Integrable.ofReal (hφ.pd 1).integrableOn
  have hint1 : IntegrableOn (F 1) (B0579.cell d) := by
    have hfun : F 1 = fun x => ((-B0579.pd 0 φ x : ℝ) : ℂ) := funext hF1
    rw [hfun]
    exact Integrable.ofReal (hφ.pd 0).integrableOn.neg
  have hint : ∀ j, IntegrableOn (F j) (B0579.cell d) := Fin.forall_fin_two.2 ⟨hint0, hint1⟩
  -- the adjoint of `F` is `φ`
  have hA : ∀ y, kerAdj d F y = ((φ y : ℝ) : ℂ) := by
    intro y
    have h1 : ∀ x, ∑ j, F j x * ((kerD d (x - y) j : ℝ) : ℂ) =
        ((kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x : ℝ) : ℂ) := by
      intro x
      rw [Fin.sum_univ_two, hF0, hF1]
      push_cast
      ring
    unfold kerAdj
    simp only [h1]
    rw [integral_complex_ofReal, hP d hd φ hφ y]
  obtain ⟨_, hEq⟩ := hF d hd F hint ψ hψ
  simp only [hA] at hEq
  have h2 : ∀ x, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) =
      ((kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x : ℝ) : ℂ) := by
    intro x
    rw [Fin.sum_univ_two, hF0, hF1]
    push_cast
    ring
  have h3 : ∫ y in B0579.cell d, ((φ y : ℝ) : ℂ) * (ψ y : ℂ) =
      ((∫ y in B0579.cell d, ψ y * φ y : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext y
    push_cast
    ring
  have h4 : ∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) =
      ((∫ x in B0579.cell d,
        (kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    exact h2 x
  rw [h3, h4] at hEq
  exact Complex.ofReal_injective hEq

end UnforcedLeray.Short.IIIa
