import UnforcedLeray.Short.Interface.WindowSteps

/-!
# Interface I18: the weak Laplacian is unique on an open set (step G1)

Fundamental lemma of the calculus of variations on an open set `O ⊆ ℝ × ℝ³`, applied one
coordinate at a time. Mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`) is used with scalar values.

For a scalar test `g` supported in `O` and a coordinate `m`, the vector test
`ψ = g • e_m` is a similarity test with `tsupport ψ ⊆ O`. The pairing `laplacianPairing` for
`Λ₁` and `Λ₂` gives equal integrals of `g · (Λ₁)_m` and `g · (Λ₂)_m`, so the coordinate
`(Λ₁ - Λ₂)_m` vanishes almost everywhere on `O`.

Statement: `WeakLaplacianUnique` (`WindowSteps.lean`), with source `paper/main.tex`

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-- The pairing of `Λ` with the test `g • e_m` is `g` times the `m`-th component of `Λ`. -/
theorem weakLap_pairTerm_single (Λ : ℝ → SpatialField) (g : SpaceTime → ℝ) (m : Fin 3)
    (z : SpaceTime) :
    pairTerm Λ (fun y : SpaceTime => g y • EuclideanSpace.single m (1 : ℝ)) z =
      g z * Λ z.1 z.2 m := by
  simp [pairTerm, real_inner_smul_right, EuclideanSpace.inner_single_right]

/-- Step G1: two locally integrable weak Laplacians of `w` on an open set agree almost
everywhere there. -/
theorem weakLaplacianUnique : WeakLaplacianUnique := by
  intro w Λ₁ Λ₂ O hO hΛ₁ hΛ₂ h₁ h₂
  have hcomp : ∀ m : Fin 3, ∀ᵐ z ∂(volume : Measure SpaceTime),
      z ∈ O → (Λ₁ z.1 z.2 - Λ₂ z.1 z.2) m = 0 := by
    intro m
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun z : SpaceTime => (Λ₁ z.1 z.2 - Λ₂ z.1 z.2) m) ?_ ?_
    · exact ContinuousLinearMap.locallyIntegrableOn_comp
        (EuclideanSpace.proj (𝕜 := ℝ) m : Space →L[ℝ] ℝ) (hΛ₁.sub hΛ₂)
    · intro g hg hgc hgO
      have hcs : HasCompactSupport
          (fun y : SpaceTime => g y • EuclideanSpace.single m (1 : ℝ)) :=
        hgc.smul_right
      have hψt : IsSimilarityTest
          (fun y : SpaceTime => g y • EuclideanSpace.single m (1 : ℝ)) :=
        ⟨hg.smul contDiff_const, hcs⟩
      have hψO : tsupport (fun y : SpaceTime => g y • EuclideanSpace.single m (1 : ℝ)) ⊆ O :=
        (tsupport_smul_subset_left g (fun _ => EuclideanSpace.single m (1 : ℝ))).trans hgO
      have hA := h₁ _ hψt hψO
      have hB := h₂ _ hψt hψO
      unfold laplacianPairing at hA hB
      have hI1 : Integrable (fun z : SpaceTime => g z * Λ₁ z.1 z.2 m) volume :=
        hA.right_integrable.congr (ae_of_all _ fun z => weakLap_pairTerm_single Λ₁ g m z)
      have hI2 : Integrable (fun z : SpaceTime => g z * Λ₂ z.1 z.2 m) volume :=
        hB.right_integrable.congr (ae_of_all _ fun z => weakLap_pairTerm_single Λ₂ g m z)
      have hE : ∫ z : SpaceTime, g z * Λ₁ z.1 z.2 m ∂volume =
          ∫ z : SpaceTime, g z * Λ₂ z.1 z.2 m ∂volume := by
        have h12 := hA.eq.symm.trans hB.eq
        simpa only [weakLap_pairTerm_single] using h12
      have hsub : ∀ z : SpaceTime, g z * (Λ₁ z.1 z.2 - Λ₂ z.1 z.2) m =
          g z * Λ₁ z.1 z.2 m - g z * Λ₂ z.1 z.2 m := by
        intro z
        simp [mul_sub]
      simp only [smul_eq_mul, hsub]
      rw [integral_sub hI1 hI2, hE, sub_self]
  have hall : ∀ᵐ z ∂(volume : Measure SpaceTime), ∀ m : Fin 3,
      z ∈ O → (Λ₁ z.1 z.2 - Λ₂ z.1 z.2) m = 0 :=
    ae_all_iff.2 hcomp
  refine (ae_restrict_iff' hO.measurableSet).2 ?_
  filter_upwards [hall] with z hz hzO
  have h0 : Λ₁ z.1 z.2 - Λ₂ z.1 z.2 = 0 := by
    ext m
    simpa using hz m hzO
  exact sub_eq_zero.mp h0

end UnforcedLeray.Short.Interface
