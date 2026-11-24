import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1

/-!


If `W` represents `F ∈ Y_{q₀}` and `W` is pointwise real (`W x = realC (r x)`), then `F ∈ realSub`.
For a real phase test `φ`, `phasePair (realC ∘ φ) F = pairF (realC ∘ φ) W` (`pairF_rep_eq`,
`phasePair_eq_pairF_rep`), and the integrand `dotL (realC (φ x)) (realC (r x))` is the real number
`∑ i, φ x i * r x i`, so the period integral is real.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-- `x ↦ realC x` is smooth on `ℝ³` (copy of the private `contDiff_realC`). -/
theorem contDiff_realC_yr : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_piLp_apply (p := 2) (i := i))

/-- The complexified real test is a phase test. -/
theorem isPhaseTest_realC_yr {P : ℝ} (φ : ℝ × Space → Space) (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (fun x => realC (φ x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiff_realC_yr.comp hφ.smooth
  · intro τ y
    show realC (φ (τ + P, y)) = realC (φ (τ, y))
    rw [hφ.periodic τ y]
  · obtain ⟨R, hR⟩ := hφ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    show realC (φ (τ, y)) = 0
    rw [hR τ y hy]
    simp [realC]

/-- The pairing of a complexified real test with a complexified real field is real. -/
theorem pairF_realC_im_yr {P : ℝ} [Fact (0 < P)] (φ r : ℝ × Space → Space) :
    (pairF P (fun x => realC (φ x)) (fun x => realC (r x))).im = 0 := by
  have hinner : ∀ t : ℝ, (∫ y, dotL (realC (φ (t, y))) (realC (r (t, y)))) =
      ((∫ y, ∑ i : Fin 3, φ (t, y) i * r (t, y) i : ℝ) : ℂ) := by
    intro t
    rw [← integral_complex_ofReal]
    congr 1
    funext y
    simp [dotL_apply, realC_apply]
  unfold pairF phaseInt
  simp only [hinner]
  rw [integral_complex_ofReal]
  simp

/-- **Packaging leaf** (SP 2370-2383): a real pointwise representative lies in `realSub`. -/
theorem yqRealSymm : UnforcedLeray.Short.IIb.YqRealSymm := by
  intro P _ F W hW hreal
  rw [mem_realSub]
  intro φ hφ
  rw [phasePair_eq_pairF_rep (isPhaseTest_realC_yr φ hφ) F, pairF_rep_eq P F W hW]
  choose r hr using hreal
  have hWeq : W = fun x => realC (r x) := funext hr
  rw [hWeq]
  exact pairF_realC_im_yr φ r

end UnforcedLeray.Short.IIb
