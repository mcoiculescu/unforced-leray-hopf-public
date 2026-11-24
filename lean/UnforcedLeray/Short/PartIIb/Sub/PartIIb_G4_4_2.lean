import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4

/-!
# `PartII-b:G4/4/2` (`LerayForceProj`): reduction to the phase-space Leray operator

Source: `the November 2 reference manuscript` (SP) line 2383 (`𝔓` is bounded on
`Y_p` and commutes with `∂_j`), with the definition of `𝔓 = I + R ⊗ R` on `L^p(ℝ³)` applied for
each phase (SP 2370-2383).

`LerayYq` is the single true analytic fact: slicewise (phase by phase) Leray projection `𝔓` on
`Y_{q₀} = L^{q₀}(ℝ/Pℤ; L^{q₀}(ℝ³; ℂ³))` as a bounded `ℂ`-linear operator, with constant
independent of the period `P`, with range in `Y_σ`, invisible on solenoidal phase tests, preserving
the real and the `𝒪`-invariant elements, and commuting with weak spatial gradients.
`lerayForceProj_of` derives `LerayForceProj` from it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **The phase-space Leray projection** (SP 2383, the `ℂ³`-valued `𝔓` of SP 2370-2383 applied for
each phase): a bounded `ℂ`-linear `T` on `Y_{q₀}`, `‖T‖ ≤ Cl` (`Cl` independent of `P`), with
`T F ∈ Y_σ`, `⟪Φ, T F⟫ = ⟪Φ, F⟫` for solenoidal phase tests `Φ`, `T` preserving `realSub` and
`Osym`, and `T` commuting with weak spatial gradients given pointwise by `HasPtwOp`. -/
def LerayYq : Prop :=
  ∃ Cl : ℝ, 0 < Cl ∧ ∀ (P : ℝ) [Fact (0 < P)], ∃ T : Yq P q0E →L[ℂ] Yq P q0E,
    ‖T‖ ≤ Cl ∧
    (∀ F, T F ∈ Ysigma P q0E) ∧
    (∀ Φ, IsSolTest P Φ → ∀ F, phasePair P q0E Φ (T F) = phasePair P q0E Φ F) ∧
    (∀ F, F ∈ realSub P q0E → T F ∈ realSub P q0E) ∧
    (∀ F, F ∈ Osym P q0E → T F ∈ Osym P q0E) ∧
    (∀ (F G : Yq P q0E) (j : Fin 3),
      HasPtwOp P (fun Φ x => -(dy j Φ x)) (fun x => rep F x.1 x.2) (fun x => rep G x.1 x.2) →
      HasPtwOp P (fun Φ x => -(dy j Φ x)) (fun x => rep (T F) x.1 x.2)
        (fun x => rep (T G) x.1 x.2))

/-- `LerayForceProj` from the phase-space Leray operator. -/
theorem lerayForceProj_of (h : LerayYq) : LerayForceProj := by
  obtain ⟨Cl, hCl, hT⟩ := h
  refine ⟨Cl, hCl, fun P _ F hFr hFO => ?_⟩
  obtain ⟨T, hTn, hσ, hid, hreal, hO, hgrad⟩ := hT P
  refine ⟨T F, (mem_forceSpace P).2 ⟨hreal F hFr, hσ F, hO F hFO⟩, fun Φ hΦ => hid Φ hΦ F, ?_, ?_⟩
  · exact (T.le_opNorm F).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))
  · intro G hG
    exact ⟨fun j => T (G j), fun j => hgrad F (G j) j (hG j),
      fun j => (T.le_opNorm (G j)).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))⟩

end UnforcedLeray.Short.IIb
