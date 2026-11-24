import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedScalarFamily

/-!
# Bounded Dyson regrouping by mild uniqueness

This leaf derives, rather than assumes, the regrouping identity for two bounded interactions.
The proof transfers the concrete mild equation from their sum to the first interaction and then
uses mild uniqueness for the second interaction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Evolution

/-- The pointwise sum of two bounded perturbations on the same finite interval. -/
def boundedPertSum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {a b : ℝ} (A B : BoundedPert X a b) : BoundedPert X a b := by
  let CA : ℝ := Classical.choose A.bdd
  let CB : ℝ := Classical.choose B.bdd
  have hCA : ∀ t ∈ Set.Icc a b, ‖A.A t‖ ≤ CA := Classical.choose_spec A.bdd
  have hCB : ∀ t ∈ Set.Icc a b, ‖B.A t‖ ≤ CB := Classical.choose_spec B.bdd
  refine ⟨fun t => A.A t + B.A t, ?_, ?_⟩
  · intro x
    exact (A.meas x).add (B.meas x)
  · refine ⟨max CA 0 + max CB 0, fun t ht => ?_⟩
    calc
      ‖A.A t + B.A t‖ ≤ ‖A.A t‖ + ‖B.A t‖ := norm_add_le _ _
      _ ≤ max CA 0 + max CB 0 :=
        add_le_add ((hCA t ht).trans (le_max_left CA 0))
          ((hCB t ht).trans (le_max_left CB 0))

/-- Subtracting the first summand from a pointwise sum leaves the second perturbation. -/
theorem boundedPertSum_sub_left {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {a b : ℝ} (A B : BoundedPert X a b) (t : ℝ) :
    (boundedPertSum A B).A t - A.A t = B.A t := by
  ext x
  simp only [boundedPertSum, sub_apply, add_apply]
  abel

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {a b : ℝ}

/-- The Dyson evolution for a sum of bounded perturbations is exactly the second Dyson
perturbation of the first. This follows by applying the existing mild-transfer and uniqueness
theorems to the concrete Dyson mild equation. -/
theorem dyson_sum_regroup (F : EvolutionFamily X a b) (A B : BoundedPert X a b)
    {s : ℝ} (hs : a ≤ s) :
    ∀ t, s ≤ t → t ≤ b → ∀ x : X,
      (dyson F (boundedPertSum A B)).U t s x =
        (dyson (dyson F A) B).U t s x := by
  intro t hst ht x
  let C := boundedPertSum A B
  let U := dyson F C
  let z : ℝ → X := fun τ => U.U τ s x
  have hsb : s ≤ b := hst.trans ht
  have hdiag : z s = x := by
    dsimp [z]
    rw [U.U_diag s ⟨hs, hsb⟩]
    rfl
  have hz : ∀ τ ∈ Icc s b,
      z τ = F.U τ s (z s) + ∫ r in s..τ, F.U τ r (C.A r (z r) + 0) := by
    intro τ hτ
    have hleft := dyson_left (F := F) (A := C) ⟨hs, hτ.1, hτ.2⟩ x
    simpa [z, U, C, hdiag] using hleft
  have hzc : ContinuousOn z (Icc s b) := by
    exact U.continuousOn_fst hs x
  have htrans := mild_transfer (F := F) (A₁ := C) (A₂ := A) hs hzc
    integrableOn_zero hz
  have hsum : ∀ r, C.A r - A.A r = B.A r := by
    intro r
    exact boundedPertSum_sub_left A B r
  have hmild : ∀ τ ∈ Icc s b,
      z τ = (dyson F A).U τ s (z s) +
        ∫ r in s..τ, (dyson F A).U τ r (B.A r (z r) + 0) := by
    intro τ hτ
    simpa [hsum] using htrans τ hτ
  have huniq := mild_unique (F := dyson F A) (A := B) hs hzc
    integrableOn_zero hmild
  have htmem : t ∈ Icc s b := ⟨hst, ht⟩
  simpa [z, U, hdiag] using huniq t htmem

end UnforcedLeray.Evolution

end
