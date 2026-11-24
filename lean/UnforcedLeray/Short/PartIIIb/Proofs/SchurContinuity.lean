import UnforcedLeray.Short.PartIIIb.Tasks
import UnforcedLeray.Lib.AlgBlocks.Neumann

/-!
# Proof of `T_schurContinuity` (target `schurContinuity`; source: `the November 2 reference manuscript`, line 5760)

Continuity in `z` of `ℓ(z) (schurSol (A z) (B z) (C z) (R z) (a z))` on `[-1,1]`.

* `z ↦ (I - C z)⁻¹` is continuous on `[-1,1]`: `I - C z` is a unit there (`‖C z‖ ≤ c < 1`), and
  `Ring.inverse` is continuous at units (`NormedRing.inverse_continuousAt`).
* `R̃(z) = R z + A z ∘ (I - C z)⁻¹ ∘ B z` is continuous on `[-1,1]` (`ContinuousOn.clm_comp`).
* `I - R̃ z` is a unit there (`‖R̃ z‖ ≤ q < 1`), so `z ↦ (I - R̃ z)⁻¹` is continuous, and
  `z ↦ (I - R̃ z)⁻¹ (a z)` is continuous (`ContinuousOn.clm_apply`).
* Pairing with `ℓ z` (`ContinuousOn.clm_apply`) finishes the proof.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- `Ring.inverse` is continuous at every unit of a complete normed ring. -/
theorem schurCont_inv_cont {R : Type} [NormedRing R] [CompleteSpace R] {u : R}
    (hu : IsUnit u) : ContinuousAt Ring.inverse u := by
  obtain ⟨v, rfl⟩ := hu
  exact NormedRing.inverse_continuousAt v

/-- Continuity in `z` of the frozen quantity `ℓ(z) w(z)` of `closure:mixed-return`
(line 5760), with `w(z) = (I - R̃(z))⁻¹ a(z)`.  Proof sketch in the module docstring. -/
theorem schurContinuity : UnforcedLeray.Short.PartIIIb.T_schurContinuity := by
  unfold UnforcedLeray.Short.PartIIIb.T_schurContinuity
  intro E X hEg hEs hEc hXg hXs hXc A B C R a ℓ c q hA hB hC hR ha hℓ hCc hc hRq hq
  -- Step 1: `z ↦ (I - C z)⁻¹` is continuous on `[-1,1]`.
  have hCinv : ContinuousOn (fun z => Ring.inverse (1 - C z)) (Icc (-1 : ℝ) 1) := by
    intro z0 hz0
    have hu : IsUnit (1 - C z0) :=
      UnforcedLeray.Algebra.isUnit_one_sub (lt_of_le_of_lt (hCc z0 hz0) hc)
    have h1 : ContinuousAt Ring.inverse (1 - C z0) := schurCont_inv_cont hu
    have h2 : ContinuousWithinAt (fun z => 1 - C z) (Icc (-1 : ℝ) 1) z0 :=
      continuousWithinAt_const.sub (hC z0 hz0)
    exact h1.comp_continuousWithinAt_of_eq h2 rfl
  -- Step 2: `z ↦ R̃ z = R z + A z ∘ ((I - C z)⁻¹ ∘ B z)` is continuous on `[-1,1]`
  -- (`∘L` is right associative, so `schurTilde` is `R + A ∘L (inv ∘L B)`).
  have hT : ContinuousOn (fun z => schurTilde (A z) (B z) (C z) (R z)) (Icc (-1 : ℝ) 1) := by
    unfold schurTilde
    exact hR.add (ContinuousOn.clm_comp hA (ContinuousOn.clm_comp hCinv hB))
  -- Step 3: `z ↦ (I - R̃ z)⁻¹` is continuous on `[-1,1]`, since `‖R̃ z‖ ≤ q < 1`.
  have hWinv : ContinuousOn (fun z => Ring.inverse (1 - schurTilde (A z) (B z) (C z) (R z)))
      (Icc (-1 : ℝ) 1) := by
    intro z0 hz0
    have hu : IsUnit (1 - schurTilde (A z0) (B z0) (C z0) (R z0)) :=
      UnforcedLeray.Algebra.isUnit_one_sub (lt_of_le_of_lt (hRq z0 hz0) hq)
    have h1 : ContinuousAt Ring.inverse (1 - schurTilde (A z0) (B z0) (C z0) (R z0)) :=
      schurCont_inv_cont hu
    have h2 : ContinuousWithinAt (fun z => 1 - schurTilde (A z) (B z) (C z) (R z))
        (Icc (-1 : ℝ) 1) z0 :=
      continuousWithinAt_const.sub (hT z0 hz0)
    exact h1.comp_continuousWithinAt_of_eq h2 rfl
  -- Step 4: `z ↦ w(z) = (I - R̃ z)⁻¹ (a z)` is continuous on `[-1,1]`.
  have hWa : ContinuousOn (fun z => Ring.inverse (1 - schurTilde (A z) (B z) (C z) (R z)) (a z))
      (Icc (-1 : ℝ) 1) :=
    ContinuousOn.clm_apply hWinv ha
  -- Step 5: pair with `ℓ z`.
  unfold schurSol
  exact ContinuousOn.clm_apply hℓ hWa

end UnforcedLeray.Short.PartIIIb
