import UnforcedLeray.Short.PartI.Sub.PartI_C08
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.MildOnPos

/-!
# `PartI:C08`: backward continuation of the canonical solution

Source of record: `the November 2 reference manuscript`
lines 1118-1125. The hypothesis `MildOnPosImpliesCanonicalMild` is discharged by
`mildOnPosImpliesCanonicalMild_proof` (`Tasks/CanonicalBackward/MildOnPos.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem canonical_backward_continuation {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) :
    ∃ b : ℝ, 0 < b ∧ ∃ W : ℝ → B0010.XG, IsCanonicalSolution W ∧
      HasCanonicalAsymptotic lam (seedKappa l q hq) q W ∧
      (∀ θ : ℝ, 0 < θ → θ ≤ b → ‖W θ‖ ≤ Real.exp (b * ‖B0012.L0‖) * ‖W b‖) ∧
      ∀ V' : ℝ → B0010.XG, IsCanonicalSolution V' →
        HasCanonicalAsymptotic lam (seedKappa l q hq) q V' → ∀ θ : ℝ, 0 < θ → V' θ = W θ :=
  canonical_backward_continuation_of mildOnPosImpliesCanonicalMild_proof hI hl hq hqd

end UnforcedLeray.Short.PartI
