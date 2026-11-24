import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap

/-!
# Part II-b, leaf `PartII-b:G4/3/6/2/3/5`: `PsiEtaSegment`

Source of record: `the November 2 reference manuscript` 2419-2423 (jets of the
stream), 261-291 (`v = ∇^⊥ψ`).

For fixed `s > 0` and `q`, the function `f t = ∂_s^l ψ(s,(q,t))` has derivative
`-(∂_s^l v)₀(s,(q,t))` by `PsiEtaSwap`. A sup bound `B` on `∂_s^l v` along the segment (with the
component bound `|v₀| ≤ ‖v‖`) gives the Lipschitz bound `|f a - f b| ≤ B |a - b|`, which, together
with the triangle inequality, is the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Norm of an age jet of order zero is the norm of the age derivative. -/
private lemma psiES_norm_ageJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 F s z‖ = ‖iteratedDeriv ℓ (fun r => F r z) s‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_zero]

end UnforcedLeray.Short.IIb

/-- **FTC in `η`** (SP 2419-2423), leaf `PartII-b:G4/3/6/2/3/5`. -/
theorem psiEtaSegment_proof : UnforcedLeray.Short.IIb.PsiEtaSegment := by
  intro ψ v hsp l s hs q a b B hB
  -- the component bound `|v₀| ≤ ‖v‖` on the segment
  have hbound : ∀ t ∈ uIcc a b,
      ‖-(iteratedDeriv l (fun r => v r (q, t)) s 0)‖ ≤ B := by
    intro t ht
    rw [norm_neg]
    have h1 := hB t ht
    rw [UnforcedLeray.Short.IIb.psiES_norm_ageJet_zero] at h1
    exact (PiLp.norm_apply_le (iteratedDeriv l (fun r => v r (q, t)) s) 0).trans h1
  -- the derivative of `t ↦ ∂_s^l ψ(s,(q,t))` is `-(∂_s^l v)₀` (`PsiEtaSwap`)
  have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t' : ℝ => iteratedDeriv l (fun r => ψ r (q, t')) s)
    (f' := fun t : ℝ => -(iteratedDeriv l (fun r => v r (q, t)) s 0))
    (s := uIcc a b)
    (fun t _ => (psiEtaSwap_proof ψ v hsp l s hs q t).hasDerivWithinAt) hbound
    (convex_uIcc a b) right_mem_uIcc left_mem_uIcc
  have hn := norm_sub_norm_le (iteratedDeriv l (fun r => ψ r (q, a)) s)
    (iteratedDeriv l (fun r => ψ r (q, b)) s)
  simp only [Real.norm_eq_abs] at hdiff hn
  rw [UnforcedLeray.Short.IIb.psiES_norm_ageJet_zero, UnforcedLeray.Short.IIb.psiES_norm_ageJet_zero]
  simp only [Real.norm_eq_abs] at hdiff hn ⊢
  linarith
