import UnforcedLeray.Short.PartI.Tasks.CanonicalFixedPoint
import UnforcedLeray.Short.PartI.Tasks.CanonicalMildIsMildOnPos
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild
import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution

/-!
# `PartI:C08`: backward continuation of the canonical solution

Source of record: `the November 2 reference manuscript`
lines 1094-1125 (uniqueness at infinity, continuation below `b` by `τ = log(b/θ)`, bound
`sup_{0<θ≤b}‖V(θ)‖ ≤ e^{b‖L‖}‖V(b)‖`).

Existing: `canonical_infinity_fixed_point` (C06, normalized mild solution on `[b,∞)`, unique among
`IsCanonicalMild b` with the asymptotic), `canonical_mild_is_mild_on_pos` (C07/1: extension `W`
mild for `Cons.G3b.S` on `(0,∞)`), `Spine.strongCanonicalIsMild` (strong solution is mild for `S`),
`Cons.G3b.norm_S_le`.  The single open input is the converse regrouping
`MildOnPosImpliesCanonicalMild` (the converse of `CanonicalFullDuhamel`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Leaf** (source 1094-1125, "Conversely every normalized solution satisfies the integrals" and
the Dyson regrouping along `Q = 1 - q⊗ℓ`, converse of `CanonicalFullDuhamel`): if `b` is a time at
which a canonical mild solution exists (so the complementary evolution `U` for the clock `b`
exists), then every curve `V'` that is mild on `(0,∞)` for `Cons.G3b.S` is a canonical mild
solution on `[b,∞)`: it is continuous on `[b,∞)` (`Spine.mildSpatialSmoothing`) and `(A, r)` with
`W = e^{λθ}θ^κ V'`, `A = ℓ W`, `r = W - A q` solves the coupled mild equations for `canonicalS U`.
Sketch: subtract the Duhamel identity for `S` (Dyson regrouped along `Q`:
`Cons.G3b.dyson_sum_regroup`, `canonicalActualCoupling_mild_of_complement`) from the one for the
complementary evolution; Gronwall for bounded coupling maps. -/
def MildOnPosImpliesCanonicalMild : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ V₀ : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V₀ →
      ∀ V' : ℝ → B0010.XG, Spine.IsMildOnPos V' → IsCanonicalMild lam q l qd hq hqd b V'

theorem canonical_backward_continuation_of (h : MildOnPosImpliesCanonicalMild)
    {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (hI : IsSeedXG lam q l) {qd : B0010.XG}
    (hl : ∀ f, l f = inner ℂ qd f) (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) :
    ∃ b : ℝ, 0 < b ∧ ∃ W : ℝ → B0010.XG,
      IsCanonicalSolution W ∧ HasCanonicalAsymptotic lam (seedKappa l q hq) q W ∧
      (∀ θ : ℝ, 0 < θ → θ ≤ b → ‖W θ‖ ≤ Real.exp (b * ‖B0012.L0‖) * ‖W b‖) ∧
      ∀ V' : ℝ → B0010.XG, IsCanonicalSolution V' →
        HasCanonicalAsymptotic lam (seedKappa l q hq) q V' → ∀ θ : ℝ, 0 < θ → V' θ = W θ := by
  obtain ⟨b, hb, V, hVm, hVa, hVu⟩ := canonical_infinity_fixed_point hI hl hq hqd
  obtain ⟨W, hW, hWV⟩ := canonical_mild_is_mild_on_pos lam q l hI qd hl hq hqd b hb V hVm
  have hWb : W b = V b := hWV b le_rfl
  refine ⟨b, hb, W, isCanonicalSolution_of_mildOnPos hW, ?_, ?_, ?_⟩
  · obtain ⟨C, b', hb', hA⟩ := hVa
    refine ⟨C, max b b', lt_of_lt_of_le hb (le_max_left _ _), fun θ hθ => ?_⟩
    rw [hWV θ ((le_max_left _ _).trans hθ)]
    exact hA θ ((le_max_right _ _).trans hθ)
  · intro θ hθ hθb
    have h1 : W θ = Cons.G3b.S θ b (W b) := hW θ b hθ hθb
    rw [h1]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    · exact (Cons.G3b.norm_S_le hθ hθb).trans (Real.exp_le_exp.2 (by
        have := norm_nonneg (B0012.L0 : B0010.XG →L[ℂ] B0010.XG)
        nlinarith))
  · intro V' hV' hV'a θ hθ
    have hmild : Spine.IsMildOnPos V' := fun x y hx hxy => Spine.strongCanonicalIsMild V' hV' x y hx hxy
    have hcm := h lam q l hI qd hl hq hqd b hb V hVm V' hmild
    have hEq := hVu V' hcm hV'a
    have hbV : V' b = V b := hEq b le_rfl
    rcases le_or_gt b θ with hbθ | hθb
    · rw [hEq θ hbθ, hWV θ hbθ]
    · rw [hmild θ b hθ hθb.le, hbV, hW θ b hθ hθb.le, hWb]

end UnforcedLeray.Short.PartI
