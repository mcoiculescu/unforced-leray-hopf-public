import UnforcedLeray.Short.PartI.Sub.PartI_C07

/-!
# `PartI:C07/1`: decomposition of `CanonicalMildIsMildOnPos`

Source `the November 2 reference manuscript`
lines 1094-1125.  The single analytic core is that the coupled mild system for `(A, r)` on
`[b,∞)` says exactly that `V` solves the Duhamel equation of the full generator for the concrete
evolution `Cons.G3b.S`.  The extension below `b` is the cocycle argument proved here.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Core** (source 1094-1125): a canonical mild solution on `[b,∞)` satisfies
`V θ = S θ θ' (V θ')` for `b ≤ θ ≤ θ'` with the concrete `Cons.G3b.S` of
`-V' = (L₀ + θ⁻¹D)V`.  Sketch: the pair `(A, r)` with `V = e^{-λθ}θ^{-κ}(A q + r)` solves the
coupled mild system; regroup the Dyson series of the full generator along `Q = 1 - q⊗ℓ`
(`Cons.G3b.dyson_sum_regroup`, `canonicalActualCoupling_mild_of_complement`,
`actualNormalizedTurnover_eq_stagedDyson`), so that `θ ↦ S b θ`-type Duhamel identity holds for `V`;
uniqueness of mild solutions with bounded perturbation by Gronwall. -/
def CanonicalFullDuhamel : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ V : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V →
      ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → V θ = Cons.G3b.S θ θ' (V θ')

theorem canonical_mild_is_mild_on_pos_of (h : CanonicalFullDuhamel) :
    CanonicalMildIsMildOnPos := by
  intro lam q l hI qd hl hq hqd b hb V hV
  have hD := h lam q l hI qd hl hq hqd b hb V hV
  refine ⟨fun θ => if b ≤ θ then V θ else Cons.G3b.S θ b (V b), ?_, fun θ hθ => by simp [hθ]⟩
  intro θ θ' hθ hθθ'
  by_cases h1 : b ≤ θ
  · have h2 : b ≤ θ' := h1.trans hθθ'
    simp only [h1, h2, if_true]
    exact hD θ θ' h1 hθθ'
  · push_neg at h1
    simp only [not_le.mpr h1, if_false]
    by_cases h2 : b ≤ θ'
    · simp only [h2, if_true]
      rw [hD b θ' le_rfl h2, Cons.G3b.S_comp_apply hθ h1.le h2]
    · push_neg at h2
      simp only [not_le.mpr h2, if_false]
      rw [Cons.G3b.S_comp_apply hθ hθθ' h2.le]

end UnforcedLeray.Short.PartI
