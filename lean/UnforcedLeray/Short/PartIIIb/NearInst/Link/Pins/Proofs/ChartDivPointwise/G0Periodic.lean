import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.CompSmoothLeaf

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A function invariant under the `q`-shift by `c` has `c`-invariant partial derivatives
`∂_q, ∂_s, ∂_η` (differentiate `f ∘ shift = f`; `fderiv_comp_add_right`). -/
theorem periodicDerivLeaf (c : ℝ) (f : Chart → ℝ)
    (hf : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) (s q η : ℝ) :
    Axi.dQ f (s, (q + c, η)) = Axi.dQ f (s, (q, η)) ∧
      Axi.dS f (s, (q + c, η)) = Axi.dS f (s, (q, η)) ∧
      Axi.dEta f (s, (q + c, η)) = Axi.dEta f (s, (q, η)) := by
  have hfun : (fun x : Chart => f (x + (0, (c, 0)))) = f := by
    funext x
    obtain ⟨s', q', η'⟩ := x
    have hx : ((s', (q', η')) : Chart) + (0, (c, 0)) = (s', (q' + c, η')) := by
      simp
    show f ((s', (q', η')) + (0, (c, 0))) = f (s', (q', η'))
    rw [hx]
    exact hf s' q' η'
  have hd : ∀ x : Chart, fderiv ℝ f (x + (0, (c, 0))) = fderiv ℝ f x := by
    intro x
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (0, (c, 0))
    rw [hfun] at h
    exact h.symm
  have hx : ((s, (q + c, η)) : Chart) = (s, (q, η)) + (0, (c, 0)) := by
    simp
  rw [hx]
  refine ⟨?_, ?_, ?_⟩
  · unfold Axi.dQ
    rw [hd]
  · unfold Axi.dS
    rw [hd]
  · unfold Axi.dEta
    rw [hd]

theorem g0Periodic : G0Periodic := by
  intro c ε M hM s q η
  have hc := compSmoothLeaf c M hM
  have pA := (hc (cmpA M) (by simp)).2
  have pB := (hc (cmpB M) (by simp)).2
  have pC := (hc (cmpC M) (by simp)).2
  have pD := (hc (cmpD M) (by simp)).2
  obtain ⟨qA, sA, eA⟩ := periodicDerivLeaf c (cmpA M) pA s q η
  obtain ⟨qB, sB, eB⟩ := periodicDerivLeaf c (cmpB M) pB s q η
  obtain ⟨-, -, eC⟩ := periodicDerivLeaf c (cmpC M) pC s q η
  have vA := pA s q η
  have vB := pB s q η
  have vD := pD s q η
  simp only [G0, qA, sA, eA, qB, sB, eB, eC, vA, vB, vD]

end UnforcedLeray.Short.PartIIIb.NearInst
