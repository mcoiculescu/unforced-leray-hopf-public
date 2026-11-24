import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5_2

/-!
# `PartIII-b:C/near/pins/5/2/2`: `q`-periodicity of `div_ε` at the recentred point

Source `the November 2 reference manuscript` 1660-1665 (`div_ε`), 2667 (cell
recentring).

`cellPt c p` is either `p` or the translate `p - (0,c,0)` in `q`.  For a `c`-periodic tensor
test `M₀`, the values of `M₀` and the partial derivatives `∂_s, ∂_q, ∂_η` are invariant under
the translation `τ_c : x ↦ x + (0,c,0)` (`fderiv` of a periodic function is periodic), and the
coefficients `s`, `η` of `Q_ε`, `K` are unchanged, so `div_ε M₀` is translation invariant.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- The Fréchet derivative of a function invariant under the `q`-shift by `c` is invariant at
the shifted point. -/
theorem swDivPer_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : UnforcedLeray.B0220.Profile → E)
    (hf : ∀ y : UnforcedLeray.B0220.Profile, f (y + (0, (c, 0))) = f y)
    (y : UnforcedLeray.B0220.Profile) :
    fderiv ℝ f (y + (0, (c, 0))) = fderiv ℝ f y := by
  have hfun : (fun x : UnforcedLeray.B0220.Profile => f (x + (0, (c, 0)))) = f := funext hf
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := y) (0, (c, 0))
  rw [hfun] at h
  exact h.symm

/-- The three profile derivatives `∂_s, ∂_q, ∂_η` are invariant under the `q`-shift. -/
theorem swDivPer_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : UnforcedLeray.B0220.Profile → E)
    (hf : ∀ y : UnforcedLeray.B0220.Profile, f (y + (0, (c, 0))) = f y)
    (y : UnforcedLeray.B0220.Profile) :
    UnforcedLeray.Short.PartIIa.pdS f (y + (0, (c, 0))) = UnforcedLeray.Short.PartIIa.pdS f y ∧
      UnforcedLeray.Short.PartIIa.pdQ f (y + (0, (c, 0))) = UnforcedLeray.Short.PartIIa.pdQ f y ∧
      UnforcedLeray.Short.PartIIa.pdEta f (y + (0, (c, 0))) =
        UnforcedLeray.Short.PartIIa.pdEta f y := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [UnforcedLeray.Short.PartIIa.pdS, UnforcedLeray.Short.PartIIa.pdQ,
      UnforcedLeray.Short.PartIIa.pdEta, swDivPer_fderiv c f hf y]

/-- `div_ε` of a `c`-periodic tensor field is invariant under the `q`-shift. -/
theorem swDivPer_divEps (c ε : ℝ) (M0 : UnforcedLeray.B0220.Profile →
      UnforcedLeray.Short.PartIIa.TensorVal)
    (hper : ∀ y : UnforcedLeray.B0220.Profile, M0 (y + (0, (c, 0))) = M0 y)
    (y : UnforcedLeray.B0220.Profile) :
    UnforcedLeray.Short.PartIIa.divEps ε M0 (y + (0, (c, 0))) =
      UnforcedLeray.Short.PartIIa.divEps ε M0 y := by
  have hf : ∀ k : Fin 4, ∀ z : UnforcedLeray.B0220.Profile,
      (fun p : UnforcedLeray.B0220.Profile => M0 p k) (z + (0, (c, 0))) =
        (fun p : UnforcedLeray.B0220.Profile => M0 p k) z := by
    intro k z
    simp only [hper]
  have a0 := swDivPer_pd c (fun p : UnforcedLeray.B0220.Profile => M0 p 0) (hf 0) y
  have a1 := swDivPer_pd c (fun p : UnforcedLeray.B0220.Profile => M0 p 1) (hf 1) y
  have a2 := swDivPer_pd c (fun p : UnforcedLeray.B0220.Profile => M0 p 2) (hf 2) y
  unfold UnforcedLeray.Short.PartIIa.divEps UnforcedLeray.Short.PartIIa.opQ
    UnforcedLeray.Short.PartIIa.opK UnforcedLeray.Short.PartIIa.opS
  simp only [hper, Prod.fst_add, Prod.snd_add, add_zero, a0.1, a0.2.1, a0.2.2, a1.1, a1.2.1,
    a1.2.2, a2.1, a2.2.1, a2.2.2]

theorem swDivEpsPer : SWDivEpsPer := by
  intro c ε M0 hM p
  have hper : ∀ y : UnforcedLeray.B0220.Profile, M0 (y + (0, (c, 0))) = M0 y := by
    rintro ⟨s, q, η⟩
    have h := hM.periodic (s, (q, η))
    have e : ((s, (q, η)) : UnforcedLeray.B0220.Profile) + (0, (c, 0)) = (s, (q + c, η)) := by
      simp
    rw [e]
    exact h
  obtain ⟨s, q, η⟩ := p
  refine ⟨?_, ?_⟩
  · unfold UnforcedLeray.Short.PartIIIb.NearInst.cellPt
    dsimp only
    split_ifs with h
    · rfl
    · have e : ((s, (q - c, η)) : UnforcedLeray.B0220.Profile) + (0, (c, 0)) = (s, (q, η)) := by
        simp
      have h1 := hper (s, (q - c, η))
      rw [e] at h1
      exact h1.symm
  · unfold UnforcedLeray.Short.PartIIIb.NearInst.cellPt
    dsimp only
    split_ifs with h
    · rfl
    · have e : ((s, (q - c, η)) : UnforcedLeray.B0220.Profile) + (0, (c, 0)) = (s, (q, η)) := by
        simp
      have h2 := swDivPer_divEps c ε M0 hper (s, (q - c, η))
      rw [e] at h2
      exact h2.symm

end UnforcedLeray.Short.PartIIIb.NearInst
