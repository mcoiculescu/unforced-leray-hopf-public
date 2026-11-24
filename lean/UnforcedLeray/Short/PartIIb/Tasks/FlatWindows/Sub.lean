import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory

theorem flatResponseSub : FlatResponseSub := by
  intro ν μ F b b' hb hb'
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := hb.solenoidal φ hφ
    obtain ⟨i2, e2⟩ := hb'.solenoidal φ hφ
    have hfun : (fun x : Coord => (b - b') x 0 * (cpd 1 φ x : ℂ) + (b - b') x 1 * (cpd 2 φ x : ℂ))
        = fun x => (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) -
            (b' x 0 * (cpd 1 φ x : ℂ) + b' x 1 * (cpd 2 φ x : ℂ)) := by
      funext x
      simp only [Pi.sub_apply, PiLp.sub_apply]
      ring
    rw [hfun]
    refine ⟨i1.sub i2, ?_⟩
    rw [integral_sub i1 i2, e1, e2, sub_zero]
  · obtain ⟨i1, -, e1⟩ := hb.equation Ψ hΨ
    obtain ⟨i2, -, e2⟩ := hb'.equation Ψ hΨ
    have hsum : (fun x : Coord => ∑ i : Fin 2, (b - b') x i * flatTranspose ν μ Ψ x i)
        = fun x => (∑ i : Fin 2, b x i * flatTranspose ν μ Ψ x i) -
            (∑ i : Fin 2, b' x i * flatTranspose ν μ Ψ x i) := by
      funext x
      simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have h0 : cdot 0 Ψ = fun _ => 0 := by
      funext x
      simp [cdot]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum]
      exact i1.sub i2
    · rw [h0]
      exact integrable_zero _ _ _
    · rw [hsum, integral_sub i1 i2, e1, e2, sub_self]
      simp [h0]

end UnforcedLeray.Short.IIb

end
