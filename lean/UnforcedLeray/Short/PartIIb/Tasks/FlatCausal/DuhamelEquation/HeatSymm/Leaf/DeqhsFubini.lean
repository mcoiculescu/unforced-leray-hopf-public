import UnforcedLeray.Short.PartIIb.Sub.T12_7_3

/-!
# Part II-b, leaf `DeqhsFubini` (SP 1923-1927): Fubini, translation and evenness

Statement `DeqhsFubini` of `Sub/T12_7_3.lean`. Route: Fubini (`integral_integral_swap`), the
translation `u = z - w` (`integral_sub_right_eq_self`), a second Fubini after the measure preserving
shear `(u, w) ↦ (u + w, w)` (`measurePreserving_add_prod`), and `K(-w) = K(w)`
(`integral_neg_eq_self`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqhsFubini : UnforcedLeray.Short.IIb.DeqhsFubini := by
  intro θ hθ f hf ψ hψ hψc hint
  have hev : ∀ w : ℝ × ℝ, flatHeatKernel θ (-w) = flatHeatKernel θ w := by
    intro w
    simp [flatHeatKernel]
  -- Step 1: pull `ψ z` inside the inner integral
  have step1 : ∀ z : ℝ × ℝ, (∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * f (z - w)) * (ψ z : ℂ)
      = ∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * f (z - w) * (ψ z : ℂ) := by
    intro z
    rw [integral_mul_const]
  simp only [step1]
  -- Step 2: first Fubini swap
  rw [integral_integral_swap (f := fun z w : ℝ × ℝ =>
    (flatHeatKernel θ w : ℂ) * f (z - w) * (ψ z : ℂ)) hint]
  -- Step 3: translation in the inner variable
  have step3 : ∀ w : ℝ × ℝ, (∫ z : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * f (z - w) * (ψ z : ℂ))
      = (flatHeatKernel θ w : ℂ) * ∫ u : ℝ × ℝ, f u * (ψ (u + w) : ℂ) := by
    intro w
    have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun x : ℝ × ℝ => f x * (ψ (x + w) : ℂ)) w
    simp only [sub_add_cancel] at h
    simp only [mul_assoc]
    rw [integral_const_mul, h]
  simp only [step3]
  -- Step 4: the integrand `Φ w u = K w * (f u * ψ (u + w))` is integrable
  have hT := (measurePreserving_add_prod (volume : Measure (ℝ × ℝ))
    (volume : Measure (ℝ × ℝ))).integrable_comp_of_integrable hint
  have hΦ : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      (flatHeatKernel θ z.1 : ℂ) * (f z.2 * (ψ (z.2 + z.1) : ℂ)))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    have hs := hT.swap
    convert hs using 1
    funext z
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, add_sub_cancel_right]
    ring
  -- Step 5: second Fubini swap
  have hswap := integral_integral_swap (μ := (volume : Measure (ℝ × ℝ)))
    (ν := (volume : Measure (ℝ × ℝ)))
    (f := fun w u : ℝ × ℝ => (flatHeatKernel θ w : ℂ) * (f u * (ψ (u + w) : ℂ))) hΦ
  have hA : ∀ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * ∫ u : ℝ × ℝ, f u * (ψ (u + w) : ℂ)
      = ∫ u : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * (f u * (ψ (u + w) : ℂ)) :=
    fun w => (integral_const_mul _ _).symm
  simp only [hA]
  rw [hswap]
  -- Step 6: evenness of the kernel and the real-to-complex cast
  congr 1
  funext u
  have hneg : ∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (u - w)
      = ∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (u + w) := by
    have h := integral_neg_eq_self (fun w : ℝ × ℝ => flatHeatKernel θ w * ψ (u + w))
      (volume : Measure (ℝ × ℝ))
    have e : ∀ w : ℝ × ℝ, flatHeatKernel θ (-w) * ψ (u + -w) = flatHeatKernel θ w * ψ (u - w) := by
      intro w
      rw [hev, ← sub_eq_add_neg]
    simp only [e] at h
    exact h
  calc ∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * (f u * (ψ (u + w) : ℂ))
      = ∫ w : ℝ × ℝ, f u * (((flatHeatKernel θ w * ψ (u + w) : ℝ)) : ℂ) := by
        congr 1
        funext w
        push_cast
        ring
    _ = f u * ∫ w : ℝ × ℝ, (((flatHeatKernel θ w * ψ (u + w) : ℝ)) : ℂ) :=
        integral_const_mul _ _
    _ = f u * ((∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (u + w) : ℝ) : ℂ) := by
        congr 1
        exact integral_ofReal
    _ = f u * ((∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (u - w) : ℝ) : ℂ) := by
        rw [hneg]

end UnforcedLeray.Short.IIb
