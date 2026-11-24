import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 5 of `Spine:SP-CAN/4/5/3`: `oscillatorD` of a real function is real

Proves `ConjOscillatorD` (statement and docstring in `Short/Spine/Sub/SP_CAN4_5_3.lean`).
Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140. The classical formula `D = Δ + ½ y·∇ + 2` is in the old manuscript `paper/main.tex`
1879-1888 (read only).

Proof: for `ψ` real and smooth, `deriv (ψ : ℝ → ℂ) = (deriv ψ : ℂ)` and the same for the second
derivative (`HasDerivAt.ofReal_comp`). Substituting into `oscillatorD` makes every summand the
image of a real number, and `Complex.conj_ofReal` finishes the proof. The case `r = 0` needs no
separate treatment, since `map_div₀` holds for division by zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

/-- **Leaf 5, `oscillatorD` of a real function is real.** -/
theorem conjOscillatorD_proof : ConjOscillatorD := by
  unfold ConjOscillatorD
  intro ψ hψ r
  obtain ⟨hd1, hψ'⟩ := contDiff_infty_iff_deriv.mp hψ
  have hd2 : Differentiable ℝ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ').1
  have h1 : ∀ s : ℝ, deriv (fun t : ℝ => (ψ t : ℂ)) s = ((deriv ψ s : ℝ) : ℂ) := fun s =>
    ((hd1 s).hasDerivAt.ofReal_comp).deriv
  have hfun : deriv (fun t : ℝ => (ψ t : ℂ)) = fun t => ((deriv ψ t : ℝ) : ℂ) := funext h1
  have h2 : ∀ s : ℝ, deriv (deriv (fun t : ℝ => (ψ t : ℂ))) s = ((deriv (deriv ψ) s : ℝ) : ℂ) := by
    intro s
    rw [hfun]
    exact ((hd2 s).hasDerivAt.ofReal_comp).deriv
  simp only [oscillatorD, h1, h2]
  simp [map_add, map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_ofNat]

end UnforcedLeray.Short.Spine
