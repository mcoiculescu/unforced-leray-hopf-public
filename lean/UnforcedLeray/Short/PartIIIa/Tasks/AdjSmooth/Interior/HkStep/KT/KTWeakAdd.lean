import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTWeakAdd`: weak derivatives add

Source: `the November 2 reference manuscript` lines 3052-3058.
The integrands split pointwise by `add_mul`; integrability and the integral identity follow
from the two hypotheses by `IntegrableOn.add` and `integral_add`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem ktWeakAdd : UnforcedLeray.Short.IIIa.KTWeakAdd := by
  intro c j φ g φ' g' hφ hφ'
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · refine ((hφ.1 ψ hψ).1.add (hφ'.1 ψ hψ).1).congr_fun_ae ?_
    exact Filter.Eventually.of_forall fun x => by simp [add_mul]
  · refine ((hφ.1 ψ hψ).2.add (hφ'.1 ψ hψ).2).congr_fun_ae ?_
    exact Filter.Eventually.of_forall fun x => by simp [add_mul]
  · have hL : (fun x => (φ + φ') x * (UnforcedLeray.B0579.pd j ψ x : ℂ)) =
        fun x => φ x * (UnforcedLeray.B0579.pd j ψ x : ℂ) +
          φ' x * (UnforcedLeray.B0579.pd j ψ x : ℂ) := by
      funext x
      simp [add_mul]
    have hR : (fun x => (g + g') x * (ψ x : ℂ)) =
        fun x => g x * (ψ x : ℂ) + g' x * (ψ x : ℂ) := by
      funext x
      simp [add_mul]
    rw [hL, hR, integral_add (hφ.1 ψ hψ).1 (hφ'.1 ψ hψ).1,
      integral_add (hφ.1 ψ hψ).2 (hφ'.1 ψ hψ).2, hφ.2 ψ hψ, hφ'.2 ψ hψ]
    ring
