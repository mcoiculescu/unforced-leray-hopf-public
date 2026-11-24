import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Basic

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the pointwise decomposition

For a spatial flat test `φ` and a time weight `ψ`, the extended integrand of `ExtWeakH1` equals the
flat integrand of the space-time test `ψ(s)φ(x)` plus the error term
`ν ψ(s) ∑ᵢ (bᵢ Δφᵢ + ∑ⱼ Gᵢⱼ ∂ⱼφᵢ)`, which integrates to zero by the weak gradient identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma extWeak_eq_flat_add (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (ψ : ℝ → ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) (hφ : IsFlatSpatialTest c φ) (p : ℝ × (ℝ × ℝ)) :
    extWeakIntegrand ν μ F b G ψ φ p =
      flatIntegrand ν μ (fun _ _ _ => 0) F b (fun s x i => ψ s * φ x i) p +
        (ν : ℂ) * (ψ p.1 : ℂ) * ∑ i : Fin 2, (b p i * (lapP (fun y => φ y i) p.2 : ℂ) +
          ∑ j : Fin 2, G p i j * (B0579.pd j (fun y => φ y i) p.2 : ℂ)) := by
  have hD : ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2),
      flatDt (fun s x i => ψ s * φ x i) s x i = deriv ψ s * φ x i := by
    intro s x i
    unfold flatDt
    exact deriv_mul_const_field _
  have hL : ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2),
      flatLap (fun s x i => ψ s * φ x i) s x i = ψ s * lapP (fun y => φ y i) x := by
    intro s x i
    unfold flatLap
    exact lapP_const_mul (isCylTest_component hφ i) (ψ s) x
  have hG : ∀ (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2),
      flatGrad (fun s x i => ψ s * φ x i) s x i j = ψ s * B0579.pd j (fun y => φ y i) x := by
    intro s x i j
    simp only [flatGrad]
    rw [pd_const_mul_fun (isCylTest_component hφ i).differentiable j (ψ s)]
  simp only [extWeakIntegrand, flatIntegrand, hD, hL, hG, Fin.sum_univ_two]
  push_cast
  ring

end UnforcedLeray.Short.IIIa
