import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerVelDivFree_of (hF : UnforcedLeray.Short.IIIa.KerAdjFubini)
    (hP : UnforcedLeray.Short.IIIa.KerDivPointwise) :
    UnforcedLeray.Short.IIIa.KerVelDivFree := by
  intro d hd ψ hψ φ hφ
  let F : Fin 2 → ℝ × ℝ → ℂ := fun j x => ((B0579.pd j φ x : ℝ) : ℂ)
  have hFi : ∀ j, IntegrableOn (F j) (B0579.cell d) := fun j =>
    Integrable.ofReal (hφ.pd j).integrableOn
  have hk : ∀ y, kerAdj d F y = 0 := by
    intro y
    have hcongr : (fun x => ∑ j, F j x * ((kerD d (x - y) j : ℝ) : ℂ)) =
        fun x => (((kerD d (x - y) 0 * B0579.pd 0 φ x + kerD d (x - y) 1 * B0579.pd 1 φ x : ℝ)) : ℂ) := by
      funext x
      simp only [F, Fin.sum_univ_two]
      push_cast
      ring
    unfold kerAdj
    rw [hcongr, integral_complex_ofReal, hP d hd φ hφ y]
    simp
  have hmain := hF d hd F hFi ψ hψ
  have h2 : ∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) = 0 := by
    rw [← hmain.2]
    simp [hk]
  have hc : (fun x => ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ)) =
      fun x => ((kerVel d ψ x 0 * B0579.pd 0 φ x + kerVel d ψ x 1 * B0579.pd 1 φ x : ℝ) : ℂ) := by
    funext x
    simp only [F, Fin.sum_univ_two]
    push_cast
    ring
  rw [hc, integral_complex_ofReal] at h2
  exact Complex.ofReal_eq_zero.mp h2

end UnforcedLeray.Short.IIIa
