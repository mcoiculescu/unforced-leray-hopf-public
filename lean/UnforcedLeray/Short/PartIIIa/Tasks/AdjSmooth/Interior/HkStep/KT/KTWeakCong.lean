import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTWeakCong`: weak derivatives depend only on the a.e. class on the cell

Source: `the November 2 reference manuscript` lines 3052-3058.
The integrands `φ' x * pd ψ x` and `φ x * pd ψ x` (and `g' x * ψ x`, `g x * ψ x`) agree
almost everywhere on the restricted measure, so both integrability and the integral identity
transfer.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem ktWeakCong : UnforcedLeray.Short.IIIa.KTWeakCong := by
  intro c j φ g φ' g' hφ hφ' hg'
  have e1 : ∀ ψ : ℝ × ℝ → ℝ,
      (fun x => φ x * (UnforcedLeray.B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict
        (UnforcedLeray.B0579.cell c)]
        (fun x => φ' x * (UnforcedLeray.B0579.pd j ψ x : ℂ)) :=
    fun ψ => hφ'.symm.mono fun x hx => by simp only [hx]
  have e2 : ∀ ψ : ℝ × ℝ → ℝ,
      (fun x => g x * (ψ x : ℂ)) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
        (fun x => g' x * (ψ x : ℂ)) :=
    fun ψ => hg'.symm.mono fun x hx => by simp only [hx]
  refine ⟨fun ψ hψ => ⟨(hφ.1 ψ hψ).1.congr_fun_ae (e1 ψ), (hφ.1 ψ hψ).2.congr_fun_ae (e2 ψ)⟩,
    fun ψ hψ => ?_⟩
  rw [integral_congr_ae (e1 ψ).symm, integral_congr_ae (e2 ψ).symm]
  exact hφ.2 ψ hψ
