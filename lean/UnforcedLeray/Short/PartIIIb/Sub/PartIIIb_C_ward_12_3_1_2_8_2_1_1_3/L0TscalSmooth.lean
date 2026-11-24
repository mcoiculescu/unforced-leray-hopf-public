import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l0TscalSmooth : L0TscalSmooth := by
  intro ν ψ hψ
  have hfd : ∀ (g : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ g → ∀ v : ℝ × UnforcedLeray.Space,
      ContDiff ℝ ∞ (fun p => fderiv ℝ g p v) := fun g hg v =>
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdy : ∀ (g : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ g → ∀ j : Fin 3,
      ContDiff ℝ ∞ (dy j g) := fun g hg j => hfd g hg _
  have hdτ : ContDiff ℝ ∞ (dτ ψ) := hfd ψ hψ (1, 0)
  have hdyψ : ∀ j : Fin 3, ContDiff ℝ ∞ (dy j ψ) := fun j => hdy ψ hψ j
  have hlap : ContDiff ℝ ∞ (lapT ψ) := by
    unfold lapT
    exact ContDiff.sum fun j _ => hdy _ (hdyψ j) j
  have hcoord : ∀ j : Fin 3, ContDiff ℝ ∞ (fun p : ℝ × UnforcedLeray.Space => p.2 j) := fun j =>
    (EuclideanSpace.proj j : UnforcedLeray.Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hrad : ContDiff ℝ ∞ (radialT ψ) := by
    unfold radialT
    exact ContDiff.sum fun j _ => (hcoord j).smul (hdyψ j)
  unfold L0Tscal
  exact (((hdτ.neg).add ((contDiff_const (c := (1 / 2 : ℝ))).smul hrad)).add
    ((contDiff_const (c := (1 / 2 : ℝ))).smul hψ)).sub
    ((contDiff_const (c := ν)).smul hlap)

end UnforcedLeray.Short.PartIIIb.Concrete
