import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

theorem secSectorSmooth_proof : UnforcedLeray.Short.PartI.SecSectorSmooth := by
  intro m ψ hψ y hy
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hψa : ContDiffAt ℝ ∞ ψ ‖y‖ := hψ.contDiffAt (Ioi_mem_nhds hpos)
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) y := contDiffAt_norm ℝ hy
  have hψc : ContDiffAt ℝ ∞ (fun z : ℂ => ψ ‖z‖) y := hψa.comp y hn
  have hnC : ContDiffAt ℝ ∞ (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hn
  have hne : ((‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hnCinv : ContDiffAt ℝ ∞ (fun z : ℂ => (((‖z‖ : ℝ) : ℂ))⁻¹) y := hnC.inv hne
  have hu : ContDiffAt ℝ ∞ (fun z : ℂ => z / ((‖z‖ : ℝ) : ℂ)) y := by
    simp only [div_eq_mul_inv]
    exact contDiffAt_id.mul hnCinv
  have hune : y / ((‖y‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero hy hne
  have hpow : ContDiffAt ℝ ∞ (fun z : ℂ => (z / ((‖z‖ : ℝ) : ℂ)) ^ m) y := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simp only [zpow_natCast]
      exact hu.pow n
    · simp only [zpow_neg, zpow_natCast]
      exact (hu.pow n).inv (pow_ne_zero n hune)
  have hfun : ContDiffAt ℝ ∞ (fun z : ℂ => ψ ‖z‖ * (z / ((‖z‖ : ℝ) : ℂ)) ^ m) y :=
    hψc.mul hpow
  exact hfun
