import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Lib.PhaseSpace.Charts

/-!
# Part II-a, task `PartII-a:F06/1/6`: the norm of a represented element of `Y_r`

Source of record: `the November 2 reference manuscript`, lines 1431-1480.
Proves `YqRepNorm` (P5 of `Sub/PartIIa_F06_1.lean`): if `IsRep a Λ` then
`P ‖a‖_{Y_r}^r = ∫₀^P ∫ ‖Λ‖^r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIa.Rep

theorem yqRepNorm : YqRepNorm := by
  intro r hr1 hrt P hP a Λ haR
  have hq' : r ≠ ⊤ := hrt
  -- Slice-wise: the inner integral of `‖Λ‖^r` equals `‖a(τ)‖^r` for a.e. `τ`.
  have hslice : ∀ᵐ τ : ℝ, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal = ‖a (τ : AddCircle P)‖ₑ ^ r.toReal := by
    filter_upwards [haR.slice] with τ hτ
    rw [← lintegral_enorm_rpow_Lp (a (τ : AddCircle P)) hq']
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    rw [hy]
  rw [lintegral_congr_ae (ae_restrict_of_ae hslice)]
  -- Integrate the slice norm over one period.
  have hper := lintegral_Ioc_period (fun x : AddCircle P => ‖a x‖ₑ ^ r.toReal)
    0 0
  simp only [zero_add] at hper
  rw [hper, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
    lintegral_enorm_rpow_Yq a hq', smul_eq_mul]
