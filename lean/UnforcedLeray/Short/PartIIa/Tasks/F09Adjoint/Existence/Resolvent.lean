import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Units.B0419
import UnforcedLeray.Lib.Semigroups.Adjoint

/-!
# Part II-a, task `PartII-a:F09/1/2`: existence of the adjoint resolvent at `r = 2`

Source `the November 2 reference manuscript` lines 1359-1361, 1403-1413, 1426-1440.

The adjoint resolvent is the Laplace transform of the adjoint phase semigroup
`(B0421.phaseSemigroup at q = 2)^*` (`Infra.ExpSemigroup.adjoint`), evaluated at `conj μ`.
Its growth rate is `ω = -γ_2 = -1/4`, so the Laplace transform exists exactly on
`Re (conj μ) > -1/4`, i.e. `0 < Re μ + 1/4`, with `‖R‖ ≤ M / (Re (conj μ) - ω) = (Re μ + 1/4)⁻¹`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Existence of the adjoint resolvent** (lines 1426-1440). -/
theorem adjResolventExists : AdjResolventExists := by
  intro P _ ν hν μ hμ
  let S : UnforcedLeray.Infra.ExpSemigroup (Yq P 2) :=
    UnforcedLeray.B0421.phaseSemigroup (P := P) (q := 2) ENNReal.ofNat_ne_top hν.le 1 zero_le_one
      (fun r _ => by
        rw [one_mul]
        exact UnforcedLeray.B0421.norm_freeC_two_le ν r)
  have hM : S.adjoint.M = 1 := rfl
  have hωval : S.adjoint.ω = -(1 / 4 : ℝ) := by
    show -UnforcedLeray.B0418.gammaExp 2 = -(1 / 4 : ℝ)
    rw [UnforcedLeray.B0419.gammaExp_two]
  have hω : S.adjoint.ω < (starRingEnd ℂ μ).re := by
    rw [hωval, Complex.conj_re]
    linarith
  have he : (starRingEnd ℂ μ).re - S.adjoint.ω = μ.re + 1 / 4 := by
    rw [hωval, Complex.conj_re]
    ring
  refine ⟨S.adjoint.laplace (starRingEnd ℂ μ), ?_, fun f => ?_⟩
  · calc ‖S.adjoint.laplace (starRingEnd ℂ μ)‖
        ≤ S.adjoint.M / ((starRingEnd ℂ μ).re - S.adjoint.ω) := S.adjoint.norm_laplace_le hω
      _ = (μ.re + 1 / 4)⁻¹ := by
          rw [he, hM, one_div]
  · exact S.adjoint.laplace_apply hω f

end UnforcedLeray.Short.PartIIa
