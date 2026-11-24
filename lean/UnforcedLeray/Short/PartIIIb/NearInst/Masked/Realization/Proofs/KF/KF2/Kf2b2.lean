import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub2
import UnforcedLeray.Units.B0225.Pointwise

/-!
# `KF2b2` (source 3613): the Laplace integral evaluated pointwise a.e.

Template: `B0225.R0_ae_eq`. The first conclusion is `Integrable.prod_right_ae` of the Fubini
integrability hypothesis. For the second, both sides are tested against sets `A` of finite measure
(`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`); `f ↦ ∫_A f` is the bounded functional
`B0225.setIntL`, which commutes with the Bochner integral in time, and Fubini swaps the order of
integration on `A × (0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.B0223 UnforcedLeray.Infra

theorem kf2b2 : KF2b2 := by
  intro P _ S μ hμ x G hG hGT hint
  refine ⟨?_, ?_⟩
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun A _ hA => ?_
    exact (hint A hA).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun A _ hA => B0225.integrableOn_of_memLp' (Lp.memLp (S.laplace μ x)) hA)
      (fun A _ hA => (hint A hA).integral_prod_left)
      (fun A _ hA => ?_)
    have hi := hint A hA
    have hswap : ∫ w in A, ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) • G t w ∂volume =
        ∫ t in Ioi (0 : ℝ), ∫ w in A, Complex.exp (-(μ * t)) • G t w ∂volume :=
      integral_integral_swap hi
    have hcomm : B0225.setIntL A hA (∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) • S.T t x) =
        ∫ t in Ioi (0 : ℝ), B0225.setIntL A hA (Complex.exp (-(μ * t)) • S.T t x) :=
      ((B0225.setIntL A hA).integral_comp_comm (S.integrableOn_lapInt hμ x)).symm
    rw [hswap]
    change B0225.setIntL A hA (S.laplace μ x) = _
    rw [S.laplace_apply hμ x]
    refine hcomm.trans (integral_congr_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    rw [map_smul, B0225.setIntL_apply, ← integral_smul]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGT t ht'] with w hw
    simp only [hw]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
