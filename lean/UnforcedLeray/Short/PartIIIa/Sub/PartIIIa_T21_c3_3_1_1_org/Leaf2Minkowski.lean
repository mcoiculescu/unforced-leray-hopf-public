import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Defs
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# Leaf (b) helper: Minkowski's integral inequality in `X_{m,d}`

Proves `XNormIntegralLe` (Props of `Leaf2Defs.lean`) from the Bochner Minkowski inequality
`UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le`, applied with `p = 2` on the product of the
cell measure and the time measure `volume.restrict (Ioc a b)`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

theorem xNormIntegralLe : UnforcedLeray.Short.IIIa.ComplFreeRateSub.XNormIntegralLe := by
  unfold UnforcedLeray.Short.IIIa.ComplFreeRateSub.XNormIntegralLe
  intro d m a b G hG
  haveI hSF : SFinite (UnforcedLeray.B0579.cellMeasure d m) := by
    unfold UnforcedLeray.B0579.cellMeasure; infer_instance
  haveI hSG : SigmaFinite (UnforcedLeray.B0579.cellMeasure d m) := by
    unfold UnforcedLeray.B0579.cellMeasure; infer_instance
  have hsw : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => G z.2 z.1)
      ((UnforcedLeray.B0579.cellMeasure d m).prod (volume.restrict (Ioc a b))) :=
    hG.prod_swap
  have key := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
    (μ := UnforcedLeray.B0579.cellMeasure d m) (ν := volume.restrict (Ioc a b))
    (F := fun x r => G r x) hsw (p := 2) (by norm_num) (by norm_num)
  unfold UnforcedLeray.Short.IIIa.xNorm
  exact key
