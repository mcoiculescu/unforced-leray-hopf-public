import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5.IbpQ.Common

/-!
# `PlaneGaussIbpQ` (task `PartIII-b:C/flatset/col/7/3/2/1/2/5/1`)

Coordinate `0` of the Gaussian integration by parts (source 1650-1656): `a₀G_θ = ∂_{y₀}²G_θ`
with `a₀(y) = y₀²/(4θ²) - 1/(2θ)`, and two integrations by parts in `y₀` move `∂_{y₀}²` onto
`ζ(σ, x - ι y)`, where `∂_{y₀}[ζ(σ, x-ιy)] = -∂_qζ`. Helpers: `IbpQ/Common.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0224 (planeι)

theorem ibp_a0_e0 (θ : ℝ) (y : Euc 2) :
    ibpA0 θ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) y =
      ((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y := by
  unfold ibpA0
  rw [ibp_inner_single]

theorem plane_gauss_ibp_q : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneGaussIbpQ := by
  intro c hc ζ hζ θ σ hθ x
  have hv : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Euc 2)‖ = 1 := ibp_norm_single 0
  have hpl : planeι (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Euc 2) = ((1 : ℝ), (0 : ℝ)) := by
    rw [UnforcedLeray.B0224.planeι_apply]
    simp
  have hw : ((0 : ℝ), (1 : ℝ), (0 : ℝ)) =
      (0, planeι (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Euc 2)) := by
    rw [hpl]
  obtain ⟨h1, h2, h3⟩ := ibp_core hc hθ hζ x _ hv _ hw
  have h1' : MeasureTheory.Integrable (fun y : Euc 2 =>
      (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y) •
        ζ (σ, x - planeι y)) := by
    simpa only [ibp_a0_e0] using h1
  have h3' : ∫ y : Euc 2, (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y) •
        ζ (σ, x - planeι y) =
      ∫ y : Euc 2, ibpA0 θ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) y •
        ζ (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_a0_e0]
  exact ⟨h1', h2, h3'.trans h3⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
