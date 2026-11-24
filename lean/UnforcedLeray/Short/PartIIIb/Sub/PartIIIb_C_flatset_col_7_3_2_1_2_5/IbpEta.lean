import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5.IbpQ.Common

/-!
# `PlaneGaussIbpEta` (task `PartIII-b:C/flatset/col/7/3/2/1/2/5/2`)

Coordinate `1` of the Gaussian integration by parts (source 1650-1656): `∂_{y₁}²G_θ` equals
`(y₁²/(4θ²) - 1/(2θ)) G_θ`, and two integrations by parts in `y₁` move `∂_{y₁}²` onto
`ζ(σ, x - ι y)`, where `∂_{y₁}[ζ(σ,x-ιy)] = -∂_ηζ`. Helpers: `IbpQ/Common.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0224 (planeι)

theorem ibp_a1_e1 (θ : ℝ) (y : Euc 2) :
    ibpA0 θ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) y =
      ((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y := by
  unfold ibpA0
  rw [ibp_inner_single]

theorem plane_gauss_ibp_eta : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneGaussIbpEta := by
  intro c hc ζ hζ θ σ hθ x
  have hv : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : Euc 2)‖ = 1 := ibp_norm_single 1
  have hpl : planeι (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : Euc 2) = ((0 : ℝ), (1 : ℝ)) := by
    rw [UnforcedLeray.B0224.planeι_apply]
    simp
  have hw : ((0 : ℝ), (0 : ℝ), (1 : ℝ)) =
      (0, planeι (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : Euc 2)) := by
    rw [hpl]
  obtain ⟨h1, h2, h3⟩ := ibp_core hc hθ hζ x _ hv _ hw
  have h1' : MeasureTheory.Integrable (fun y : Euc 2 =>
      (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y) •
        ζ (σ, x - planeι y)) := by
    simpa only [ibp_a1_e1] using h1
  have h3' : ∫ y : Euc 2, (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y) •
        ζ (σ, x - planeι y) =
      ∫ y : Euc 2, ibpA0 θ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) y •
        ζ (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_a1_e1]
  exact ⟨h1', h2, h3'.trans h3⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
