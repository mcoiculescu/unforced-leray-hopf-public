import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.NsSymNormLe

/-!
# `PartIII-b:C/near/masked/22/2/6`: the source norm bound `∫∫|cartLift g|² ≤ 2πRc ‖g‖²` (source 4000-4003)

Leaf Q6 of `PartIII-b_C_near_masked_22_2.lean`: `NearSource`.
Route: off the axis `srcNorm (cartLift) = gAx` (`cartLiftNormOffAxis_holds`), the axis is null
(`axisNull_holds`), `chartL2Source_of` gives the `L²` identity, and `|nsSym T| ≤ |T|`
(`nsSymNormLe_holds`) with `eLpNorm_nnreal_pow_eq_lintegral` closes it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **Leaf Q6** (source norm, 2683). -/
theorem nearSource_holds : NearSource := by
  intro R c g hR hc hg
  have hgm : Measurable g := hg.measurable
  have hL2 := chartL2Source_of ageShift_holds polarReduction_holds
    (chartChange_of chartChangeSE_holds chartChangeTQ_holds) gAxFacts_holds R c hR hc g hgm
  -- the axis `{hRad z = 0}` is null, so `srcNorm = gAx` almost everywhere
  have hae : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space), hRad z ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) axisNull_holds
    exact not_not.1 hz
  have hstep1 : ∀ τ : ℝ,
      (∫⁻ z : UnforcedLeray.Space,
          UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) τ z ^ (2 : ℝ)) =
        ∫⁻ z : UnforcedLeray.Space, gAx R c g τ z ^ (2 : ℝ) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [cartLiftNormOffAxis_holds R c g τ z hz]
  -- `|nsSym T| ≤ |T|` and `ofReal ‖T‖ = ‖T‖ₑ` on the target side
  have hkey : ∀ T : Ten3, ENNReal.ofReal ‖T‖ = ‖T‖ₑ := fun T => by simp
  have hgnorm : (∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (g x))) ^
        (2 : ℝ) ∂(ageμ c (-1 / 2))) ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
    refine lintegral_mono fun x => ?_
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← hkey (g x)]
    exact ENNReal.ofReal_le_ofReal (nsSymNormLe_holds (g x))
  have hLp : eLpNorm g 2 (ageμ c (-1 / 2)) ^ (2 : ℝ) =
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := ageμ c (-1 / 2)) (p := 2)
      (by norm_num)
    simpa using h
  calc (∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
          UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) τ z ^ (2 : ℝ))
      = ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
          gAx R c g τ z ^ (2 : ℝ) := lintegral_congr fun τ => hstep1 τ
    _ = ENNReal.ofReal (2 * Real.pi * R * c) * ∫⁻ x,
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (g x))) ^ (2 : ℝ)
            ∂(ageμ c (-1 / 2)) := hL2
    _ ≤ ENNReal.ofReal (2 * Real.pi * R * c) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)
            ∂(ageμ c (-1 / 2)) := by gcongr
    _ = ENNReal.ofReal (2 * Real.pi * R * c) * eLpNorm g 2 (ageμ c (-1 / 2)) ^ (2 : ℝ) := by
          rw [hLp]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
