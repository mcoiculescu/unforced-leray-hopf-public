import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2
import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution

/-!
# Fibre strong continuity of the planar heat (decomposition of `heatFiberCont_holds`)

Source `the November 2 reference manuscript` lines 1650-1656.  The `MeridC`-valued
fibre statement `HeatFiberCont` is reduced to the `Vec = ℝ²`-valued one (the carrier of the
`HeatCylinder` heat theory), which in turn is the strong continuity
`HeatCylinder.tendsto_heatVecL2CLM_apply_zero_full` transported to the strip.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

open UnforcedLeray.B0224 (planeHeat strip planeHeat_of_nonpos)
open UnforcedLeray.Train (Vec)

/-- Fibre strong continuity of the planar heat at time `0`, `Vec = ℝ²`-valued fibres. -/
def HeatFiberContVec (c : ℝ) : Prop :=
  ∀ u : ℝ × ℝ → Vec, StronglyMeasurable u → UnforcedLeray.Cyl.IsPeriodic c u →
    (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) < ∞ →
    Tendsto (fun θ : ℝ => ∫⁻ z in strip c, ‖planeHeat θ u z - u z‖ₑ ^ 2) (𝓝 0) (𝓝 0)

/-- For `θ > 0`, `planeHeat` (Gaussian average over `Euc 2` through `planeι`, source line 3373) is
the Gaussian convolution `heatVecConvolution` over `Plane = ℝ × ℝ` with `B0284.heatKernel2`
(change of variables by the measure preserving `planeι`, and
`gaussKernel 2 θ y = heatKernel2 θ (planeι y)`). -/
def PlaneHeatEqConv : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ (u : ℝ × ℝ → Vec) (z : ℝ × ℝ),
    planeHeat θ u z = UnforcedLeray.HeatCylinder.heatVecConvolution θ u z

/-- Positive-side strip `L²` continuity of the Gaussian convolution at `0`: the class of `u` in
`Lp Vec 2 (cellMeasure c)` is `x`; `heatVecL2CLM_value_ae` identifies `heatVecL2CLM hc θ x` with the
convolution a.e. on the cell, and the strip `lintegral` is `c` times the cell `lintegral`
(`B0224.lintegral_strip_eq_cell`, `PlaneHeat.lean:85`); conclude with
`HeatCylinder.tendsto_heatVecL2CLM_apply_zero_full`. -/
def VecConvStripCont (c : ℝ) : Prop :=
  ∀ u : ℝ × ℝ → Vec, StronglyMeasurable u → UnforcedLeray.Cyl.IsPeriodic c u →
    (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) < ∞ →
    Tendsto (fun θ : ℝ => ∫⁻ z in strip c,
        ‖UnforcedLeray.HeatCylinder.heatVecConvolution θ u z - u z‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0)

/-- Reduction of the `MeridC = ℂ²`-valued statement to the `Vec = ℝ²`-valued one: split
`u = (Re u, Im u)` by the real-linear coordinate maps `MeridC →L[ℝ] Vec`; `planeHeat` commutes with
them a.e. (the Gaussian-weighted integrand is integrable a.e., `integrable_gauss_smul`), and
`‖v‖² ≤ 2(‖Re v‖² + ‖Im v‖²)`-type comparison closes it. -/
def HeatFiberContReduce (c : ℝ) : Prop := HeatFiberContVec c → HeatFiberCont c

theorem heatFiberContVec_of (c : ℝ) (h1 : PlaneHeatEqConv) (h2 : VecConvStripCont c) :
    HeatFiberContVec c := by
  intro u hm hp hfin
  rw [← nhdsLE_sup_nhdsGT]
  refine Tendsto.sup ?_ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ' : θ ≤ 0 := by simpa using hθ
    simp [planeHeat_of_nonpos hθ']
  · refine (h2 u hm hp hfin).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ' : 0 < θ := by simpa using hθ
    refine lintegral_congr fun z => ?_
    rw [h1 θ hθ' u z]

theorem heatFiberCont_holds_of (c : ℝ) (h1 : PlaneHeatEqConv) (h2 : VecConvStripCont c)
    (h3 : HeatFiberContReduce c) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberCont c :=
  h3 (heatFiberContVec_of c h1 h2)

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
