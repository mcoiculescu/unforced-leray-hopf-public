import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor.GaussSplit.Moments
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor.GaussSplit.IterExpand

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/2`: `HeatGaussSplit` (assembly)

Source `the November 2 reference manuscript`, lines 261-288. The Gaussian average
of the second-order Taylor expansion, with moments `1, 0, 2h δ_ij`, is `HeatGaussSplit`.
Assembled from the two leaves `heatGaussSplit_moments` (`HGMoments`) and
`heatGaussSplit_iterExpand` (`HGIterExpand`) via `heatGaussSplit_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatGaussSplit` (lines 261-288).** Assembly from the Gaussian moments and the
coordinate expansion of `iterD`. -/
theorem heatGaussSplit : HeatGaussSplit :=
  heatGaussSplit_of heatGaussSplit_moments heatGaussSplit_iterExpand

end UnforcedLeray.Short.PartI
