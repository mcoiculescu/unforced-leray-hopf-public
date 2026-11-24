import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T5
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T12

/-!
# `hpWordPointwise` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1`)

Source `the November 2 reference manuscript`
lines 5063-5071, 5076-5079, 4963-4985. Assembly of `hpWordPointwise_of` (in `Defs.lean`) from
the lattice decomposition (T1), the summand smoothness (T5), the summand word bound (T12), the
envelope summability (T2), the locally uniform envelope majorant (T3) and termwise conormal
differentiation (T4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem hpWordPointwise (as : ℝ) (χf : ℝ → ℝ) : HpWordPointwise as χf :=
  hpWordPointwise_of as χf hpSumDecomp (hpSummandSmooth as χf) (hpSummandBound as χf)
    envSummable envLocSumm termwiseWord

end UnforcedLeray.Short.PartIIIb.Concrete
