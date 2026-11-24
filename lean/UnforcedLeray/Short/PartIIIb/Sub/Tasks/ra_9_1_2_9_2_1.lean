import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T5
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T6
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T2

/-!
# `psiWordPointwise` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1`)

Source `the November 2 reference manuscript`
lines 5063-5071, 5076-5079, 4979. Assembly of `psiWordPointwise_of` (in `Defs.lean`) from
the summand smoothness (T5), the summand word bound (T6), the envelope summability (`envSummable`,
from the Hp chain `ra_9_1_2_9_1_1/T2.lean`), the locally uniform envelope majorant (T2) and termwise
conormal differentiation (T1).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem psiWordPointwise (as : ℝ) (χf : ℝ → ℝ) : PsiWordPointwise as χf :=
  psiWordPointwise_of as χf (psiSummandSmooth as χf) (psiSummandBound as χf)
    envSummable psiEnvLocSumm psiTermwiseWord

end UnforcedLeray.Short.PartIIIb.Concrete
