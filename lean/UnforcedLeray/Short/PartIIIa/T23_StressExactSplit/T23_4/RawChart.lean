import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.TrainVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.RaisedStream

/-!
# Part III-a, task `PartIII-a:T23/4/2`: transverse tail of the raw chart coefficient

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`) and 463-467 (`sct:transverse`); the raw chart coefficient is the
profile of the lift of the train stream, `v_raw = v + εH e_z` (SP 1205-1216, 2042-2043, 5461).

Proves `rawChartTail_of_uniform`: the raw chart tail `RawChartTail` follows from the uniform
Part I tails `TrainTransverseTailsUniform` and the absorption `TailAbsorb`, by combining
`trainVelTransverseTail_of` (task `PartIII-a:T23/4/1`) and `raisedStreamTransverseTail_of`
(task `PartIII-a:T23/4/3`) through `rawChartTail_of` (proved in `T23_4_Leaves.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

theorem rawChartTail_of_uniform (hT : UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform)
    (hK : UnforcedLeray.Short.IIIa.TailAbsorb) : UnforcedLeray.Short.IIIa.RawChartTail :=
  rawChartTail_of (trainVelTransverseTail_of hT hK) (raisedStreamTransverseTail_of hT hK)

end UnforcedLeray.Short.IIIa
