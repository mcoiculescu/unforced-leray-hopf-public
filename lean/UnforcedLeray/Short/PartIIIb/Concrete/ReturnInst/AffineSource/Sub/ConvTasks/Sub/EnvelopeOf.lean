import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.TrainBand
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.HpPsiEnv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ProfileEqs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DiffParts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.CB0Bound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.CB1Bound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.ZPairBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.CKAdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.CKCongr
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.ToMerNorm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.LatticeAbsorb
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Env.ConvSDiff

/-!
# `convGEnvelope` from the two Part I train statements (`PartIII-b:C/asrc/ra/9/2/2/13`)

Source: `the November 2 reference manuscript` 5034-5044. Every input of
`convGEnvelope_of` is an unconditional theorem except `TrainBand`, which needs
`TrainTransverseTails` (460-467) and `TrainFixedBand` (468-478) of Part I (tasks PartI:T24, PartI:T25).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem convGEnvelope_of_partI (as : ℝ) (χf : ℝ → ℝ)
    (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : ConvGEnvelope as χf :=
  convGEnvelope_of as χf (trainBand_of_partI hT hF) (hpPsiEnv as) (convProfileEqs as χf)
    (convDiffParts as χf) (convSDiff as χf) cb0Bound cb1Bound zPairBound ckAdd ckCongr
    toMerNorm latticeAbsorb

end UnforcedLeray.Short.PartIIIb.Concrete

end
