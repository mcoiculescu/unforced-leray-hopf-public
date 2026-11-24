import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Of
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.PerEContinuous
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.PerLam0Continuous
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.QFunPtCont
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.Lam0KerPtCont
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.QFunGaussBound
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.GaussStripMemLp
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.Lam0KerBdd
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.QFunCirc
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.IntegralCellDilate
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.ContinuousToLpOfDominated
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.SeedKernelEven
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.SeedKernelMeanZero
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.SeedDualConj
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Proofs.PerLamConj

/-!


Source of record `the November 2 reference manuscript` (2894-2912, 4352-4356,
3030-3035, 593-610). The proof is the compiled reduction `Pair.frozenPairExists_of` applied to the
fourteen leaf proofs of `Pair/Proofs/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem frozenPairExists : FrozenPairExists :=
  Pair.frozenPairExists_of Pair.perEContinuous Pair.perLam0Continuous Pair.qFunPtCont
    Pair.lam0KerPtCont Pair.qFunGaussBound Pair.gaussStripMemLp Pair.lam0KerBdd
    Pair.qFunCirc Pair.integralCellDilate Pair.continuousToLpOfDominated
    Pair.seedKernelEven Pair.seedKernelMeanZero Pair.seedDualConj Pair.perLamConj

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
