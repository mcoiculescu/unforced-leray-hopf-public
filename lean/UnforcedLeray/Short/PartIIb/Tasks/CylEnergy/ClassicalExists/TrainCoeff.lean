import UnforcedLeray.Short.PartIIb.Sub.T22_1_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.Regular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.Bdd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.DeltaD1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.VcDeriv

/-!
# Part II-b, task `PartII-b:T22/1/1`: `TrainCoeffBdd`

Source: `the November 2 reference manuscript` lines 2085-2093.  The four leaves
`tcRegular`, `tcBdd`, `tcDeltaD1`, `tcVcDeriv` feed the decomposition `trainCoeffBdd_of`
(`Sub/T22_1_1.lean`).
-/

set_option autoImplicit false

noncomputable section

theorem trainCoeffBdd : UnforcedLeray.Short.IIb.CylPDE.TrainCoeffBdd :=
  UnforcedLeray.Short.IIb.CylPDE.trainCoeffBdd_of
    UnforcedLeray.Short.IIb.CylPDE.tcRegular
    UnforcedLeray.Short.IIb.CylPDE.tcBdd
    UnforcedLeray.Short.IIb.CylPDE.tcDeltaD1
    UnforcedLeray.Short.IIb.CylPDE.tcVcDeriv
