import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.CohJetsExists
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.MeasPathVersion
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.MeasPlaneVersion
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.StLocL2Of
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.StTimeIdentity
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.StSpaceIdentity

/-!
# `PartIII-a:T21/2/7/2/1/1/7`: `TimeJetsSTSobolev` from the proved leaves

Assembles `timeJetsSTSobolev_of` (`Sub/AdjInterior/STSobolev/Assembly.lean`) with the leaf
theorems of the folder `Tasks/AdjSmooth/Interior/STSobolev/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem timeJetsSTSobolev : TimeJetsSTSobolev :=
  timeJetsSTSobolev_of cohJetsExists measPathVersion measPlaneVersion stLocL2Of stTimeIdentity
    stSpaceIdentity

end UnforcedLeray.Short.IIIa
