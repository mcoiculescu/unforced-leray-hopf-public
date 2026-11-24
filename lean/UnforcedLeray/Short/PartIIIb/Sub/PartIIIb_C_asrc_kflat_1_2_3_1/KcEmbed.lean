import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.EvenRepAssembly
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.BSScale
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.VelNormScale
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.RealBridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.JscaleInvPres
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.MemLpNormCmp

/-!


Source of record: `the November 2 reference manuscript`, lines 3176-3184 and
3228-3240 (`eq:ct-embeddings`).

Assembles `tfkKcEmbed_of` (EvenRepAssembly.lean) from the five dilation/bridge facts, each proved
in its own sibling module of this folder.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- **`tfkKcEmbed`** (source 3176-3184, 3228-3240): the embedding `TFKKcEmbed m` for every
`m > 1`, from the sibling facts. -/
theorem tfkKcEmbed (m : ℝ) [Fact (1 < m)] : TFKKcEmbed m :=
  tfkKcEmbed_of m
    (fun c a hc ha f u h => isBiotSavart_jscaleInv c a hc ha f u h)
    (fun c a hc ha u => UnforcedLeray.Short.IIIa.velNorm_scale c a hc ha u)
    (fun ξ u h => kcLp_norm_le_velNorm ξ u h)
    (fun c a hc ha g he hz => jscaleInv_even_zeroCirc c a hc ha g he hz)
    (fun a ha ξ => jscaleInv_rePart_memLp_le a ha ξ)

end UnforcedLeray.Short.PartIIIb.Concrete
