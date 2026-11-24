import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_closure
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_normlaws
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_complete
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff

/-!
# `PartIII-b:C/ret/1`: the Banach space `𝒜` (source lines 4733-4752)

`AffSp as` is the subtype `{A : ℝ → Mat3 // IsAffElem as A}`, with norm `affNorm as`.
The lemmas `affClosure`, `affNormLaws`, `affCompleteness` (true for every `as`, no
positivity needed for these signatures) supply the structure through `affNAG`, `affNS`
and `affSub_complete`. The Banach instances are installed as `instance`s and the norm
identity is recorded as `AffSp.norm_def`.
-/

set_option autoImplicit false

noncomputable section

open Set Real Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Banach space `𝒜` of affine-type elements, as a subtype. -/
abbrev AffSp (as : ℝ) := {A : ℝ → Mat3 // IsAffElem as A}

/-- Normed group structure on `AffSp as`, with norm `affNorm as`. -/
instance affSpNAG (as : ℝ) : NormedAddCommGroup (AffSp as) :=
  affNAG as (affClosure as) (affNormLaws as (affClosure as))

/-- Normed space structure on `AffSp as` over `ℝ`. -/
instance affSpNS (as : ℝ) : NormedSpace ℝ (AffSp as) :=
  affNS as (affClosure as) (affNormLaws as (affClosure as))

/-- `AffSp as` is complete for the norm `affNorm as`. -/
instance affSpComplete (as : ℝ) : @CompleteSpace (AffSp as) (affSpNAG as).toUniformSpace :=
  affSub_complete as (affClosure as) (affNormLaws as (affClosure as))
    (affCompleteness as (affClosure as) (affNormLaws as (affClosure as)))

/-- The norm on `AffSp as` is `affNorm as` (source 4750). -/
theorem AffSp.norm_def (as : ℝ) (A : AffSp as) : ‖A‖ = affNorm as A.1 :=
  affNAG_norm as (affClosure as) (affNormLaws as (affClosure as)) A

end UnforcedLeray.Short.PartIIIb.Concrete
