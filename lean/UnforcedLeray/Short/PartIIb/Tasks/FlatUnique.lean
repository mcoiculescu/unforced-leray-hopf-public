import UnforcedLeray.Short.PartIIb.Sub.T11
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrthogonality
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate

/-!
# Part II-b, task `PartII-b:T11` (`flat_unique`): assembly

Source of record: `the November 2 reference manuscript`, SP 1921-1938 and 2618.
The conditional glue `flat_unique_of` (`Sub/T11.lean`) takes slice orthogonality (`PartII-b:T11/5`,
`flatSliceOrthogonality`) and separation (`PartII-b:T11/6`, `niceFieldsSeparate`) as hypotheses.
Both are proved unconditionally in their own files, so `flat_unique` is unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Flat uniqueness** (`PartII-b:T11`): a flat response with zero initial datum vanishes a.e. -/
theorem flat_unique {c r ν : ℝ} {μ : ℂ} (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hr3 : r < 3)
    (ha : 0 < μ.re + (3 / r - 1) / 2) (b : CProf) (hb : InFlatClass c r b)
    (h0 : IsFlatResponse ν μ 0 b) : b =ᵐ[hMeas c r] 0 :=
  flat_unique_of flatSliceOrthogonality niceFieldsSeparate hc hν hr hr3 ha b hb h0

end UnforcedLeray.Short.IIb

end

#print axioms UnforcedLeray.Short.IIb.flat_unique
