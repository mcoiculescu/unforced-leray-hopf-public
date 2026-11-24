import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!
# Leaf `PartIII-b:C/env/3`: the generic affine envelope `M(A) ≤ C e^{1.1a_s/ν} ‖A‖_𝒜`

Source of record: `the November 2 reference manuscript` (73 pages), lines
5089-5091 (`For generic A ∈ 𝒜, M(A) ≤ C e^{1.1a_s/ν}‖A‖_𝒜`), feeding `PLBound`
(lines 5883-5890).

Proof: the one line `affMEnvelope_of_cutoff sDerivIterDiffOn sDerivIterLeibniz hχ`, using the
two leaves `C/env/1` (`sDerivIterDiffOn`) and `C/env/2` (`sDerivIterLeibniz`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf `PartIII-b:C/env/3`: for the source cutoff profile `χ̂_f`, `M(A) ≤ C e^{1.1a_s/ν}‖A‖_𝒜`
(source 5089-5091). -/
theorem affMEnvelope (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) : AffMEnvelope χ :=
  affMEnvelope_of_cutoff sDerivIterDiffOn sDerivIterLeibniz hχ

end UnforcedLeray.Short.PartIIIb.Concrete
