import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3

/-!
# `kerIntProd` (`PartIII-b:C/rep/2/6/3/3/2`, source 3603-3626, 3800-3807, 4171-4200, 5223)

Fubini on `mHZ = (vol|_{(0,∞)}) ⊗ vol`: the iterated integral defining `kerInt` is the product
integral of `kerF`, when the integrand is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(L2)** Fubini: the iterated integral `kerInt` is `-∫ kerF` over `mHZ` when integrable. -/
theorem kerIntProd : KerIntProd := by
  intro T τ i Φ y hint
  unfold kerInt
  congr 1
  unfold mHZ at hint ⊢
  rw [integral_prod _ hint]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
