import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatAPeriodic

/-!
# `perExt` is the identity on `hAcoef` (`PartIII-b:C/asrc/ra/9/2/2/2`, source 4963-4975)

`perExt c b (s, x) = b (s, (cellRep c x.1, x.2))`.  With `c = cOf ν`, `cellRep c ξ = ξ + n c`
for the integer `n = -⌊(ξ + c/2)/c⌋`, and `ĥ_A` is invariant under `q ↦ q + n c`
(`hhatAPeriodic_proof`), so `hAcoef` is too.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `cellRep` is a lattice translation: `cellRep c ξ = ξ + n c` with `n ∈ ℤ`. -/
theorem cellRep_eq_add_int_mul (c ξ : ℝ) :
    cellRep c ξ = ξ + ((-⌊(ξ + c / 2) / c⌋ : ℤ) : ℝ) * c := by
  unfold cellRep
  push_cast
  ring

/-- `hAcoef` is `cOf ν`-periodic in its `q`-variable. -/
theorem hAcoef_cellRep_eq (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hAcoef ν ε χf A (s, (cellRep (cOf ν) x.1, x.2)) = hAcoef ν ε χf A (s, x) := by
  unfold hAcoef
  rw [cellRep_eq_add_int_mul]
  have h := hhatAPeriodic_proof ν ε χf A s x (-⌊(x.1 + cOf ν / 2) / cOf ν⌋)
  simp only at h ⊢
  rw [h]

theorem convPerExtHat (as : ℝ) (χf : ℝ → ℝ) : ConvPerExtHat as χf := by
  intro _ ν ε _ _ A _ s _ x
  unfold perExt
  exact hAcoef_cellRep_eq ν ε χf A s x

end UnforcedLeray.Short.PartIIIb.Concrete
