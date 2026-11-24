import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Space

/-!
# Zero circulation of the real part of `xFn ξ` (source 3176-3184, 4349-4350)

`rePart_zeroCirc_aux`: `Re (xFn ξ)` is integrable on the cell with vanishing integral. The
pointwise even representative of `Re (xFn ξ)` used with `eq:ct-embeddings` (task
`PartIII-b:C/asrc/kflat/1/2/3/1/1/4`) is `rePart_evenRep_zeroCirc` in `RePartEvenRep.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Zero circulation of the real part of `xFn ξ` (source 3176-3184, 4349-4350). -/
theorem rePart_zeroCirc_aux {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    UnforcedLeray.Short.IIIa.HasZeroCirculation c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) := by
  have hre : IntegrableOn (fun x => (xFn ξ x).re) (B0579.cell c) :=
    (xFn_integrableOn ξ).re
  refine ⟨hre.ofReal, ?_⟩
  have h : ∫ x in B0579.cell c, (xFn ξ x).re = (∫ x in B0579.cell c, xFn ξ x).re :=
    integral_re (xFn_integrableOn ξ)
  rw [integral_complex_ofReal, h, xFn_circ]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
