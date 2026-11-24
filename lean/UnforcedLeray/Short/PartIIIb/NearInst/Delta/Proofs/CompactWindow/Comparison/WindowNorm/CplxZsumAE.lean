import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_4

/-!
# The transported summed input (item `PartIII-b:C/near/delta/8/2/4/3`)

Source of record `the November 2 reference manuscript` 1641-1646.
The transport `cplxT` of `zsumL X` is `tv4 ∘ zsum X ∘ cellPt` almost everywhere: `cplxT_ae`
gives the pointwise formula `tv4 ∘ (zsumL X) ∘ cellPt`, `zsumL_ae` identifies `zsumL X` with `zsum X`
almost everywhere for `ageμ c (-1/2)`, and the image of `measureHT` under `cellPt` is
`c • ageμ c (-1/2)` (`CellPtHT`), which transfers the a.e. identity back along `cellPt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

theorem cplxZsumAE_proof : CplxZsumAE := by
  intro c mZ ρb hT hmZ hρ X
  have hmap : Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
      ENNReal.ofReal c • ageμ c (-1 / 2) := hT
  have h1 : ∀ᵐ x ∂(Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c)),
      ((Masked.zsumL c mZ ρb hmZ hρ X : HTsp c) : Chart → Ten3) x = zsum X x := by
    rw [hmap]
    exact Measure.ae_smul_measure (Masked.zsumL_ae c mZ ρb hmZ hρ X) _
  have h2 : ∀ᵐ p ∂(UnforcedLeray.Short.PartIIa.measureHT c),
      ((Masked.zsumL c mZ ρb hmZ hρ X : HTsp c) : Chart → Ten3) (cellPt c p) =
        zsum X (cellPt c p) :=
    ae_of_ae_map (Masked.measurable_cellPt c).aemeasurable h1
  filter_upwards [Masked.cplxT_ae c hT (Masked.zsumL c mZ ρb hmZ hρ X), h2] with p hp1 hp2
  rw [hp1, hp2]

theorem cplxZsumAE : CplxZsumAE := cplxZsumAE_proof

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
