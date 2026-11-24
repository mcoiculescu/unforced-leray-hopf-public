import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub

/-!
# Bilinear expansion of `cB0` (`PartIII-b:C/asrc/ra/9/2/2/9`)

Pure algebra: `cB0` is built from `fderiv`, `cDiv` (a linear functional of `fderiv`) and scalar
multiples, so with `F' = F + ε E` and `G' = G + ε K` the expansion is bilinear in `ε`.
Source of record: `the November 2 reference manuscript`, lines 5034-5044.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem convB0Expand : ConvB0Expand := by
  unfold ConvB0Expand
  intro F E G K ε s x hF hE hG hK
  have dF : fderiv ℝ (fun y => F s y + ε • E s y) x =
      fderiv ℝ (F s) x + ε • fderiv ℝ (E s) x :=
    ((hF.hasFDerivAt).add ((hE.hasFDerivAt).const_smul ε)).fderiv
  have dG : fderiv ℝ (fun y => G s y + ε • K s y) x =
      fderiv ℝ (G s) x + ε • fderiv ℝ (K s) x :=
    ((hG.hasFDerivAt).add ((hK.hasFDerivAt).const_smul ε)).fderiv
  unfold cB0 cAdv cDiv
  simp only [dF, dG, add_apply, smul_apply, map_add, map_smul,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    add_apply, smul_apply, map_add, map_smul] <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
