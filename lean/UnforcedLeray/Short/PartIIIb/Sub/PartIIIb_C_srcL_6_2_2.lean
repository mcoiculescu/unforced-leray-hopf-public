import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1

/-!
# `PartIII-b:C/srcL/6/2/2`: smoothness of the zero-width Young field on the outward region

Source of record: `the November 2 reference manuscript` lines 4776-4782.
`youngW c ν ε μ χo M = ε² • newtonV c ν μ χo M (ε • ·)`, and `ε • y` lies in the region
`{5ν/6 < x₀² + x₁²}` exactly when `y ∈ outReg ν ε`.  So `XSYoungWSmooth` follows from the
smoothness of `newtonV` on that region (`newtonVSmooth`), by composition with the dilation and
multiplication by the constant `ε²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsYoungWSmooth : XSYoungWSmooth := by
  intro c ν ε μ χo M hc hν hε hμ hχ hM
  have hsq : ∀ y : Vec3, cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  have hmaps : MapsTo (fun y : Vec3 => ε • y) (outReg ν ε)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    intro y hy
    have hy' : 5 * ν / (6 * ε ^ 2) < y 0 ^ 2 + y 1 ^ 2 := by
      have := hy; simp only [outReg, mem_setOf_eq] at this; rwa [hsq] at this
    have h2 : 0 < 6 * ε ^ 2 := by positivity
    have := (div_lt_iff₀ h2).1 hy'
    show 5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  have h := (newtonVSmooth c ν μ χo M hc hν hμ hχ hM).comp
    ((contDiff_const_smul ε).contDiffOn (s := outReg ν ε)) hmaps
  exact (h.const_smul (ε ^ 2)).congr fun y _ => rfl

end UnforcedLeray.Short.PartIIIb.Concrete
