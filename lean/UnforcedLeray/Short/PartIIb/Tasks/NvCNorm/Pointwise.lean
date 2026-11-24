import UnforcedLeray.Short.PartIIb.Sub.T07
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.NormSq
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.MeridNormSq

/-!


Source of record: `the November 2 reference manuscript`, lines 1902-1906
(the complex lift `N_v b = N_v(Re b) + i N_v(Im b)` and its norm identity).

Proves `NvCPointwise`: off the axis, for `q ≥ 0`,
`‖N_v b(τ, y)‖ₑ ^ q = age^{q/2} ‖b(chart R τ y)‖ₑ ^ q`.

Proof sketch: write `A = Nv R (Re ∘ b) τ y` and `B = Nv R (Im ∘ b) τ y`, so
`NvC R b (τ, y) = realC A + I • realC B`. By `nvCNormSq` the squared norm is `‖A‖² + ‖B‖²`;
by `Axi.norm_Nv` both `‖A‖` and `‖B‖` are `√age` times the meridional norms of `b(chart)`; by
`cMeridNormSq` the meridional norms add up to `‖b(chart)‖²`. Hence `‖NvC‖ = √age ‖b(chart)‖`
(both sides nonnegative), and the ENNReal identity follows as in `Axi.enorm_Nv_rpow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- SP 1902-1906, step 3: the pointwise identity for the complex ring lift, off the axis. -/
theorem nvCPointwise : UnforcedLeray.Short.IIb.NvCPointwise := by
  unfold NvCPointwise
  intro R b τ y hy q hq
  have hNSq : NvCNormSq := nvCNormSq
  have hMSq : CMeridNormSq := cMeridNormSq
  have hage : 0 ≤ Axi.age R y := Axi.age_nonneg R y
  have hN : NvC R b (τ, y) =
      UnforcedLeray.B0412.realC (Axi.Nv R (fun z => reM (b z)) τ y) +
        Complex.I • UnforcedLeray.B0412.realC (Axi.Nv R (fun z => imM (b z)) τ y) := rfl
  have hA : ‖Axi.Nv R (fun z => reM (b z)) τ y‖ =
      Real.sqrt (Axi.age R y) * ‖reM (b (Axi.chart R τ y))‖ :=
    Axi.norm_Nv R (fun z => reM (b z)) τ hy
  have hB : ‖Axi.Nv R (fun z => imM (b z)) τ y‖ =
      Real.sqrt (Axi.age R y) * ‖imM (b (Axi.chart R τ y))‖ :=
    Axi.norm_Nv R (fun z => imM (b z)) τ hy
  have hM : ‖b (Axi.chart R τ y)‖ ^ 2 =
      ‖reM (b (Axi.chart R τ y))‖ ^ 2 + ‖imM (b (Axi.chart R τ y))‖ ^ 2 :=
    hMSq (b (Axi.chart R τ y))
  have hsq2 : ‖NvC R b (τ, y)‖ ^ 2 =
      ‖Axi.Nv R (fun z => reM (b z)) τ y‖ ^ 2 + ‖Axi.Nv R (fun z => imM (b z)) τ y‖ ^ 2 := by
    rw [hN]
    exact hNSq _ _
  have key : ‖NvC R b (τ, y)‖ ^ 2 = (Real.sqrt (Axi.age R y) * ‖b (Axi.chart R τ y)‖) ^ 2 := by
    rw [hA, hB] at hsq2
    linear_combination hsq2 - Real.sqrt (Axi.age R y) ^ 2 * hM
  have hnorm : ‖NvC R b (τ, y)‖ = Real.sqrt (Axi.age R y) * ‖b (Axi.chart R τ y)‖ :=
    (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      two_ne_zero).1 key
  rw [← ofReal_norm, hnorm, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hq,
    Axi.sqrt_rpow hage q, ofReal_norm]

end UnforcedLeray.Short.IIb
