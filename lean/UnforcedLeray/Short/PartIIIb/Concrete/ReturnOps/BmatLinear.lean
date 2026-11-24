import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `C/ret/6`: linearity of `B = (A^y)' + μ A^y / s` in `A`

Source 4957-4958 (`B = (A^y)' + μ A^y/s`) and 4985 (all maps depend linearly on `A`).
Only the pointwise linearity at `s` is claimed, under differentiability of `A^y` at `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bmatLinear : BmatLinear := by
  intro ν μ χ A A' r s hA hA'
  constructor
  · have hval : Ay ν χ (A + A') s = Ay ν χ A s + Ay ν χ A' s := by
      simp only [Ay, Pi.add_apply, smul_add]
    have hfun : Ay ν χ (A + A') = Ay ν χ A + Ay ν χ A' := by
      funext t
      simp only [Ay, Pi.add_apply, smul_add]
    unfold Bmat
    rw [hval, hfun, deriv_add hA hA']
    module
  · have hval : Ay ν χ (r • A) s = r • Ay ν χ A s := by
      simp only [Ay, Pi.smul_apply]
      exact smul_comm _ _ _
    have hfun : Ay ν χ (r • A) = r • Ay ν χ A := by
      funext t
      simp only [Ay, Pi.smul_apply]
      exact smul_comm _ _ _
    unfold Bmat
    rw [hval, hfun, deriv_const_smul r hA]
    module

end UnforcedLeray.Short.PartIIIb.Concrete
